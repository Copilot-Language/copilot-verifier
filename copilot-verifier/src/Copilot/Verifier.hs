{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

module Copilot.Verifier where

import Control.Lens (view, (^.))
import Control.Monad (foldM)
import qualified Data.Map.Strict as Map
import Data.IORef (newIORef, modifyIORef, IORef)

import Copilot.Compile.C99 (CSettings(..), compileWith)
import Copilot.Core

-- import qualified Copilot.Theorem.What4 as CW4

import Data.Parameterized.Nonce (globalNonceGenerator)
import Data.Parameterized.Some (Some(..))

import Lang.Crucible.Backend
  ( IsSymInterface, Goals(..), Assumptions, Assertion
  , pushAssumptionFrame, popUntilAssumptionFrame
  , getProofObligations
  )
import Lang.Crucible.Backend.Simple (newSimpleBackend)
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import Lang.Crucible.Simulator (SimContext(..), ctxSymInterface)

import Lang.Crucible.LLVM.Extension (LLVM)
import Lang.Crucible.LLVM.Globals (initializeAllMemory, populateAllGlobals)
import Lang.Crucible.LLVM.MemModel
  (mkMemVar, withPtrWidth, HasLLVMAnn, MemImpl, LLVMAnnMap
  )
import Lang.Crucible.LLVM.Translation
  ( translateModule, ModuleTranslation, globalInitMap
  , transContext, cfgMap
  , llvmPtrWidth, llvmTypeCtx
  )

import Crux (defaultOutputConfig)
import Crux.Config (cfgJoin, Config(..))
import Crux.Config.Load (fromFile, fromEnv)
import Crux.Config.Common (cruxOptions, CruxOptions(..), postprocessOptions, )
import Crux.Goal (proveGoalsOffline)
import Crux.Log
  ( cruxLogMessageToSayWhat, withCruxLogMessage, outputHandle
  , Logs, SupportsCruxLogMessage
  )
import Crux.Types (SimCtxt, Crux, ProcessedGoals(..), ProofResult(..))

import Crux.LLVM.Config (llvmCruxConfig, LLVMOptions(..))
import Crux.LLVM.Compile (genBitCode)
import Crux.LLVM.Simulate (setupSimCtxt, parseLLVM, explainFailure)
import CruxLLVMMain
  (withCruxLLVMLogging, cruxLLVMLoggingToSayWhat, processLLVMOptions)

import What4.Expr.Builder (FloatModeRepr(..), ExprBuilder)
import What4.ProgramLoc (ProgramLoc)
import What4.Solver.Z3 (z3Adapter)

verify :: CSettings -> String -> Spec -> IO ()
verify csettings prefix spec =
  do compileWith csettings prefix spec
     putStrLn ("Generated " ++ prefix)

     let csrc = prefix ++ ".c"

     llvmcfg <- llvmCruxConfig
     let cfg = cfgJoin cruxOptions llvmcfg

     (cruxOpts, llvmOpts) <-
       do -- TODO, load from and actual configuration file
          fileOpts <- fromFile "copilot-verifier" cfg Nothing
          (cruxOpts0, llvmOpts0) <- foldM fromEnv fileOpts (cfgEnv cfg)
          let ?outputConfig = defaultOutputConfig cruxLogMessageToSayWhat (Just cruxOpts0)
          cruxOpts1 <- withCruxLogMessage (postprocessOptions cruxOpts0{ inputFiles = [csrc] })
          processLLVMOptions (cruxOpts1, llvmOpts0)


     let ?outputConfig = defaultOutputConfig cruxLLVMLoggingToSayWhat (Just cruxOpts)
     bcFile <- withCruxLLVMLogging (genBitCode cruxOpts llvmOpts)

     putStrLn ("Compiled " ++ prefix ++ " into " ++ bcFile)

     verifyBitcode csettings spec cruxOpts llvmOpts bcFile

verifyBitcode ::
  CSettings ->
  Spec ->
  CruxOptions ->
  LLVMOptions ->
  FilePath ->
  IO ()
verifyBitcode csettings spec cruxOpts llvmOpts bcFile =
  do halloc <- newHandleAllocator
     sym <- newSimpleBackend FloatUninterpretedRepr globalNonceGenerator
     bbMapRef <- newIORef mempty
     let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
     let ?outputConfig = defaultOutputConfig cruxLLVMLoggingToSayWhat (Just cruxOpts)

     memVar <- mkMemVar "llvm_memory" halloc

     let simctx = (setupSimCtxt halloc sym (memOpts llvmOpts) memVar)
                  { printHandle = view outputHandle ?outputConfig }

     llvmMod <- parseLLVM bcFile
     Some trans <- let ?transOpts = transOpts llvmOpts
                    in translateModule halloc memVar llvmMod

     putStrLn ("Translated bitcode into Crucible")

     let llvmCtxt = trans ^. transContext
     let ?lc = llvmCtxt ^. llvmTypeCtx
     let ?memOpts = memOpts llvmOpts
     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withCruxLLVMLogging $
       do emptyMem   <- initializeAllMemory sym llvmCtxt llvmMod
          initialMem <- populateAllGlobals sym (globalInitMap trans) emptyMem

          verifyInitialState cruxOpts spec bbMapRef simctx initialMem
          verifyStepBisimulation cruxOpts csettings spec bbMapRef simctx emptyMem

verifyInitialState ::
  IsSymInterface sym =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  sym ~ ExprBuilder t st fs =>
  CruxOptions ->
  Spec ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  MemImpl sym ->
  IO ()
verifyInitialState cruxOpts spec bbMapRef simctx mem =
  do let sym = simctx^.ctxSymInterface
     putStrLn "Computing initial state verification conditions"
     frm <- pushAssumptionFrame sym

     -- Do the actual computation here

     popUntilAssumptionFrame sym frm

     putStrLn "Proving initial state verification conditions"
     proveObls cruxOpts bbMapRef simctx

verifyStepBisimulation ::
  IsSymInterface sym =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  sym ~ ExprBuilder t st fs =>
  CruxOptions ->
  CSettings ->
  Spec ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  MemImpl sym ->
  IO ()
verifyStepBisimulation cruxOpts csettings spec bbMapRef simctx mem =
  do let sym = simctx^.ctxSymInterface
     putStrLn "Computing step bisimulation verification conditions"

     frm <- pushAssumptionFrame sym

     -- Do the actual computation here

     popUntilAssumptionFrame sym frm

     putStrLn "Proving step bisimulation verification conditions"
     proveObls cruxOpts bbMapRef simctx

proveObls ::
  IsSymInterface sym =>
  sym ~ ExprBuilder t st fs =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  IO ()
proveObls cruxOpts bbMapRef simctx =
  do let sym = simctx^.ctxSymInterface
     obls <- getProofObligations sym

     let adapters = [z3Adapter] -- TODO? configurable
     results <- proveGoalsOffline adapters cruxOpts simctx (explainFailure sym bbMapRef) obls
     presentResults sym results

presentResults ::
  IsSymInterface sym =>
  sym ->
  (ProcessedGoals, Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym))) ->
  IO ()
presentResults sym (num, goals) =
  do return () -- TODO
