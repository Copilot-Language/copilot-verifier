{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Copilot.Verifier where

import Control.Lens (view, (^.), to)
import Control.Monad (foldM, forM_)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (execStateT, lift, StateT(..))
import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import Data.IORef (newIORef, modifyIORef, IORef)
import qualified Text.LLVM.AST as L
import Data.List (genericLength)
import qualified Data.BitVector.Sized as BV
import System.Exit (exitFailure)
import System.FilePath ((</>))

import Copilot.Compile.C99 (CSettings(..), compileWith)
import Copilot.Core
import qualified Copilot.Core.Type as CT

import qualified Copilot.Theorem.What4 as CW4

import Data.Parameterized.Ctx (EmptyCtx)
import Data.Parameterized.Context (pattern Empty)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr (intValue, natValue, testEquality, knownNat, type (<=) )
import Data.Parameterized.Nonce (globalNonceGenerator)
import Data.Parameterized.Some (Some(..))
import Data.Parameterized.TraversableFC (toListFC)

import Lang.Crucible.Backend
  ( IsSymInterface, Goals(..), Assumptions, Assertion
  , pushAssumptionFrame, popUntilAssumptionFrame
  , getProofObligations, clearProofObligations
  , LabeledPred(..), addDurableProofObligation
  , addAssumption, CrucibleAssumption(..)
  )
import Lang.Crucible.Backend.Simple (newSimpleBackend)
import Lang.Crucible.CFG.Core (AnyCFG(..), cfgArgTypes, cfgReturnType)
import Lang.Crucible.CFG.Common ( freshGlobalVar )
import Lang.Crucible.FunctionHandle (newHandleAllocator)
import Lang.Crucible.Simulator
  ( SimContext(..), ctxSymInterface, ExecResult(..), ExecState(..)
  , defaultAbortHandler, runOverrideSim, partialValue, gpValue
  , GlobalVar, executeCrucible, OverrideSim, regValue
  , readGlobal, writeGlobal, callCFG, emptyRegMap, RegEntry(..)
  )
import Lang.Crucible.Simulator.GlobalState ( insertGlobal )
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Simulator.SimError (SimError(..), SimErrorReason(..))
import Lang.Crucible.Types
  ( TypeRepr(..), (:~:)(..), KnownRepr(..), BoolType )

import Lang.Crucible.LLVM (llvmGlobals, registerModuleFn, register_llvm_overrides)
import Lang.Crucible.LLVM.Bytes (bitsToBytes)
import Lang.Crucible.LLVM.DataLayout (DataLayout)
import Lang.Crucible.LLVM.Extension (LLVM, ArchWidth)
import Lang.Crucible.LLVM.Globals (initializeAllMemory, populateAllGlobals)
import Lang.Crucible.LLVM.Intrinsics
  ( IntrinsicsOptions, OverrideTemplate, basic_llvm_override, LLVMOverride(..) )

import Lang.Crucible.LLVM.MemType
  ( MemType(..)
  , i1, i8, i16, i32, i64
  , memTypeSize, memTypeAlign
  , mkStructInfo
  )
import Lang.Crucible.LLVM.MemModel
  ( mkMemVar, withPtrWidth, HasLLVMAnn, MemImpl, LLVMAnnMap
  , HasPtrWidth, doResolveGlobal, doLoad, doStore
  , MemOptions, StorageType, bitvectorType
  , ptrAdd, toStorableType, projectLLVM_bv
  , pattern LLVMPointerRepr, llvmPointer_bv
  , memRepr, Mem
  )
import Lang.Crucible.LLVM.Translation
  ( ModuleTranslation(..), translateModule, globalInitMap
  , transContext, llvmPtrWidth, llvmTypeCtx, llvmTypeAsRepr
  )
import Lang.Crucible.LLVM.TypeContext (TypeContext, llvmDataLayout)

import Crux (defaultOutputConfig)
import Crux.Config (cfgJoin, Config(..))
import Crux.Config.Load (fromFile, fromEnv)
import Crux.Config.Common (cruxOptions, CruxOptions(..), postprocessOptions, )
import Crux.Goal (proveGoalsOffline, provedGoalsTree)
import Crux.Log
  ( cruxLogMessageToSayWhat, withCruxLogMessage, outputHandle
  , Logs, SupportsCruxLogMessage, logGoal
  )
import Crux.Types (SimCtxt, Crux, ProcessedGoals(..), ProofResult(..))

import Crux.LLVM.Config (llvmCruxConfig, LLVMOptions(..))
import Crux.LLVM.Compile (genBitCode)
import Crux.LLVM.Simulate (setupSimCtxt, parseLLVM, explainFailure)
import CruxLLVMMain
  (withCruxLLVMLogging, cruxLLVMLoggingToSayWhat, processLLVMOptions)

import What4.Config
  (extendConfig)
import What4.Interface
  ( Pred, bvLit, bvAdd, bvUrem, bvMul, bvIsNonzero, bvEq, isEq
  , getConfiguration, freshBoundedBV, predToBV
  , getCurrentProgramLoc, printSymExpr
  , truePred, falsePred, eqPred
  )
import What4.Expr.Builder (FloatModeRepr(..), ExprBuilder, BoolExpr, startCaching)
import What4.ProgramLoc (ProgramLoc, mkProgramLoc, Position(..))
import What4.Solver.Adapter (SolverAdapter(..))
import What4.Solver.Z3 (z3Adapter)
import What4.Symbol (safeSymbol)

setOutput :: CruxOptions -> CSettings -> CSettings
setOutput cruxOpts cin =
  case cSettingsOutputDirectory cin of
    Nothing -> cin{ cSettingsOutputDirectory = Just (outDir cruxOpts)  }
    Just _  -> cin

verify :: CSettings -> [String] -> String -> Spec -> IO ()
verify csettings0 properties prefix spec =
  do (cruxOpts, llvmOpts, csettings, csrc) <-
       do llvmcfg <- llvmCruxConfig
          let cfg = cfgJoin cruxOptions llvmcfg
          -- TODO, load from and actual configuration file?
          fileOpts <- fromFile "copilot-verifier" cfg Nothing
          (cruxOpts0, llvmOpts0) <- foldM fromEnv fileOpts (cfgEnv cfg)
          let odir = case cSettingsOutputDirectory csettings0 of
                       Just d -> d
                       Nothing -> "results" </> prefix
          let csettings = csettings0{ cSettingsOutputDirectory = Just odir }
          let csrc = odir </> prefix ++ ".c"
          let cruxOpts1 = cruxOpts0{ outDir = odir, bldDir = odir, inputFiles = [csrc] }
          let ?outputConfig = defaultOutputConfig cruxLogMessageToSayWhat (Just cruxOpts1)
          cruxOpts2 <- withCruxLogMessage (postprocessOptions cruxOpts1)
          (cruxOpts3, llvmOpts2) <- processLLVMOptions (cruxOpts2, llvmOpts0{ optLevel = 0 })
          return (cruxOpts3, llvmOpts2, csettings, csrc)

     compileWith csettings prefix spec
     putStrLn ("Generated " ++ show csrc)

     let ?outputConfig = defaultOutputConfig cruxLLVMLoggingToSayWhat (Just cruxOpts)
     bcFile <- withCruxLLVMLogging (genBitCode cruxOpts llvmOpts)
     putStrLn ("Compiled " ++ prefix ++ " into " ++ bcFile)

     verifyBitcode csettings properties spec cruxOpts llvmOpts bcFile

verifyBitcode ::
  CSettings ->
  [String] ->
  Spec ->
  CruxOptions ->
  LLVMOptions ->
  FilePath ->
  IO ()
verifyBitcode csettings properties spec cruxOpts llvmOpts bcFile =
  do halloc <- newHandleAllocator
     sym <- newSimpleBackend FloatUninterpretedRepr globalNonceGenerator
     -- turn on hash-consing
     startCaching sym
     bbMapRef <- newIORef mempty
     let ?recordLLVMAnnotation = \an bb -> modifyIORef bbMapRef (Map.insert an bb)
     let ?outputConfig = defaultOutputConfig cruxLLVMLoggingToSayWhat (Just cruxOpts)

     let adapters = [z3Adapter] -- TODO? configurable
     extendConfig (solver_adapter_config_options z3Adapter) (getConfiguration sym)

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
     let ?intrinsicsOpts = intrinsicsOpts llvmOpts

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $
       withCruxLLVMLogging $
       do emptyMem   <- initializeAllMemory sym llvmCtxt llvmMod
          initialMem <- populateAllGlobals sym (globalInitMap trans) emptyMem

          putStrLn "Generating proof state data"
          proofStateBundle <- CW4.computeBisimulationProofBundle sym properties spec

          verifyInitialState cruxOpts adapters bbMapRef simctx initialMem
             (CW4.initialStreamState proofStateBundle)

          verifyStepBisimulation cruxOpts adapters csettings
             bbMapRef simctx llvmMod trans memVar emptyMem proofStateBundle

verifyInitialState ::
  IsSymInterface sym =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  sym ~ ExprBuilder t st fs =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>

  CruxOptions ->
  [SolverAdapter st] ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  MemImpl sym ->
  CW4.BisimulationProofState sym ->
  IO ()
verifyInitialState cruxOpts adapters bbMapRef simctx mem initialState =
  do let sym = simctx^.ctxSymInterface
     putStrLn "Computing initial state verification conditions"
     frm <- pushAssumptionFrame sym

     assertStateRelation sym mem initialState

     popUntilAssumptionFrame sym frm

     putStrLn "Proving initial state verification conditions"
     proveObls cruxOpts adapters bbMapRef simctx

verifyStepBisimulation ::
  IsSymInterface sym =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  sym ~ ExprBuilder t st fs =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (1 <= ArchWidth arch) =>
  HasPtrWidth (ArchWidth arch) =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>

  CruxOptions ->
  [SolverAdapter st] ->
  CSettings ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  L.Module ->
  ModuleTranslation arch ->
  GlobalVar Mem ->
  MemImpl sym ->
  CW4.BisimulationProofBundle sym ->
  IO ()
verifyStepBisimulation cruxOpts adapters csettings bbMapRef simctx llvmMod modTrans memVar mem prfbundle =
  do let sym = simctx^.ctxSymInterface
     putStrLn "Computing step bisimulation verification conditions"

     frm <- pushAssumptionFrame sym

     do -- set up the memory image
        mem' <- setupPrestate sym mem prfbundle

        -- sanity check, verify that we set up the memory in the expected relation
        assertStateRelation sym mem' (CW4.preStreamState prfbundle)

        -- set up trigger guard global variables
        let halloc = simHandleAllocator simctx
        let prepTrigger (nm, guard, _) =
              do gv <- freshGlobalVar halloc (Text.pack (nm ++ "_called")) BoolRepr
                 return (nm, gv, guard)
        triggerGlobals <- mapM prepTrigger (CW4.triggerState prfbundle)

        -- execute the step function
        let overrides = zipWith triggerOverride triggerGlobals (CW4.triggerState prfbundle)
        mem'' <- executeStep csettings simctx memVar mem' llvmMod modTrans triggerGlobals overrides (CW4.assumptions prfbundle)

        -- assert the poststate is in the relation
        assertStateRelation sym mem'' (CW4.postStreamState prfbundle)

     popUntilAssumptionFrame sym frm

     putStrLn "Proving step bisimulation verification conditions"
     proveObls cruxOpts adapters bbMapRef simctx


triggerOverride ::
  IsSymInterface sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (1 <= ArchWidth arch) =>
  HasPtrWidth (ArchWidth arch) =>
  HasLLVMAnn sym =>

  (Name, GlobalVar BoolType, Pred sym) ->
  (Name, BoolExpr t, [(Some Type, CW4.XExpr sym)]) ->
  OverrideTemplate (Crux sym) sym arch (RegEntry sym Mem) EmptyCtx Mem
triggerOverride (_,triggerGlobal,_) (nm, _guard, args) =
   let args' = map toTypeRepr args in
   case Ctx.fromList args' of
     Some argCtx ->
      basic_llvm_override $
      LLVMOverride decl argCtx UnitRepr $
        \_memOps sym calledArgs ->
          do writeGlobal triggerGlobal (truePred sym)
             liftIO $ checkArgs sym (toListFC Some calledArgs) (map snd args)
             return ()

 where
  decl = L.Declare
         { L.decLinkage = Nothing
         , L.decVisibility = Nothing
         , L.decRetType = L.PrimType L.Void
         , L.decName = L.Symbol nm
         , L.decArgs = map llvmArgTy args
         , L.decVarArgs = False
         , L.decAttrs = []
         , L.decComdat = Nothing
         }

  toTypeRepr (Some ctp, _) = llvmTypeAsRepr (copilotTypeToMemType (llvmDataLayout ?lc) ctp) Some
  llvmArgTy (Some ctp, _) = copilotTypeToLLVMType ctp

  checkArgs sym = loop (0::Integer)
    where
    loop i (x:xs) (v:vs) = checkArg sym i x v >> loop (i+1) xs vs
    loop _ [] [] = return ()
    loop _ _ _ = fail $ "Argument list mismatch in " ++ nm

  checkArg sym i (Some (RegEntry tp v)) x =
    do eq <- computeEqualVals sym x tp v
       let shortmsg = "Trigger " ++ show nm ++ " argument " ++ show i
       let longmsg  = show (printSymExpr eq)
       let rsn      = AssertFailureSimError shortmsg longmsg
       loc <- getCurrentProgramLoc sym
       addDurableProofObligation sym (LabeledPred eq (SimError loc rsn))


executeStep :: forall sym arch.
  IsSymInterface sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (1 <= ArchWidth arch) =>
  HasPtrWidth (ArchWidth arch) =>
  HasLLVMAnn sym =>

  CSettings ->
  SimCtxt Crux sym LLVM ->
  GlobalVar Mem ->
  MemImpl sym ->
  L.Module ->
  ModuleTranslation arch ->
  [(Name, GlobalVar BoolType, Pred sym)] ->
  [OverrideTemplate (Crux sym) sym arch (RegEntry sym Mem) EmptyCtx Mem] ->
  [Pred sym] ->
  IO (MemImpl sym)
executeStep csettings simctx memVar mem llvmmod modTrans triggerGlobals triggerOverrides assums =
  do let initSt = InitialState simctx globSt defaultAbortHandler memRepr $
                    runOverrideSim memRepr runStep
     res <- executeCrucible [] initSt
     case res of
       FinishedResult _ pr -> return (pr^.partialValue.gpValue.to regValue)
       AbortedResult{} -> fail "simulation aborted!"
       TimeoutResult{} -> fail "simulation timed out!"
 where
  setupTrigger gs (_,gv,_) = insertGlobal gv (falsePred sym) gs
  globSt = foldl setupTrigger (llvmGlobals memVar mem) triggerGlobals
  llvm_ctx = modTrans ^. transContext
  stepName = cSettingsStepFunctionName csettings
  sym = simctx^.ctxSymInterface

  dummyLoc = mkProgramLoc "<>" InternalPos

  assumeProperty b =
    addAssumption sym (GenericAssumption dummyLoc "Property assumption" b)

  runStep :: OverrideSim (Crux sym) sym LLVM (RegEntry sym Mem) EmptyCtx Mem (MemImpl sym)
  runStep =
    do -- set up built-in functions
       register_llvm_overrides llvmmod [] triggerOverrides llvm_ctx
       -- set up functions defined in the module
       mapM_ (registerModuleFn llvm_ctx) (Map.elems (cfgMap modTrans))

       -- make any property assumptions
       liftIO (mapM_ assumeProperty assums)

       -- look up and run the step function
       () <- case Map.lookup (L.Symbol stepName) (cfgMap modTrans) of
         Just (_, AnyCFG anyCfg) ->
           case (cfgArgTypes anyCfg, cfgReturnType anyCfg) of
             (Empty, UnitRepr) -> regValue <$> callCFG anyCfg emptyRegMap
             _ -> fail $ unwords [show stepName, "should take no arguments and return void"]
         Nothing -> fail $ unwords ["Could not find step function named", show stepName]

       forM_ triggerGlobals $ \(nm, gv, guard) ->
         do guard' <- readGlobal gv
            eq <- liftIO $ eqPred sym guard guard'
            let shortmsg = "Trigger guard equality condition: " ++ show nm
            let longmsg  = show (printSymExpr eq)
            let rsn      = AssertFailureSimError shortmsg longmsg
            liftIO $ addDurableProofObligation sym (LabeledPred eq (SimError dummyLoc rsn))

       -- return the final state of the memory
       readGlobal memVar

setupPrestate ::
  IsSymInterface sym =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>

  sym ->
  MemImpl sym ->
  CW4.BisimulationProofBundle sym ->
  IO (MemImpl sym)
setupPrestate sym mem0 prfbundle =
  do mem' <- foldM setupStreamState mem0 (CW4.streamState (CW4.preStreamState prfbundle))
     foldM setupExternalInput mem' (CW4.externalInputs prfbundle)

 where
   sizeTStorage :: StorageType
   sizeTStorage = bitvectorType (bitsToBytes (intValue ?ptrWidth))

   setupExternalInput mem (nm, Some ctp, v) =
     do -- Compute LLVM/Crucible type information from the Copilot type
        let memTy      = copilotTypeToMemType' (llvmDataLayout ?lc) ctp
        let typeAlign  = memTypeAlign (llvmDataLayout ?lc) memTy
        stType <- toStorableType memTy
        Some typeRepr <- return (llvmTypeAsRepr memTy Some)

        -- resolve the global varible to a pointers
        ptrVal <- doResolveGlobal sym mem (L.Symbol nm)

        -- write the value into the global
        regVal <- copilotExprToRegValue sym v typeRepr
        doStore sym mem ptrVal typeRepr stType typeAlign regVal

   setupStreamState mem (nm, Some ctp, vs) =
     do -- TODO, should get these from somewhere inside copilot instead of building these names directly
        let idxName = "s" ++ show nm ++ "_idx"
        let bufName = "s" ++ show nm
        let buflen  = genericLength vs :: Integer

        -- Compute LLVM/Crucible type information from the Copilot type
        let memTy      = copilotTypeToMemType' (llvmDataLayout ?lc) ctp
        let typeLen    = memTypeSize (llvmDataLayout ?lc) memTy
        let typeAlign  = memTypeAlign (llvmDataLayout ?lc) memTy
        stType <- toStorableType memTy
        Some typeRepr <- return (llvmTypeAsRepr memTy Some)

        -- Resolve the global names into base pointers
        idxPtr <- doResolveGlobal sym mem (L.Symbol idxName)
        bufPtr <- doResolveGlobal sym mem (L.Symbol bufName)

        -- Create a fresh index value in the proper range
        idxVal <- freshBoundedBV sym (safeSymbol idxName) ?ptrWidth
                     (Just 0) (Just (fromIntegral (buflen - 1)))
        idxVal' <- llvmPointer_bv sym idxVal

        -- store the index value in the correct location
        let sizeTAlign = memTypeAlign (llvmDataLayout ?lc) (IntType (natValue ?ptrWidth))
        mem' <- doStore sym mem idxPtr (LLVMPointerRepr ?ptrWidth) sizeTStorage sizeTAlign idxVal'

        buflen'  <- bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth buflen)
        typeLen' <- bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth (toInteger typeLen))

        flip execStateT mem' $
          forM_ (zip vs [0 ..]) $ \(v,i) ->
            do ptrVal <- lift $
                 do x1 <- bvAdd sym idxVal =<< bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth i)
                    x2 <- bvUrem sym x1 buflen'
                    x3 <- bvMul sym x2 typeLen'
                    ptrAdd sym ?ptrWidth bufPtr x3

               regVal <- lift $ copilotExprToRegValue sym v typeRepr
               StateT $ \m ->
                 do m' <- doStore sym m ptrVal typeRepr stType typeAlign regVal
                    return ((),m')

assertStateRelation ::
  IsSymInterface sym =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>

  sym ->
  MemImpl sym ->
  CW4.BisimulationProofState sym ->
  IO ()
assertStateRelation sym mem prfst =
  -- For each stream in the proof state, assert that the
  -- generated ring buffer global contains the corresponding
  -- values.
  forM_ (CW4.streamState prfst) assertStreamState

 where
   sizeTStorage :: StorageType
   sizeTStorage = bitvectorType (bitsToBytes (intValue ?ptrWidth))

   assertStreamState (nm, Some ctp, vs) =
     do -- TODO, should get these from somewhere inside copilot instead of building these names directly
        let idxName = "s" ++ show nm ++ "_idx"
        let bufName = "s" ++ show nm
        let buflen  = genericLength vs :: Integer

        -- Compute LLVM/Crucible type information from the Copilot type
        let memTy      = copilotTypeToMemType' (llvmDataLayout ?lc) ctp
        let typeLen    = memTypeSize (llvmDataLayout ?lc) memTy
        let typeAlign  = memTypeAlign (llvmDataLayout ?lc) memTy
        stType <- toStorableType memTy
        Some typeRepr <- return (llvmTypeAsRepr memTy Some)

        -- Resolve the global names into base pointers
        idxPtr <- doResolveGlobal sym mem (L.Symbol idxName)
        bufPtr <- doResolveGlobal sym mem (L.Symbol bufName)

        -- read the value of the ring buffer index
        let sizeTAlign = memTypeAlign (llvmDataLayout ?lc) (IntType (natValue ?ptrWidth))
        idxVal <- projectLLVM_bv sym =<<
          doLoad sym mem idxPtr sizeTStorage (LLVMPointerRepr ?ptrWidth) sizeTAlign

        buflen'  <- bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth buflen)
        typeLen' <- bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth (toInteger typeLen))

        -- For each value in the stream description, read a corresponding value from
        -- memory and assert that they are equal.
        forM_ (zip vs [0 ..]) $ \(v,i) ->
          do ptrVal <-
               do x1 <- bvAdd sym idxVal =<< bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth i)
                  x2 <- bvUrem sym x1 buflen'
                  x3 <- bvMul sym x2 typeLen'
                  ptrAdd sym ?ptrWidth bufPtr x3

             v' <- doLoad sym mem ptrVal stType typeRepr typeAlign
             eq <- computeEqualVals sym v typeRepr v'
             let shortmsg = "State equality condition: " ++ show nm ++ " index value " ++ show i
             let longmsg  = show (printSymExpr eq)
             let rsn      = AssertFailureSimError shortmsg longmsg
             let loc      = mkProgramLoc "<>" InternalPos
             addDurableProofObligation sym (LabeledPred eq (SimError loc rsn))

        return ()

copilotExprToRegValue :: forall sym tp.
  IsSymInterface sym =>
  sym ->
  CW4.XExpr sym ->
  TypeRepr tp ->
  IO (RegValue sym tp)
copilotExprToRegValue sym = loop
  where
    loop :: forall tp'. CW4.XExpr sym -> TypeRepr tp' -> IO (RegValue sym tp')

    loop (CW4.XBool b) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @1) =
      llvmPointer_bv sym =<< predToBV sym b knownRepr
    loop (CW4.XBool b) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @8) =
      llvmPointer_bv sym =<< predToBV sym b knownRepr
    loop (CW4.XInt8 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @8) =
      llvmPointer_bv sym x
    loop (CW4.XInt16 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @16) =
      llvmPointer_bv sym x
    loop (CW4.XInt32 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @32) =
      llvmPointer_bv sym x
    loop (CW4.XInt64 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @64) =
      llvmPointer_bv sym x
    loop (CW4.XWord8 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @8) =
      llvmPointer_bv sym x
    loop (CW4.XWord16 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @16) =
      llvmPointer_bv sym x
    loop (CW4.XWord32 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @32) =
      llvmPointer_bv sym x
    loop (CW4.XWord64 x) (LLVMPointerRepr w) | Just Refl <- testEquality w (knownNat @64) =
      llvmPointer_bv sym x

--    loop (CW4.XFloat x)  (FloatRepr SingleFloatRepr) v =
--      iFloatEq sym x v
--    loop (CW4.XDouble x) (FloatRepr DoubleFloatRepr) v =
--      iFloatEq sym x v

    loop CW4.XEmptyArray _ = fail "FIXME: empty array"
    loop CW4.XArray{} _ = fail "FIXME: nonempty array"
    loop CW4.XStruct{} _ = fail "FIXME: struct"

    loop x tpr =
      fail $ unlines ["Mismatch between Copilot value and crucible value", show x, show tpr]


computeEqualVals :: forall sym tp.
  IsSymInterface sym =>
  sym ->
  CW4.XExpr sym ->
  TypeRepr tp ->
  RegValue sym tp ->
  IO (Pred sym)
computeEqualVals sym = loop
  where
    loop :: forall tp'. CW4.XExpr sym -> TypeRepr tp' -> RegValue sym tp' -> IO (Pred sym)
    loop (CW4.XBool b) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @1) =
      isEq sym b =<< bvIsNonzero sym =<< projectLLVM_bv sym v
    loop (CW4.XBool b) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @8) =
      isEq sym b =<< bvIsNonzero sym =<< projectLLVM_bv sym v
    loop (CW4.XInt8 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @8) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XInt16 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @16) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XInt32 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @32) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XInt64 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @64) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XWord8 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @8) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XWord16 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @16) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XWord32 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @32) =
      bvEq sym x =<< projectLLVM_bv sym v
    loop (CW4.XWord64 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @64) =
      bvEq sym x =<< projectLLVM_bv sym v


--    loop (CW4.XFloat x)  (FloatRepr SingleFloatRepr) v =
--      iFloatEq sym x v
--    loop (CW4.XDouble x) (FloatRepr DoubleFloatRepr) v =
--      iFloatEq sym x v

    loop CW4.XEmptyArray _ _ = fail "FIXME: empty array"
    loop CW4.XArray{} _ _ = fail "FIXME: nonempty array"
    loop CW4.XStruct{} _ _ = fail "FIXME: struct"

    loop x tpr _v =
      fail $ unlines ["Mismatch between Copilot value and crucible value", show x, show tpr]

copilotTypeToMemType' ::
  DataLayout ->
  CT.Type a ->
  MemType
copilotTypeToMemType' _dl CT.Bool = i8
copilotTypeToMemType' dl tp = copilotTypeToMemType dl tp

copilotTypeToMemType ::
  DataLayout ->
  CT.Type a ->
  MemType
copilotTypeToMemType dl = loop
  where
    loop :: forall t. CT.Type t -> MemType
    loop CT.Bool   = i1
    loop CT.Int8   = i8
    loop CT.Int16  = i16
    loop CT.Int32  = i32
    loop CT.Int64  = i64
    loop CT.Word8  = i8
    loop CT.Word16 = i16
    loop CT.Word32 = i32
    loop CT.Word64 = i64
    loop CT.Float  = FloatType
    loop CT.Double = DoubleType
    loop t0@(CT.Array tp) =
      let len = fromIntegral (tylength t0) in
      ArrayType len (loop tp)
    loop (CT.Struct v) =
      StructType (mkStructInfo dl False (map val (CT.toValues v)))

    val :: forall t. CT.Value t -> MemType
    val (CT.Value tp _) = loop tp

copilotTypeToLLVMType ::
  CT.Type a ->
  L.Type
copilotTypeToLLVMType = loop
  where
    loop :: forall t. CT.Type t -> L.Type
    loop CT.Bool   = L.PrimType (L.Integer 1)
    loop CT.Int8   = L.PrimType (L.Integer 8)
    loop CT.Int16  = L.PrimType (L.Integer 16)
    loop CT.Int32  = L.PrimType (L.Integer 32)
    loop CT.Int64  = L.PrimType (L.Integer 64)
    loop CT.Word8  = L.PrimType (L.Integer 8)
    loop CT.Word16 = L.PrimType (L.Integer 16)
    loop CT.Word32 = L.PrimType (L.Integer 32)
    loop CT.Word64 = L.PrimType (L.Integer 64)
    loop CT.Float  = L.PrimType (L.FloatType L.Float)
    loop CT.Double = L.PrimType (L.FloatType L.Double)
    loop t0@(CT.Array tp) =
      let len = fromIntegral (tylength t0) in
      L.Array len (loop tp)
    loop (CT.Struct v) =
      L.Struct (map val (CT.toValues v))

    val :: forall t. CT.Value t -> L.Type
    val (CT.Value tp _) = loop tp


proveObls ::
  IsSymInterface sym =>
  sym ~ ExprBuilder t st fs =>
  Logs msgs =>
  SupportsCruxLogMessage msgs =>
  CruxOptions ->
  [SolverAdapter st] ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  IO ()
proveObls cruxOpts adapters bbMapRef simctx =
  do let sym = simctx^.ctxSymInterface
     obls <- getProofObligations sym
     clearProofObligations sym

     results <- proveGoalsOffline adapters cruxOpts simctx (explainFailure sym bbMapRef) obls
     presentResults sym results

presentResults ::
  Logs msgs =>
  IsSymInterface sym =>
  sym ->
  (ProcessedGoals, Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym))) ->
  IO ()
presentResults sym (num, goals)
  | numTotalGoals == 0
  = putStrLn $ "All obligations proved by concrete simplification"

    -- All goals were proven
  | numProvedGoals == numTotalGoals
  = printGoals

    -- There were some unproved goals, so fail with exit code 1
  | otherwise
  = do printGoals
       exitFailure
  where
    numTotalGoals  = totalProcessedGoals num
    numProvedGoals = provedGoals num

    printGoals =
      do putStrLn $ unwords ["Proved",show numProvedGoals, "of", show numTotalGoals, "total goals"]
         goals' <- provedGoalsTree sym goals
         case goals' of
           Just g -> logGoal g
           Nothing -> return ()
