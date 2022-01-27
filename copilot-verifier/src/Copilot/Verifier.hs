{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
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

module Copilot.Verifier
  ( verify
  , verifyWithOptions
  , VerifierOptions(..)
  , defaultVerifierOptions
  , sideCondVerifierOptions
  , Verbosity(..)
  ) where

import Control.Lens (view, (^.), to)
import Control.Monad (foldM, forM_, when)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (execStateT, lift, StateT(..))
import Data.Aeson (ToJSON)
import qualified Data.Text as Text
import qualified Data.Map.Strict as Map
import Data.IORef (newIORef, modifyIORef, IORef)
import qualified Text.LLVM.AST as L
import Data.List (genericLength)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import qualified Data.Vector as V
import qualified Data.BitVector.Sized as BV
import GHC.Generics (Generic)
import qualified Prettyprinter as PP
import System.Exit (exitFailure)
import System.FilePath ((</>))

import Copilot.Compile.C99 (CSettings(..), compileWith)
import Copilot.Core
import qualified Copilot.Core.Type as CT

import qualified Copilot.Theorem.What4 as CW4

import qualified Copilot.Verifier.Log as Log

import Data.Parameterized.Ctx (EmptyCtx)
import Data.Parameterized.Context (pattern Empty)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.NatRepr (intValue, natValue, testEquality, knownNat, type (<=) )
import Data.Parameterized.Nonce (globalNonceGenerator)
import Data.Parameterized.Some (Some(..))
import Data.Parameterized.TraversableFC (toListFC)
import Data.Parameterized.TraversableFC.WithIndex (ifoldlMFC)
import qualified Data.Parameterized.Vector as PVec

import Lang.Crucible.Backend
  ( IsSymInterface, Goals(..), Assumptions, Assertion
  , pushAssumptionFrame, popUntilAssumptionFrame
  , getProofObligations, clearProofObligations
  , LabeledPred(..), addDurableProofObligation
  , addAssumption, CrucibleAssumption(..), ppAbortExecReason
  , IsSymBackend(..), HasSymInterface(..)
  -- , ProofObligations, proofGoal, goalsToList, labeledPredMsg
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
  , AbortedResult(..)
  )
import Lang.Crucible.Simulator.ExecutionTree ( withBackend )
import Lang.Crucible.Simulator.GlobalState ( insertGlobal )
import Lang.Crucible.Simulator.RegValue (RegValue, RegValue'(..))
import Lang.Crucible.Simulator.SimError (SimError(..), SimErrorReason(..)) -- ppSimError
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
  ( MemType(..), SymType(..)
  , i1, i8, i16, i32, i64
  , memTypeSize, memTypeAlign
  , mkStructInfo
  )
import Lang.Crucible.LLVM.MemModel
  ( mkMemVar, withPtrWidth, HasLLVMAnn, MemImpl, LLVMAnnMap
  , HasPtrWidth, doResolveGlobal, doLoad, doStore
  , MemOptions, StorageType, bitvectorType
  , ptrAdd, toStorableType, projectLLVM_bv
  , pattern LLVMPointerRepr, pattern PtrRepr, llvmPointer_bv
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
import Crux.Config.Common
  ( cruxOptions, CruxOptions(..), postprocessOptions, outputOptions
  , OutputOptions(..)
  )
import Crux.Goal (proveGoalsOffline, provedGoalsTree)
import qualified Crux.Log as Log
import Crux.Types (SimCtxt, Crux, ProcessedGoals(..), ProofResult(..))

import Crux.LLVM.Config (llvmCruxConfig, LLVMOptions(..))
import Crux.LLVM.Compile (genBitCode)
import qualified Crux.LLVM.Log as Log
import Crux.LLVM.Simulate (setupSimCtxt, parseLLVM, explainFailure)
import CruxLLVMMain (processLLVMOptions)

import What4.Config
  (extendConfig)
import What4.Interface
  ( Pred, bvLit, bvAdd, bvUrem, bvMul, bvIsNonzero, bvEq, isEq
  , getConfiguration, freshBoundedBV, predToBV
  , getCurrentProgramLoc, printSymExpr
  , truePred, falsePred, eqPred, andPred, backendPred
  )
import What4.Expr.Builder
  ( FloatModeRepr(..), ExprBuilder, BoolExpr, startCaching
  , newExprBuilder
  )
import What4.InterpretedFloatingPoint
  ( FloatInfoRepr(..), IsInterpretedFloatExprBuilder(..)
  , SingleFloat, DoubleFloat
  )
import What4.ProgramLoc (ProgramLoc, mkProgramLoc, Position(..))
import What4.Solver.Adapter (SolverAdapter(..))
import What4.Solver.Z3 (z3Adapter)
import What4.Symbol (safeSymbol)

-- | @'verify' csettings props prefix spec@ verifies the Copilot specification
-- @spec@ under the assumptions @props@ matches the behavior of the C program
-- compiled with @csettings@ within a directory prefixed by @prefix@.
verify :: CSettings -> [String] -> String -> Spec -> IO ()
verify = verifyWithOptions defaultVerifierOptions

-- | Options for configuring the behavior of the verifier.
data VerifierOptions = VerifierOptions
  { verbosity :: Verbosity
    -- ^ How much output the verifier should produce.
  , assumePartialSideConds :: Bool
    -- ^ If 'True', the verifier will determine the conditions under which
    --   a Copilot specification's partial operations are well defined and
    --   add these side conditions as assumptions. As a result, even if the
    --   generated C code performs a partial operation, the verification will
    --   succeed if this partial operation coincides with a corresponding
    --   operation on the Copilot side.
    --
    --   If 'False', the verifier will not assume any side conditions related
    --   to partial operations in the Copilot specification. As a result, any
    --   use of a partial operation in the generated C code will cause
    --   verification to fail unless the user adds their own assumptions.
  } deriving stock Show

-- | The default 'VerifierOptions':
--
-- * Produce diagnostics as verification proceeds ('Noisy').
--
-- * Do not assume any side conditions related to partial operations.
defaultVerifierOptions :: VerifierOptions
defaultVerifierOptions = VerifierOptions
  { verbosity = Noisy
  , assumePartialSideConds = False
  }

-- | Like 'defaultVerifierOptions', except that the verifier will assume side
-- conditions related to partial operations used in the Copilot spec.
sideCondVerifierOptions :: VerifierOptions
sideCondVerifierOptions = defaultVerifierOptions
  { assumePartialSideConds = True
  }

-- | How much output should verification produce?
data Verbosity
  = Noisy -- ^ Produce diagnostics as verification proceeds.
  | Quiet -- ^ Don't produce any diagnostics.
  deriving stock (Eq, Show)

-- | Like 'verify', but with 'VerifierOptions' to more finely control the
-- verifier's behavior.
verifyWithOptions :: VerifierOptions -> CSettings -> [String] -> String -> Spec -> IO ()
verifyWithOptions opts csettings0 properties prefix spec =
  withCopilotLogging $
  do -- munge options structures into the necessary forms
     (ocfg, cruxOpts, llvmOpts, csettings, csrc) <- computeConfiguration opts csettings0 prefix
     let ?outputConfig = ocfg

     -- Compile the Copilot spec into C source code, using
     -- preexisting Copilot library calls.
     compileWith csettings prefix spec
     Log.sayCopilot $ Log.GeneratedCFile csrc

     -- Compile the C source into LLVM bitcode, using preexisting
     -- Crux library calls.
     bcFile <- genBitCode cruxOpts llvmOpts
     Log.sayCopilot $ Log.CompiledBitcodeFile prefix bcFile

     -- Run the main verification procedure
     verifyBitcode opts csettings properties spec cruxOpts llvmOpts bcFile


-- | Do the (surprisingly large amount) of options munging necessary to set up
--   the crucible/crux environment.
computeConfiguration ::
  Log.SupportsCruxLogMessage CopilotLogging =>
  VerifierOptions -> CSettings -> FilePath ->
  IO (Log.OutputConfig CopilotLogging, CruxOptions, LLVMOptions, CSettings, FilePath)
computeConfiguration opts csettings0 prefix =
  do ocfg1 <- defaultOutputConfig copilotLoggingToSayWhat
     let quiet = verbosity opts == Quiet
     let ocfg2 mbOutputOpts = (ocfg1 mbOutputOpts) { Log._quiet = quiet }
     llvmcfg <- llvmCruxConfig
     let cfg = cfgJoin cruxOptions llvmcfg
     -- TODO, load from an actual configuration file?
     fileOpts <- fromFile "copilot-verifier" cfg Nothing
     (cruxOpts0, llvmOpts0) <- foldM fromEnv fileOpts (cfgEnv cfg)
     let odir0 = cSettingsOutputDirectory csettings0
     let odir = -- A bit grimy, but this corresponds to how crux-llvm sets
                -- its output directory.
                if odir0 == "."
                  then "results" </> prefix
                  else odir0
     let csettings = csettings0{ cSettingsOutputDirectory = odir }
     let csrc = odir </> prefix ++ ".c"
     let cruxOpts1 = cruxOpts0{ outDir = odir, bldDir = odir, inputFiles = [csrc]
                              , outputOptions = (outputOptions cruxOpts0)
                                                  { quietMode = quiet
                                                  }
                              }
     let ?outputConfig = ocfg2 (Just (outputOptions cruxOpts1))
     cruxOpts2 <- postprocessOptions cruxOpts1

     -- NB, we are fixing the optimization level to -O0 here
     (cruxOpts3, llvmOpts2) <- processLLVMOptions (cruxOpts2, llvmOpts0{ optLevel = 0 })

     let ocfg3 = ocfg2 (Just (outputOptions cruxOpts3))
     return (ocfg3, cruxOpts3, llvmOpts2, csettings, csrc)


data CopilotVerifierData t = CopilotVerifierData


-- | Main entry point for the verifier.
verifyBitcode ::
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  Log.SupportsCopilotLogMessage msgs =>
  VerifierOptions {- ^ Verifier-specific settings -} ->
  CSettings   {- ^ Settings used to compile the Copilot spec. Used to find the names of functions and variables. -} ->
  [String]    {- ^ Names of properties to assume during verification. -} ->
  Spec        {- ^ The input Copilot specification -} ->
  CruxOptions {- ^ Crux options -} ->
  LLVMOptions {- ^ CruxLLVM options -} ->
  FilePath    {- ^ Path to the bitcode file to verify -} ->
  IO ()
verifyBitcode opts csettings properties spec cruxOpts llvmOpts bcFile =
  do -- Set up the expression builder and symbolic backend
     halloc <- newHandleAllocator
     sym <- newExprBuilder FloatUninterpretedRepr CopilotVerifierData globalNonceGenerator
     bak <- newSimpleBackend sym
     -- turn on hash-consing
     startCaching sym

     -- capture LLVM side-condition information for use in error reporting
     bbMapRef <- newIORef mempty
     let ?recordLLVMAnnotation = \stk an bb -> modifyIORef bbMapRef (Map.insert an (stk,bb))

     -- Set up the solver to use for verification.  Right now we hard-code this to Z3.
     let adapters = [z3Adapter] -- TODO? configurable
     extendConfig (solver_adapter_config_options z3Adapter) (getConfiguration sym)

     -- Set up the Crucible/LLVM simulation context
     memVar <- mkMemVar "llvm_memory" halloc
     let simctx = (setupSimCtxt halloc bak (memOpts llvmOpts) memVar)
                  { printHandle = view Log.outputHandle ?outputConfig }

     -- Load and translate the input LLVM module
     llvmMod <- parseLLVM bcFile
     (Some trans, _warns) <-
        let ?transOpts = transOpts llvmOpts
         in translateModule halloc memVar llvmMod

     Log.sayCopilot Log.TranslatedToCrucible

     -- Grab some metadata from the bitcode file and options;
     -- make the available via implicit arguments to the places
     -- that expect them.
     let llvmCtxt = trans ^. transContext
     let ?lc = llvmCtxt ^. llvmTypeCtx
     let ?memOpts = memOpts llvmOpts
     let ?intrinsicsOpts = intrinsicsOpts llvmOpts

     llvmPtrWidth llvmCtxt $ \ptrW ->
       withPtrWidth ptrW $

       do -- Compute the LLVM memory state with global variables allocated
          -- but not initialized
          emptyMem   <- initializeAllMemory bak llvmCtxt llvmMod

          -- Compute the LLVM memory state with global variables initialized
          -- to their initial values.
          initialMem <- populateAllGlobals bak (globalInitMap trans) emptyMem

          -- Use the Copilot spec directly to compute the symbolic states
          -- necessary to carry out the states of the bisimulation proof.
          Log.sayCopilot Log.GeneratingProofState
          proofStateBundle <- CW4.computeBisimulationProofBundle sym properties spec

          -- First check that the initial state of the program matches the starting
          -- segment of the associated Copilot streams.
          verifyInitialState cruxOpts adapters bbMapRef simctx initialMem
             (CW4.initialStreamState proofStateBundle)

          -- Now, the real meat. Carry out the bisimulation step of the proof.
          verifyStepBisimulation opts cruxOpts adapters csettings
             bbMapRef simctx llvmMod trans memVar emptyMem proofStateBundle


-- | Prove that the state of the global variables at program startup
--   matches the expected initial segments of the associated Copilot
--   streams.
verifyInitialState ::
  IsSymInterface sym =>
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  Log.SupportsCopilotLogMessage msgs =>
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
  withBackend simctx $ \bak ->
  do Log.sayCopilot $ Log.ComputingConditions Log.InitialState
     frm <- pushAssumptionFrame bak

     assertStateRelation bak mem initialState

     popUntilAssumptionFrame bak frm

     Log.sayCopilot $ Log.ProvingConditions Log.InitialState
     proveObls cruxOpts adapters bbMapRef simctx


verifyStepBisimulation ::
  IsSymInterface sym =>
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  Log.SupportsCopilotLogMessage msgs =>
  sym ~ ExprBuilder t st fs =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (1 <= ArchWidth arch) =>
  HasPtrWidth (ArchWidth arch) =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>

  VerifierOptions ->
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
verifyStepBisimulation opts cruxOpts adapters csettings bbMapRef simctx llvmMod modTrans memVar mem prfbundle =
  withBackend simctx $ \bak ->
  do Log.sayCopilot $ Log.ComputingConditions Log.StepBisimulation

     frm <- pushAssumptionFrame bak

     do -- set up the memory image
        mem' <- setupPrestate bak mem prfbundle

        -- sanity check, verify that we set up the memory in the expected relation
        assertStateRelation bak mem' (CW4.preStreamState prfbundle)

        -- set up trigger guard global variables
        let halloc = simHandleAllocator simctx
        let prepTrigger (nm, guard, _) =
              do gv <- freshGlobalVar halloc (Text.pack (nm ++ "_called")) BoolRepr
                 return (nm, gv, guard)
        triggerGlobals <- mapM prepTrigger (CW4.triggerState prfbundle)

        -- execute the step function
        let overrides = zipWith triggerOverride triggerGlobals (CW4.triggerState prfbundle)
        mem'' <- executeStep opts csettings simctx memVar mem' llvmMod modTrans triggerGlobals overrides (CW4.assumptions prfbundle) (CW4.sideConds prfbundle)

        -- assert the poststate is in the relation
        assertStateRelation bak mem'' (CW4.postStreamState prfbundle)

     popUntilAssumptionFrame bak frm

     Log.sayCopilot $ Log.ProvingConditions Log.StepBisimulation
     proveObls cruxOpts adapters bbMapRef simctx


-- | Set up the "trigger override" functions.  These dummy functions
--   take the place of the external functions called by the Copilot
--   monitor when a guarded condition occurs.
--
--   Each trigger statement has a corresponding global variable that
--   is used to record if the trigger function was called; initially
--   the global is false, and is set to true when the trigger function
--   is called.  At the end of verification, we check that the value
--   of this global variable is true iff the corresponding trigger guard
--   condition is true.
--
--   The other function of the trigger overrides is to check that, when called,
--   the functions are given the expected argument values.
--
--   Otherwise, the override functions have no effects, which corresponds
--   to the assumption that the external environment makes no changes to the
--   program state that are observable to the Copilot monitor.
triggerOverride :: forall sym t arch.
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
        \memOps bak calledArgs ->
          do let sym = backendGetSym bak
             writeGlobal triggerGlobal (truePred sym)
             mem <- readGlobal memOps
             liftIO $ checkArgs bak mem (toListFC Some calledArgs) args
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

  -- Use the `-CompositePtr` functions here to ensure that arguments with array
  -- or struct types are treated as pointers. See Note [Arrays and structs].
  toTypeRepr (Some ctp, _) = llvmTypeAsRepr (copilotTypeToMemTypeCompositePtr (llvmDataLayout ?lc) ctp) Some
  llvmArgTy (Some ctp, _) = copilotTypeToLLVMTypeCompositePtr ctp

  checkArgs :: forall bak. IsSymBackend sym bak =>
    bak -> MemImpl sym -> [Some (RegEntry sym)] -> [(Some Type, CW4.XExpr sym)] -> IO ()
  checkArgs bak mem = loop (0::Integer)
    where
    loop i (x:xs) ((ctp,v):vs) = checkArg bak mem i x ctp v >> loop (i+1) xs vs
    loop _ [] [] = return ()
    loop _ _ _ = fail $ "Argument list mismatch in " ++ nm

  checkArg :: forall bak. IsSymBackend sym bak =>
    bak -> MemImpl sym -> Integer -> Some (RegEntry sym) -> Some Type -> CW4.XExpr sym -> IO ()
  checkArg bak mem i (Some (RegEntry tp v)) (Some ctp) x =
    do let sym = backendGetSym bak
       eq <- computeEqualVals bak mem ctp x tp v
       let shortmsg = "Trigger " ++ show nm ++ " argument " ++ show i
       let longmsg  = show (printSymExpr eq)
       let rsn      = AssertFailureSimError shortmsg longmsg
       loc <- getCurrentProgramLoc sym
       addDurableProofObligation bak (LabeledPred eq (SimError loc rsn))


-- | Actually execute the Crucible simulator on the generated "step" function.
--   This will record proof side-conditions into the symbolic backend, and
--   return the memory state corresponding to the function post-state.
--
--   This function will record side-conditions that arise from the semantics
--   of C itself (e.g., memory is accessed in bounds and signed arithmetic
--   doesn't overflow) as well as the conditions related to trigger functions.
executeStep :: forall sym arch.
  IsSymInterface sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>
  (?intrinsicsOpts :: IntrinsicsOptions) =>
  (1 <= ArchWidth arch) =>
  HasPtrWidth (ArchWidth arch) =>
  HasLLVMAnn sym =>

  VerifierOptions ->
  CSettings ->
  SimCtxt Crux sym LLVM ->
  GlobalVar Mem ->
  MemImpl sym ->
  L.Module ->
  ModuleTranslation arch ->
  [(Name, GlobalVar BoolType, Pred sym)] ->
  [OverrideTemplate (Crux sym) sym arch (RegEntry sym Mem) EmptyCtx Mem] ->
  [Pred sym] {- User-provided property assumptions -} ->
  [Pred sym] {- Side conditions related to partial operations -} ->
  IO (MemImpl sym)
executeStep opts csettings simctx memVar mem llvmmod modTrans triggerGlobals triggerOverrides assums sideConds =
  do let initSt = InitialState simctx globSt defaultAbortHandler memRepr $
                    runOverrideSim memRepr runStep
     res <- executeCrucible [] initSt
     case res of
       FinishedResult _ pr -> return (pr^.partialValue.gpValue.to regValue)
       AbortedResult _ abortRes -> fail $ show $ ppAbortedResult abortRes
       TimeoutResult{} -> fail "simulation timed out!"

 where
  setupTrigger gs (_,gv,_) = insertGlobal gv (falsePred sym) gs
  globSt = foldl setupTrigger (llvmGlobals memVar mem) triggerGlobals
  llvm_ctx = modTrans ^. transContext
  stepName = cSettingsStepFunctionName csettings
  sym = simctx^.ctxSymInterface

  -- TODO, would be lovely to be able to do better than dummy positions for all these things
  -- so we can correspond assumptions and asserts back to the parts of the original spec that
  -- gave rise to them.
  dummyLoc = mkProgramLoc "<>" InternalPos

  assumeProperty b =
    withBackend simctx $ \bak ->
      addAssumption bak (GenericAssumption dummyLoc "Property assumption" b)

  assumeSideCond b =
    withBackend simctx $ \bak ->
      addAssumption bak (GenericAssumption dummyLoc "Side condition for partial operation" b)

  ppAbortedResult :: AbortedResult sym ext -> PP.Doc ann
  ppAbortedResult abortRes =
    case gatherReasons abortRes of
      reason :| [] -> reason
      reasons      -> PP.vcat $ "Simulation aborted for multiple reasons."
                              : NE.toList reasons

  gatherReasons :: AbortedResult sym ext -> NonEmpty (PP.Doc ann)
  gatherReasons (AbortedExec rsn _) =
    PP.vcat ["Simulation aborted!", ppAbortExecReason rsn] :| []
  gatherReasons (AbortedExit ec) =
    PP.vcat ["Simulation called exit!", PP.viaShow ec] :| []
  gatherReasons (AbortedBranch _ _ t f) =
    gatherReasons t <> gatherReasons f

  -- Simulator entry point
  runStep :: OverrideSim (Crux sym) sym LLVM (RegEntry sym Mem) EmptyCtx Mem (MemImpl sym)
  runStep =
    do -- set up built-in functions and trigger overrides
       register_llvm_overrides llvmmod [] triggerOverrides llvm_ctx
       -- set up functions defined in the module
       mapM_ (registerModuleFn llvm_ctx) (Map.elems (cfgMap modTrans))

       -- make any property assumptions
       liftIO (mapM_ assumeProperty assums)

       -- assume side conditions related to partial operations
       when (assumePartialSideConds opts) $ liftIO $
         mapM_ assumeSideCond sideConds

       -- look up and call the step function
       () <- case Map.lookup (L.Symbol stepName) (cfgMap modTrans) of
         Just (_, AnyCFG anyCfg) ->
           case (cfgArgTypes anyCfg, cfgReturnType anyCfg) of
             (Empty, UnitRepr) -> regValue <$> callCFG anyCfg emptyRegMap
             _ -> fail $ unwords [show stepName, "should take no arguments and return void"]
         Nothing -> fail $ unwords ["Could not find step function named", show stepName]

       -- Assert that the trigger functions were called iff the associated guard condition was true
       forM_ triggerGlobals $ \(nm, gv, guard) ->
         do guard' <- readGlobal gv
            eq <- liftIO $ eqPred sym guard guard'
            let shortmsg = "Trigger guard equality condition: " ++ show nm
            let longmsg  = show (printSymExpr eq)
            let rsn      = AssertFailureSimError shortmsg longmsg
            withBackend simctx $ \bak ->
              liftIO $ addDurableProofObligation bak (LabeledPred eq (SimError dummyLoc rsn))

       -- return the final state of the memory
       readGlobal memVar

-- | Given a bisimulation proof bundle and an empty initial state,
--   populate the global ring-buffer variables with abstract state
--   values, and write the abstract values of the external stream
--   values into their proper locations.
setupPrestate ::
  IsSymBackend sym bak =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>

  bak ->
  MemImpl sym ->
  CW4.BisimulationProofBundle sym ->
  IO (MemImpl sym)
setupPrestate bak mem0 prfbundle =
  do mem' <- foldM setupStreamState mem0 (CW4.streamState (CW4.preStreamState prfbundle))
     foldM setupExternalInput mem' (CW4.externalInputs prfbundle)

 where
   sym = backendGetSym bak

   sizeTStorage :: StorageType
   sizeTStorage = bitvectorType (bitsToBytes (intValue ?ptrWidth))

   setupExternalInput mem (nm, Some ctp, v) =
     do -- Compute LLVM/Crucible type information from the Copilot type
        let memTy      = copilotTypeToMemTypeBool8 (llvmDataLayout ?lc) ctp
        let typeAlign  = memTypeAlign (llvmDataLayout ?lc) memTy
        stType <- toStorableType memTy
        Some typeRepr <- return (llvmTypeAsRepr memTy Some)

        -- resolve the global variable to a pointers
        ptrVal <- doResolveGlobal bak mem (L.Symbol nm)

        -- write the value into the global
        regVal <- copilotExprToRegValue sym v typeRepr
        doStore bak mem ptrVal typeRepr stType typeAlign regVal

   setupStreamState mem (nm, Some ctp, vs) =
     do -- TODO, should get these from somewhere inside copilot instead of building these names directly
        let idxName = "s" ++ show nm ++ "_idx"
        let bufName = "s" ++ show nm
        let buflen  = genericLength vs :: Integer

        -- Compute LLVM/Crucible type information from the Copilot type
        let memTy      = copilotTypeToMemTypeBool8 (llvmDataLayout ?lc) ctp
        let typeLen    = memTypeSize (llvmDataLayout ?lc) memTy
        let typeAlign  = memTypeAlign (llvmDataLayout ?lc) memTy
        stType <- toStorableType memTy
        Some typeRepr <- return (llvmTypeAsRepr memTy Some)

        -- Resolve the global names into base pointers
        idxPtr <- doResolveGlobal bak mem (L.Symbol idxName)
        bufPtr <- doResolveGlobal bak mem (L.Symbol bufName)

        -- Create a fresh index value in the proper range
        idxVal <- freshBoundedBV sym (safeSymbol idxName) ?ptrWidth
                     (Just 0) (Just (fromIntegral (buflen - 1)))
        idxVal' <- llvmPointer_bv sym idxVal

        -- store the index value in the correct location
        let sizeTAlign = memTypeAlign (llvmDataLayout ?lc) (IntType (natValue ?ptrWidth))
        mem' <- doStore bak mem idxPtr (LLVMPointerRepr ?ptrWidth) sizeTStorage sizeTAlign idxVal'

        buflen'  <- bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth buflen)
        typeLen' <- bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth (toInteger typeLen))

        -- Write each value of the stream ring buffer into its correct location
        flip execStateT mem' $
          forM_ (zip vs [0 ..]) $ \(v,i) ->
            do ptrVal <- lift $
                 do x1 <- bvAdd sym idxVal =<< bvLit sym ?ptrWidth (BV.mkBV ?ptrWidth i)
                    x2 <- bvUrem sym x1 buflen'
                    x3 <- bvMul sym x2 typeLen'
                    ptrAdd sym ?ptrWidth bufPtr x3

               regVal <- lift $ copilotExprToRegValue sym v typeRepr
               StateT $ \m ->
                 do m' <- doStore bak m ptrVal typeRepr stType typeAlign regVal
                    return ((),m')

-- | Given a memory image and a "proof state", assert that the global values
--   for each stream ring buffer have values that correspond to the given
--   stream state. This collection of assertions defines the bisimulation
--   relation.
assertStateRelation ::
  IsSymBackend sym bak =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (?memOpts :: MemOptions) =>
  (?lc :: TypeContext) =>

  bak ->
  MemImpl sym ->
  CW4.BisimulationProofState sym ->
  IO ()
assertStateRelation bak mem prfst =
  -- For each stream in the proof state, assert that the
  -- generated ring buffer global contains the corresponding
  -- values.
  forM_ (CW4.streamState prfst) assertStreamState

 where
   sym = backendGetSym bak

   sizeTStorage :: StorageType
   sizeTStorage = bitvectorType (bitsToBytes (intValue ?ptrWidth))

   assertStreamState (nm, Some ctp, vs) =
     do -- TODO, should get these from somewhere inside copilot instead of building these names directly
        let idxName = "s" ++ show nm ++ "_idx"
        let bufName = "s" ++ show nm
        let buflen  = genericLength vs :: Integer

        -- Compute LLVM/Crucible type information from the Copilot type
        let memTy      = copilotTypeToMemTypeBool8 (llvmDataLayout ?lc) ctp
        let typeLen    = memTypeSize (llvmDataLayout ?lc) memTy
        let typeAlign  = memTypeAlign (llvmDataLayout ?lc) memTy
        stType <- toStorableType memTy
        Some typeRepr <- return (llvmTypeAsRepr memTy Some)

        -- Resolve the global names into base pointers
        idxPtr <- doResolveGlobal bak mem (L.Symbol idxName)
        bufPtr <- doResolveGlobal bak mem (L.Symbol bufName)

        -- read the value of the ring buffer index
        let sizeTAlign = memTypeAlign (llvmDataLayout ?lc) (IntType (natValue ?ptrWidth))
        idxVal <- projectLLVM_bv bak =<<
          doLoad bak mem idxPtr sizeTStorage (LLVMPointerRepr ?ptrWidth) sizeTAlign

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

             v' <- doLoad bak mem ptrVal stType typeRepr typeAlign
             eq <- computeEqualVals bak mem ctp v typeRepr v'
             let shortmsg = "State equality condition: " ++ show nm ++ " index value " ++ show i
             let longmsg  = show (printSymExpr eq)
             let rsn      = AssertFailureSimError shortmsg longmsg
             let loc      = mkProgramLoc "<>" InternalPos
             addDurableProofObligation bak (LabeledPred eq (SimError loc rsn))

        return ()

-- | Translate the @XExpr@ values from the "Copilot.Theorem.What4" module into
--   Crucible @RegValue@s suitable for injection into the Crucible simulator.
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

    loop (CW4.XFloat x)  (FloatRepr SingleFloatRepr) = return x
    loop (CW4.XDouble x) (FloatRepr DoubleFloatRepr) = return x

    loop CW4.XEmptyArray (VectorRepr _tpr) =
      pure V.empty
    loop (CW4.XArray xs) (VectorRepr tpr) =
      V.generateM (PVec.lengthInt xs) (\i -> loop (PVec.elemAtUnsafe i xs) tpr)
    loop (CW4.XStruct xs) (StructRepr ctx) =
      Ctx.traverseWithIndex
        (\i tpr -> RV <$> loop (xs !! Ctx.indexVal i) tpr)
        ctx

    loop x tpr =
      fail $ unlines ["Mismatch between Copilot value and crucible value", show x, show tpr]


-- | Given an @XExpr@ from from the "Copilot.Theorem.What4" module, and
--   a Crucible @RegValue@ which is expected to match, compute an equality
--   predicate between the values.  The Crucible values may be pointers,
--   requiring us to resolve the indirection through memory; this is necessary
--   for array and struct values, but would also work for scalars.
computeEqualVals :: forall sym bak tp a wptr.
  IsSymBackend sym bak =>
  HasPtrWidth wptr =>
  HasLLVMAnn sym =>
  (?lc :: TypeContext) =>
  (?memOpts :: MemOptions) =>
  bak ->
  MemImpl sym ->
  Type a ->
  CW4.XExpr sym ->
  TypeRepr tp ->
  RegValue sym tp ->
  IO (Pred sym)
computeEqualVals bak mem = loop
  where
    sym = backendGetSym bak

    loop :: forall tp' a'. Type a' -> CW4.XExpr sym -> TypeRepr tp' -> RegValue sym tp' -> IO (Pred sym)
    loop Bool (CW4.XBool b) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @1) =
      isEq sym b =<< bvIsNonzero sym =<< projectLLVM_bv bak v
    loop Bool (CW4.XBool b) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @8) =
      isEq sym b =<< bvIsNonzero sym =<< projectLLVM_bv bak v
    loop Int8 (CW4.XInt8 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @8) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Int16 (CW4.XInt16 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @16) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Int32 (CW4.XInt32 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @32) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Int64 (CW4.XInt64 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @64) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Word8 (CW4.XWord8 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @8) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Word16 (CW4.XWord16 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @16) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Word32 (CW4.XWord32 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @32) =
      bvEq sym x =<< projectLLVM_bv bak v
    loop Word64 (CW4.XWord64 x) (LLVMPointerRepr w) v | Just Refl <- testEquality w (knownNat @64) =
      bvEq sym x =<< projectLLVM_bv bak v

    loop Float (CW4.XFloat x)  (FloatRepr SingleFloatRepr) v = iFloatEq @_ @SingleFloat sym x v
    loop Double (CW4.XDouble x) (FloatRepr DoubleFloatRepr) v = iFloatEq @_ @DoubleFloat sym x v

    loop (Array _ctp) CW4.XEmptyArray (VectorRepr _tpr) vs =
      pure $ backendPred sym $ V.null vs
    loop (Array ctp) (CW4.XArray xs) (VectorRepr tpr) vs
      | PVec.lengthInt xs == V.length vs
      = V.ifoldM (\pAcc i v -> andPred sym pAcc =<< loop ctp (PVec.elemAtUnsafe i xs) tpr v)
                 (truePred sym) vs
      | otherwise
      = pure (falsePred sym)
    loop (Struct struct) (CW4.XStruct xs) (StructRepr ctx) vs
      | length copilotVals == Ctx.sizeInt (Ctx.size vs)
      = ifoldlMFC (\i pAcc tpr ->
                    case copilotVals !! Ctx.indexVal i of
                      (Value ctp _, x) ->
                        andPred sym pAcc =<< loop ctp x tpr (unRV (vs Ctx.! i)))
                  (truePred sym) ctx
      | otherwise
      = pure (falsePred sym)
      where
        copilotVals :: [(Value a', CW4.XExpr sym)]
        copilotVals = zip (toValues struct) xs

    -- If we encounter a pointer, read the memory that it points to and recurse,
    -- using the Copilot type as a guide for how much memory to read. This is
    -- needed to make array- or struct-typed arguments work (see
    -- Note [Arrays and structs]), although there is nothing about this code
    -- that is array- or struct-specific. In fact, this code could also work
    -- for pointer arguments of any other type.
    loop ctp x PtrRepr v =
      do let memTy = copilotTypeToMemTypeBool8 (llvmDataLayout ?lc) ctp
             typeAlign = memTypeAlign (llvmDataLayout ?lc) memTy
         stp <- toStorableType memTy
         llvmTypeAsRepr memTy $ \tpr ->
           do regVal <- doLoad bak mem v stp tpr typeAlign
              loop ctp x tpr regVal

    loop _ctp x tpr _v =
      fail $ unlines ["Mismatch between Copilot value and crucible value", show x, show tpr]

-- | Convert a Copilot 'CT.Type' to a Crucible 'MemType'. 'CT.Bool's are
-- assumed to be one bit in size. See @Note [How LLVM represents bool]@.
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
      ArrayType len (copilotTypeToMemTypeBool8 dl tp)
    loop (CT.Struct v) =
      StructType (mkStructInfo dl False (map val (CT.toValues v)))

    val :: forall t. CT.Value t -> MemType
    val (CT.Value tp _) = copilotTypeToMemTypeBool8 dl tp

-- | Like 'copilotTypeToMemType', except that 'CT.Bool's are assumed to be
-- eight bits, not one bit. See @Note [How LLVM represents bool]@.
copilotTypeToMemTypeBool8 ::
  DataLayout ->
  CT.Type a ->
  MemType
copilotTypeToMemTypeBool8 _dl CT.Bool = i8
copilotTypeToMemTypeBool8 dl tp = copilotTypeToMemType dl tp

-- | Like 'copilotTypeToMemType', except that composite types (i.e.,
-- 'CT.Array's and 'CT.Struct's) are converted to 'PtrType's instead of direct
-- 'ArrayType's or 'StructType's. See @Note [Arrays and structs]@.
copilotTypeToMemTypeCompositePtr ::
  DataLayout ->
  CT.Type a ->
  MemType
copilotTypeToMemTypeCompositePtr dl (CT.Array tp) =
  PtrType (MemType (copilotTypeToMemTypeBool8 dl tp))
copilotTypeToMemTypeCompositePtr _dl (CT.Struct struct) =
  PtrType (Alias (copilotStructIdent struct))
copilotTypeToMemTypeCompositePtr dl tp = copilotTypeToMemType dl tp

-- | Convert a Copilot 'CT.Type' to an LLVM 'L.Type'. 'CT.Bool's are
-- assumed to be one bit in size. See @Note [How LLVM represents bool]@.
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
      L.Array len (copilotTypeToLLVMTypeBool8 tp)
    loop (CT.Struct v) =
      L.Struct (map val (CT.toValues v))

    val :: forall t. CT.Value t -> L.Type
    val (CT.Value tp _) = copilotTypeToLLVMTypeBool8 tp

-- | Like 'copilotTypeToLLVMType', except that 'CT.Bool's are assumed to be
-- eight bits, not one bit. See @Note [How LLVM represents bool]@.
copilotTypeToLLVMTypeBool8 ::
  CT.Type a ->
  L.Type
copilotTypeToLLVMTypeBool8 CT.Bool = L.PrimType (L.Integer 8)
copilotTypeToLLVMTypeBool8 tp = copilotTypeToLLVMType tp

-- | Like 'copilotTypeToLLVMType', except that composite types (i.e.,
-- 'CT.Array's and 'CT.Struct's) are converted to 'L.PtrTo' instead of direct
-- 'L.Array's or 'L.Struct's. See @Note [Arrays and structs]@.
copilotTypeToLLVMTypeCompositePtr ::
  CT.Type a ->
  L.Type
copilotTypeToLLVMTypeCompositePtr (CT.Array tp) =
  L.PtrTo (copilotTypeToLLVMTypeBool8 tp)
copilotTypeToLLVMTypeCompositePtr (CT.Struct struct) =
  L.PtrTo (L.Alias (copilotStructIdent struct))
copilotTypeToLLVMTypeCompositePtr tp = copilotTypeToLLVMType tp

-- | Given a struct @s@, construct the name @struct.s@ as an LLVM identifier.
copilotStructIdent :: Struct a => a -> L.Ident
copilotStructIdent struct = L.Ident $ "struct." ++ typename struct

{-
Note [How LLVM represents bool]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
How are C values of type `bool` represented in LLVM? It depends. If it's being
stored directly a `bool`, it's represented with `i1` (i.e., a single bit). If
a `bool` is a member of some composite type, such as a pointer, array, or
struct, however, it's representing with `i8` (i.e., eight bits). This means
that we have to be careful when converting Bool-typed Copilot values, as they
can become `i1` or `i8` depending on the context.

copilot-verifier handles this by having both `copilotTypeToLLVMType` and
`copilotTypeToLLVMTypeBool8` functions. The former function treats `bool`s as
`i1`, whereas the latter treats `bool`s as `i8`. The former is used when
converting "top-level" types (e.g., the argument types in a trigger override),
whereas the latter is used when converting types that are part of a larger
composite type (e.g., the element type in an array).

The story for the `copilotTypeToMemType` and `copilotTypeToMemTypeBool8`
functions is similar.

Note [Arrays and structs]
~~~~~~~~~~~~~~~~~~~~~~~~~
When Clang compiles a function with an array argument, such as this trigger
function:

  void func(int32_t func_arg0[2]) { ... }

It will produce the following LLVM code:

  declare void @func(i32*) { ... }

Note that the argument is an i32*, not a [2 x i32]. As a result, we can't
translate Copilot array types directly to LLVM array types when they're used as
arguments to a function. This impedance mismatch is handled in two places:

1. The `copilotTypeToMemTypeCompositePtr`/`copilotTypeToLLVMTypeCompositePtr`
   functions special-case Copilot arrays such that they are translated to
   pointers. These functions are used when declaring the argument types of an
   override for a trigger function (see `triggerOverride`).
2. The `computeEqualVals` function has a special case for pointer
   arguments—see the case that matches on `PtrRepr`. When a `PtrRepr` is
   encountered, the underlying array values that it points to are read from
   memory. Because `PtrRepr` doesn't record the type of the thing being pointed
   to, `computeEqualVals` uses the corresponding Copilot type as a guide to
   determine how much memory to read and at what type the memory should be
   used. After this, `computeEqualVals` reads from the read array
   element-by-element—see the `VectorRepr` cases.

   Note that unlike `computeEqualVals`, `copilotExprToRegValue` does not need
   a `PtrRepr` case. This is because `copilotExprToRegValue` is ultimately used
   in service of calling writing elements of streams to memory, and streams do
   not store pointer values (at least, not in today's Copilot).

There is a very similar story for structs. Copilot passes structs by reference
in trigger functions (e.g., `void trigger(struct s *ss)`), so we must also load
from a `PtrRepr` in `computeEqualVals` to handle structs.
-}


-- | Given a simulator state, extract any collected proof obligations,
--   attempt to prove them, and present the results to the user.
--
--   Afterward, the simulator state will be cleared of any proof obligations,
--   regardless of if they could all be proved.
proveObls ::
  IsSymInterface sym =>
  sym ~ ExprBuilder t st fs =>
  Log.Logs msgs =>
  Log.SupportsCruxLogMessage msgs =>
  Log.SupportsCopilotLogMessage msgs =>
  CruxOptions ->
  [SolverAdapter st] ->
  IORef (LLVMAnnMap sym) ->
  SimCtxt Crux sym LLVM ->
  IO ()
proveObls cruxOpts adapters bbMapRef simctx =
  withBackend simctx $ \bak ->
  do let sym = backendGetSym bak
     obls <- getProofObligations bak
     clearProofObligations bak

--     mapM_ (print . ppSimError) (summarizeObls sym obls)

     results <- proveGoalsOffline adapters cruxOpts simctx (explainFailure sym bbMapRef) obls
     presentResults sym results

{-
summarizeObls :: sym -> ProofObligations sym -> [SimError]
summarizeObls _ Nothing = []
summarizeObls _ (Just obls) = map (view labeledPredMsg . proofGoal) (goalsToList obls)
-}

presentResults ::
  Log.Logs msgs =>
  Log.SupportsCopilotLogMessage msgs =>
  IsSymInterface sym =>
  sym ->
  (ProcessedGoals, Maybe (Goals (Assumptions sym) (Assertion sym, [ProgramLoc], ProofResult sym))) ->
  IO ()
presentResults sym (num, goals)
  | numTotalGoals == 0
  = Log.sayCopilot Log.AllGoalsProved

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
      do Log.sayCopilot $ Log.OnlySomeGoalsProved numProvedGoals numTotalGoals
         goals' <- provedGoalsTree sym goals
         case goals' of
           Just g -> Log.logGoal g
           Nothing -> return ()

data CopilotLogging
  = LoggingCrux Log.CruxLogMessage
  | LoggingCruxLLVM Log.CruxLLVMLogMessage
  | LoggingCopilot Log.CopilotLogMessage
  deriving stock Generic
  deriving anyclass ToJSON

copilotLoggingToSayWhat :: CopilotLogging -> Log.SayWhat
copilotLoggingToSayWhat (LoggingCrux msg) = Log.cruxLogMessageToSayWhat msg
copilotLoggingToSayWhat (LoggingCruxLLVM msg) = Log.cruxLLVMLogMessageToSayWhat msg
copilotLoggingToSayWhat (LoggingCopilot msg) = Log.copilotLogMessageToSayWhat msg

withCopilotLogging ::
  ( ( Log.SupportsCruxLogMessage CopilotLogging
    , Log.SupportsCruxLLVMLogMessage CopilotLogging
    , Log.SupportsCopilotLogMessage CopilotLogging
    ) => computation ) ->
  computation
withCopilotLogging computation = do
  let ?injectCruxLogMessage = LoggingCrux
      ?injectCruxLLVMLogMessage = LoggingCruxLLVM
      ?injectCopilotLogMessage = LoggingCopilot
    in computation
