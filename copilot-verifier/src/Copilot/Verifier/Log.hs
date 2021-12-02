{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
module Copilot.Verifier.Log
  ( SupportsCopilotLogMessage
  , CopilotLogMessage(..)
  , VerificationStep(..)
  , sayCopilot
  , copilotLogMessageToSayWhat
  ) where

import Crux (SayLevel (..), SayWhat (..))
import qualified Crux.Log as Log
import Data.Aeson (ToJSON)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

data CopilotLogMessage
  = GeneratedCFile FilePath -- The path of the generated C File
  | CompiledBitcodeFile String -- The prefix to use in the compiled bitcode's directory
                        FilePath -- The name of the generated LLVM bitcode file
  | TranslatedToCrucible
  | GeneratingProofState
  | ComputingConditions VerificationStep
  | ProvingConditions VerificationStep
  | AllGoalsProved
  | OnlySomeGoalsProved Integer -- Number of goals proved
                        Integer -- Number of total goals
  deriving stock Generic
  deriving anyclass ToJSON

data VerificationStep
  = InitialState
  | StepBisimulation
  deriving stock Generic
  deriving anyclass ToJSON

type SupportsCopilotLogMessage msgs =
  (?injectCopilotLogMessage :: CopilotLogMessage -> msgs)

sayCopilot ::
  Log.Logs msgs =>
  SupportsCopilotLogMessage msgs =>
  CopilotLogMessage ->
  IO ()
sayCopilot msg =
  let ?injectMessage = ?injectCopilotLogMessage
   in Log.say msg

copilotTag :: Text
copilotTag = "copilot-verifier"

-- copilotFail :: Text -> SayWhat
-- copilotFail = SayWhat Fail copilotTag

copilotSimply :: Text -> SayWhat
copilotSimply = SayWhat Simply copilotTag

-- copilotWarn :: Text -> SayWhat
-- copilotWarn = SayWhat Warn copilotTag

copilotLogMessageToSayWhat :: CopilotLogMessage -> SayWhat
copilotLogMessageToSayWhat (GeneratedCFile csrc) =
  copilotSimply $ "Generated " <> T.pack (show csrc)
copilotLogMessageToSayWhat (CompiledBitcodeFile prefix bcFile) =
  copilotSimply $ "Compiled " <> T.pack prefix <> " into " <> T.pack bcFile
copilotLogMessageToSayWhat TranslatedToCrucible =
  copilotSimply "Translated bitcode into Crucible"
copilotLogMessageToSayWhat GeneratingProofState =
  copilotSimply "Generating proof state data"
copilotLogMessageToSayWhat (ComputingConditions step) =
  copilotSimply $ "Computing " <> describeVerificationStep step <> " verification conditions"
copilotLogMessageToSayWhat (ProvingConditions step) =
  copilotSimply $ "Proving " <> describeVerificationStep step <> " verification conditions"
copilotLogMessageToSayWhat AllGoalsProved =
  copilotSimply "All obligations proved by concrete simplification"
copilotLogMessageToSayWhat (OnlySomeGoalsProved numProvedGoals numTotalGoals) =
  copilotSimply $ T.unwords
    [ "Proved", T.pack (show numProvedGoals)
    , "of"
    , T.pack (show numTotalGoals), "total goals"
    ]

describeVerificationStep :: VerificationStep -> Text
describeVerificationStep InitialState     = "initial state"
describeVerificationStep StepBisimulation = "step bisimulation"
