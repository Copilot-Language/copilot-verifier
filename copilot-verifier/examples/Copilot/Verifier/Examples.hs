{-# LANGUAGE OverloadedStrings #-}
module Copilot.Verifier.Examples
  ( shouldFailExamples
  , shouldPassExamples
  ) where

import qualified Data.CaseInsensitive as CI
import Data.CaseInsensitive (CI)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)

import Copilot.Verifier (Verbosity)
import qualified Copilot.Verifier.Examples.ShouldFail.UnderConstrained as UnderConstrained
import qualified Copilot.Verifier.Examples.ShouldPass.Array   as Array
import qualified Copilot.Verifier.Examples.ShouldPass.Arith   as Arith
import qualified Copilot.Verifier.Examples.ShouldPass.Clock   as Clock
import qualified Copilot.Verifier.Examples.ShouldPass.Counter as Counter
import qualified Copilot.Verifier.Examples.ShouldPass.Engine  as Engine
import qualified Copilot.Verifier.Examples.ShouldPass.FPOps   as FPOps
import qualified Copilot.Verifier.Examples.ShouldPass.Heater  as Heater
import qualified Copilot.Verifier.Examples.ShouldPass.IntOps  as IntOps
import qualified Copilot.Verifier.Examples.ShouldPass.Structs as Structs
import qualified Copilot.Verifier.Examples.ShouldPass.Voting  as Voting
import qualified Copilot.Verifier.Examples.ShouldPass.WCV     as WCV

shouldFailExamples :: Verbosity -> Map (CI Text) (IO ())
shouldFailExamples verb = Map.fromList
    [ example "UnderConstrained" (UnderConstrained.verifySpec verb)
    ]

shouldPassExamples :: Verbosity -> Map (CI Text) (IO ())
shouldPassExamples verb = Map.fromList
    [ example "Array" (Array.verifySpec verb)
    , example "Arith" (Arith.verifySpec verb)
    , example "Clock" (Clock.verifySpec verb)
    , example "Counter" (Counter.verifySpec verb)
    , example "Engine" (Engine.verifySpec verb)
    , example "FPOps" (FPOps.verifySpec verb)
    , example "Heater" (Heater.verifySpec verb)
    , example "IntOps" (IntOps.verifySpec verb)
    , example "Structs" (Structs.verifySpec verb)
    , example "Voting" (Voting.verifySpec verb)
    , example "WCV" (WCV.verifySpec verb)
    ]

example :: Text -> IO () -> (CI Text, IO ())
example name action = (CI.mk name, action)
