{-# LANGUAGE OverloadedStrings #-}
module Copilot.Verifier.Examples (allExamples) where

import qualified Data.CaseInsensitive as CI
import Data.CaseInsensitive (CI)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)

import qualified Copilot.Verifier.Examples.Arith   as Arith
import qualified Copilot.Verifier.Examples.Clock   as Clock
import qualified Copilot.Verifier.Examples.Counter as Counter
import qualified Copilot.Verifier.Examples.Engine  as Engine
import qualified Copilot.Verifier.Examples.Heater  as Heater
import qualified Copilot.Verifier.Examples.Voting  as Voting

allExamples :: Map (CI Text) (IO ())
allExamples = Map.fromList
    [ example "Arith" Arith.main
    , example "Clock" Clock.main
    , example "Counter" Counter.main
    , example "Engine" Engine.main
    , example "Heater" Heater.main
    , example "Voting" Voting.main
    ]
  where
    example :: Text -> IO () -> (CI Text, IO ())
    example name action = (CI.mk name, action)
