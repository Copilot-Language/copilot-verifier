module Main (main) where

import qualified Data.CaseInsensitive as CI
import qualified Data.Map as Map
import qualified Data.Text as Text
import Test.Tasty
import Test.Tasty.HUnit

import Copilot.Verifier.Examples (allExamples)

main :: IO ()
main = defaultMain $
  testGroup "copilot-verifier-examples tests" $
    map (\(name, action) -> testCase (Text.unpack (CI.original name)) action)
        (Map.toAscList allExamples)
