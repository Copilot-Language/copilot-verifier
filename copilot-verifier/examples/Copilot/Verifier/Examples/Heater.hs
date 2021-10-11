--------------------------------------------------------------------------------
-- Copyright 2019 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

-- This is a simple example with basic usage. It implements a simple home
-- heating system: It heats when temp gets too low, and stops when it is high
-- enough. It read temperature as a byte (range -50C to 100C) and translates
-- this to Celcius.

module Copilot.Verifier.Examples.Heater where

import Language.Copilot
import Copilot.Compile.C99
--import Copilot.Core.PrettyDot (prettyPrintDot)
--import Copilot.Language.Prelude

import Copilot.Verifier (verify)

import Prelude ()

-- External temperature as a byte in degrees C
temp :: Stream Word8
temp = extern "temperature" Nothing

-- width of the sliding window
window :: Int
window = 3

-- Compute a sum of the last 3 samples
sumTemp :: Stream Word32
sumTemp = sum window (replicate 3 19 ++ cast temp)

spec :: Spec
spec = do
  trigger "heaton"  (sumTemp < (18*fromIntegral window)) [arg sumTemp]
  trigger "heatoff" (sumTemp > (21*fromIntegral window)) [arg sumTemp]

-- Compile the spec
main :: IO ()
main = reify spec >>= verify mkDefaultCSettings [] "heater"
{-
  do spec' <- reify spec
     putStrLn $ prettyPrintDot spec'
-}
