--------------------------------------------------------------------------------
-- Copyright 2019 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

-- This is a simple example with basic usage. It implements a simple home
-- heating system: It heats when temp gets too low, and stops when it is high
-- enough. It read temperature as a byte (range -50C to 100C) and translates
-- this to Celcius.

module Copilot.Verifier.Examples.ShouldPass.Heater where

import Language.Copilot
import Copilot.Compile.C99
import Copilot.Core.PrettyPrint as PP
--import Copilot.Language.Prelude

import Copilot.Verifier ( Verbosity(..), VerifierOptions(..)
                        , defaultVerifierOptions, verifyWithOptions )

import qualified Prelude as P
import Control.Monad (when)

-- External temperature as a byte, range of -50C to 100C
temp :: Stream Word8
temp = extern "temperature" Nothing

-- Calculate temperature in Celcius.
-- We need to cast the Word8 to a Float. Note that it is an unsafeCast, as there
-- is no direct relation between Word8 and Float.
ctemp :: Stream Float
ctemp = (unsafeCast temp) * constant (150.0/255.0) - 50.0

-- width of the sliding window
window :: Int
window = 5

-- Compute the sliding average of the last 5 temps
avgTemp :: Stream Float
avgTemp = (sum window (replicate window 19.0 ++ ctemp)) / fromIntegral window

spec :: Spec
spec = do
  trigger "heaton"  (avgTemp < 18.0) [arg avgTemp]
  trigger "heatoff" (avgTemp > 21.0) [arg avgTemp]

-- Compile the spec
verifySpec :: Verbosity -> IO ()
verifySpec verb =
  do rspec <- reify spec
     when (verb P.== Noisy) $ putStrLn (PP.prettyPrint rspec)
     verifyWithOptions defaultVerifierOptions{verbosity = verb}
                       mkDefaultCSettings [] "heater"
                       rspec

{-
  do spec' <- reify spec
     putStrLn $ prettyPrintDot spec'
-}
