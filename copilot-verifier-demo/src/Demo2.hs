-- This is a simple example with basic usage. It implements a simple home
-- heating system: It heats when temp gets too low, and stops when it is high
-- enough. It read temperature as a byte (range -50C to 100C) and translates
-- this to Celcius.

{-# LANGUAGE RebindableSyntax #-}
module Demo2 (main) where

import qualified Prelude as P ()

import Language.Copilot
import Copilot.Compile.C99
import Copilot.Verifier

-- External temperature as a byte, range of -50C to 100C
temp :: Stream Word8
temp = extern "temperature"
              Nothing
              -- (Just [100, 120, 120, 120])

-- Calculate temperature in Celcius.
-- We need to cast the Word8 to a Float. Note that it is an unsafeCast, as there
-- is no direct relation between Word8 and Float.
ctemp :: Stream Float
ctemp = (unsafeCast temp * constant (150.0/255.0)) - constant 50.0

-- width of the sliding window
window :: Int
window = 5

-- Compute the sliding average of the last 5 temps
-- (Here, 19.5 is the average of 18.0 and 21.0, the two temperature extremes
-- that we check for in the spec.)
avgTemp :: Stream Float
avgTemp = (sum 5 (replicate 5 19.5 ++ ctemp)) / fromIntegral window

spec :: Spec
spec = do
  trigger "heaton"  (avgTemp < 18.0) [arg avgTemp]
  trigger "heatoff" (avgTemp > 21.0) [arg avgTemp]

main :: IO ()
main = do
  -- interpret 4 spec

  spec' <- reify spec
  compile "demo2" spec'
  verify mkDefaultCSettings [] "demo2" spec'
