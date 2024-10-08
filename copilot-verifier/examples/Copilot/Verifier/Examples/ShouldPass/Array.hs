--------------------------------------------------------------------------------
-- Copyright © 2019 National Institute of Aerospace / Galois, Inc.
--------------------------------------------------------------------------------

-- | This is a simple example for arrays. As a program, it does not make much
-- sense, however it shows of the features of arrays nicely.

-- | Enable compiler extension for type-level data, necesary for the array
-- length.

{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE DataKinds        #-}

module Copilot.Verifier.Examples.ShouldPass.Array where

import Language.Copilot
import Copilot.Compile.C99
import Copilot.Verifier ( Verbosity, VerifierOptions(..)
                        , defaultVerifierOptions, verifyWithOptions )

-- Lets define an array of length 2.
-- Make the buffer of the streams 3 elements long.
arr :: Stream (Array 2 Bool)
arr = [ array [True, False]
      , array [True, True]
      , array [False, False]] ++ arr

spec :: Spec
spec = do
  -- A trigger that fires 'func' when the first element of 'arr' is True.
  -- It passes the current value of arr as an argument.
  -- The prototype of 'func' would be:
  -- void func (int8_t arg[3]);
  trigger "func" (arr ! 0) [arg arr]

-- Compile the spec
verifySpec :: Verbosity -> IO ()
verifySpec verb = reify spec >>= verifyWithOptions defaultVerifierOptions{verbosity = verb}
                                                   mkDefaultCSettings [] "array"
-- verifySpec _ = interpret 30 spec
