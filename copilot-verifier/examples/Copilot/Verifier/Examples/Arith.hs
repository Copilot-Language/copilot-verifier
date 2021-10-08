
{-# LANGUAGE RebindableSyntax #-}

module Copilot.Verifier.Examples.Arith where

import Language.Copilot
import Copilot.Compile.C99
import Copilot.Verifier (verify)
import Copilot.Theorem.What4 (prove, Solver(..))

-- The largest unsigned 32-bit prime
lastPrime :: Stream Word32
lastPrime = 31
--lastPrime = 4294967291 -- Whelp, this prime seems too big for the solvers to handle well

multRingSpec :: Spec
multRingSpec = do
  _ <- prop "clamp nonzero" (forall ((clamp > 0) && (clamp < lastPrime)))
  _ <- prop "reduced" (forall (acc < lastPrime))
  _ <- prop "nonzero" (forall (acc > 0 && (acc < lastPrime)))

  trigger "outofrange" (not (acc > 0 && acc < lastPrime)) [arg acc]

  return ()

  where
  -- a stream of external values
  vals  = externW32 "values" Nothing

  -- Generate a value in [1, lastPrime), which
  -- is the multiplictive group of Z_p
  clamp :: Stream Word32
  clamp = (vals `mod` (lastPrime - 1)) + 1

  -- Successively multiply new values
  acc :: Stream Word32
  acc = [1] ++ unsafeCast ((cast acc * cast clamp) `mod` (cast lastPrime :: Stream Word64))

main :: IO ()
main =
  do s <- reify multRingSpec
     r <- prove Z3 s
     print r
     verify mkDefaultCSettings ["reduced"] "multRingSpec" s

--main = interpret 10 engineMonitor
