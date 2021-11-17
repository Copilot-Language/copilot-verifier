{-# LANGUAGE NoImplicitPrelude #-}
module Copilot.Verifier.Examples.FPOps where

import Copilot.Compile.C99 (mkDefaultCSettings)
import qualified Copilot.Language.Stream as Copilot
import Copilot.Verifier (verify)
import Language.Copilot
import qualified Prelude as P

spec :: Spec
spec = do
  let stream :: Stream Double
      stream = extern "stream" Nothing

  triggerOp1 "abs" abs stream
  -- Currently fails due to https://github.com/GaloisInc/copilot-verifier/issues/14
  -- triggerOp1 "signum" signum stream
  triggerOp1 "recip" recip stream
  triggerOp1 "exp" exp stream
  triggerOp1 "sqrt" sqrt stream
  triggerOp1 "log" log stream
  triggerOp1 "sin" sin stream
  triggerOp1 "tan" tan stream
  triggerOp1 "cos" cos stream
  triggerOp1 "asin" asin stream
  triggerOp1 "atan" atan stream
  triggerOp1 "acos" acos stream
  triggerOp1 "sinh" sinh stream
  triggerOp1 "tanh" tanh stream
  triggerOp1 "cosh" cosh stream
  triggerOp1 "asinh" asinh stream
  triggerOp1 "atanh" atanh stream
  triggerOp1 "acosh" acosh stream
  triggerOp1 "ceiling" Copilot.ceiling stream
  triggerOp1 "floor" Copilot.floor stream

  triggerOp2 "add" (+) stream
  triggerOp2 "sub" (-) stream
  triggerOp2 "mul" (*) stream
  triggerOp2 "div" (/) stream
  triggerOp2 "pow" (**) stream
  triggerOp2 "logBase" logBase stream
  triggerOp2 "atan2" Copilot.atan2 stream

triggerOp1 :: String ->
              (Stream Double -> Stream Double) ->
              Stream Double ->
              Spec
triggerOp1 name op stream =
  trigger (name P.++ "Trigger") (testOp1 op stream) [arg stream]

triggerOp2 :: String ->
              (Stream Double -> Stream Double -> Stream Double) ->
              Stream Double ->
              Spec
triggerOp2 name op stream =
  trigger (name P.++ "Trigger") (testOp2 op stream) [arg stream]

testOp1 :: (Stream Double -> Stream Double) -> Stream Double -> Stream Bool
testOp1 op stream =
  -- NB: Use (>=) rather than (==) here, as floating-point equality gets weird
  -- due to NaNs.
  op stream >= op stream

testOp2 :: (Stream Double -> Stream Double -> Stream Double) -> Stream Double -> Stream Bool
testOp2 op stream =
  op stream stream >= op stream stream

main :: IO ()
main = do
  spec' <- reify spec
  verify mkDefaultCSettings [] "fpOps" spec'
