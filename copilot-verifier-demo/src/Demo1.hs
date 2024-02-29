-- A simple example involving a stream of Fibonacci numbers.

{-# LANGUAGE RebindableSyntax #-}
module Demo1 (main) where

import qualified Prelude as P ()

import Language.Copilot
import Copilot.Compile.C99
import Copilot.Verifier

fibs :: Stream Word32
fibs = [1, 1] ++ (fibs + drop 1 fibs)

evenStream :: Stream Word32 -> Stream Bool
evenStream n = (n `mod` constant 2) == constant 0

oddStream :: Stream Word32 -> Stream Bool
oddStream n = not (evenStream n)

spec :: Spec
spec = do
  trigger "even" (evenStream fibs) [arg fibs]
  trigger "odd"  (oddStream fibs) [arg fibs]

main :: IO ()
main = do
  interpret 6 spec

  spec' <- reify spec
  -- compile "demo1" spec'
  verifyWithOptions defaultVerifierOptions{verbosity = Noisy} mkDefaultCSettings [] "demo1" spec'
