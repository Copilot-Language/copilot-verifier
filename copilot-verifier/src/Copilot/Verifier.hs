{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ImplicitParams #-}

module Copilot.Verifier where

import Control.Monad (foldM)

import Copilot.Compile.C99 (CSettings(..), compileWith)
import Copilot.Core

-- import qualified Copilot.Theorem.What4 as CW4

import Crux.LLVM.Config (llvmCruxConfig)
import Crux.LLVM.Compile (genBitCode)
import CruxLLVMMain
  (withCruxLLVMLogging, cruxLLVMLoggingToSayWhat, processLLVMOptions)

import Crux.Config (cfgJoin, Config(..))
import Crux.Config.Load (fromFile, fromEnv)
import Crux.Config.Common (cruxOptions, CruxOptions(..), postprocessOptions, )
import Crux (defaultOutputConfig)
import Crux.Log (cruxLogMessageToSayWhat, withCruxLogMessage)

verify :: CSettings -> String -> Spec -> IO ()
verify csettings prefix spec =
  do compileWith csettings prefix spec
     putStrLn ("Generated " ++ prefix)

     let csrc = prefix ++ ".c"

     llvmcfg <- llvmCruxConfig
     let cfg = cfgJoin cruxOptions llvmcfg

     (cruxOpts, llvmOpts) <-
       do -- TODO, load from and actual configuration file
          fileOpts <- fromFile "copilot-verifier" cfg Nothing
          (cruxOpts0, llvmOpts0) <- foldM fromEnv fileOpts (cfgEnv cfg)
          let ?outputConfig = defaultOutputConfig cruxLogMessageToSayWhat (Just cruxOpts0)
          cruxOpts1 <- withCruxLogMessage (postprocessOptions cruxOpts0{ inputFiles = [csrc] })
          processLLVMOptions (cruxOpts1, llvmOpts0)


     let ?outputConfig = defaultOutputConfig cruxLLVMLoggingToSayWhat (Just cruxOpts)
     bcOut <- withCruxLLVMLogging (genBitCode cruxOpts llvmOpts)

     putStrLn ("Compiled " ++ prefix ++ " into " ++ bcOut)
