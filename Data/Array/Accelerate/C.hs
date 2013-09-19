{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Array.Accelerate.C
-- Copyright   : [2013] Manuel M T Chakravarty
-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the sequential C backend for the embedded array language /Accelerate/.
--

module Data.Array.Accelerate.C (
  runExpIO
) where

  -- standard libraries
import Control.Monad
import System.Exit    (ExitCode(..))
import System.Process (system)

  -- libraries
import Text.PrettyPrint.Mainland as C
import Language.C.Quote.C        as C

  -- accelerate
import Data.Array.Accelerate.Analysis.Type as Sugar
import Data.Array.Accelerate.Array.Sugar                (Elt(..))
import Data.Array.Accelerate.Smart                      (Exp)
import Data.Array.Accelerate.Trafo.Sharing              (convertExp)

  -- friends
import Data.Array.Accelerate.C.Type
import Data.Array.Accelerate.C.Exp


-- Execute a scalar Accelerate computation
-- ---------------------------------------

-- Compile an scalar Accelerate computation to C code, run it, and return the result.
--
runExpIO :: forall t. Elt t => Exp t -> IO t
runExpIO e
  = do
    { let e'    = convertExp True e
          ces   = expToC e'
          ctys  = tupleTypeToC (Sugar.expType e')
          cUnit = [cunit|
                    $ty:(head ctys) $id:cFunName ()
                    { 
                      return $exp:(head ces);
                    }
                  |]
    ; unless (length ces == 1) $
        error "Data.Array.Accelerate.C.runExpIO: result type may neither be unit nor a tuple"
    ; writeFile cFile $ 
        "#include \"HsFFI.h\"\n" ++
        "#include \"cbits/accelerate_c.h\"\n\n" ++
        (show . C.ppr $ cUnit)
    ; ec <- system $ unwords $ [cCompiler, "-c", cOpts, "-I" ++ ffiLibDir, "-o", oFile, cFile]
    ; case ec of
        ExitFailure c -> error $ "Data.Array.Accelerate.C: C compiler failed with exit code " ++ show c
        ExitSuccess   -> 
          do
          { error "FIXME: load and run code (this functionality will be provided)"
          } }


-- Constants
-- ---------

cFile :: FilePath
cFile = "accelerate.c"

oFile :: FilePath
oFile = "accelerate.o"

cFunName :: String
cFunName = "expfun"

cCompiler :: FilePath
cCompiler = "cc"

cOpts :: String
cOpts = "-O2"

-- IMPORTANT: check this path!
--
-- The default value is for the Haskell Platform with GHC 7.6.3 on OS X.
--
ffiLibDir :: FilePath
ffiLibDir = "/Library/Frameworks/GHC.framework/Versions/Current/usr/lib/ghc-7.6.3/include/"
