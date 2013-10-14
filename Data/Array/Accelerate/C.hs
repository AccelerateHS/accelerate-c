{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ForeignFunctionInterface #-}

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
  runExpIO, runIO
) where

  -- standard libraries
import Control.Applicative
import Control.Monad
import Foreign
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process   (system)

  -- libraries
import qualified 
       Text.PrettyPrint.Mainland as C
import Language.C.Quote.C        as C
import System.Posix.Temp

  -- accelerate
import Data.Array.Accelerate.Analysis.Type as Sugar
import Data.Array.Accelerate.Array.Sugar   as Sugar
import Data.Array.Accelerate.AST                        (Val(..))
import Data.Array.Accelerate.Smart                      (Exp, Acc)
import Data.Array.Accelerate.Trafo.Sharing              (convertExp, convertAcc)
import Data.Array.Accelerate.Type

  -- friends
import Data.Array.Accelerate.C.Acc
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Execute
import Data.Array.Accelerate.C.Exp
import Data.Array.Accelerate.C.Load
import Data.Array.Accelerate.C.Type


-- Execute a scalar Accelerate computation
-- ---------------------------------------

-- Compile an scalar Accelerate computation to C code, run it, and return the result.
--
runExpIO :: forall t. Elt t => Exp t -> IO t
runExpIO e
  = do
    { let e'    = convertExp True e
          ces   = expToC e'
          ctys  = tupleTypeToC $ expType e'
          resty = head ctys   -- we check for 'length ces == 1' further down
          cUnit = [cunit|
                    $edecls:cshapeDefs
                    $ty:resty * $id:cFunName ()
                    {
                      $ty:resty *result = malloc(sizeof($ty:resty));
                      *result = $exp:(head ces);
                      return result;
                    }
                  |]
    ; unless (length ces == 1) $
        error "Data.Array.Accelerate.C.runExpIO: result type may neither be unit nor a tuple"

    ; tmpPath <- addTrailingPathSeparator <$> getTemporaryDirectory >>= mkdtemp
    ; logMsgLn $ "Data.Array.Accelerate.C: temporary directory: " ++ tmpPath
    ; let cFilePath = tmpPath </> cFile
          oFilePath = tmpPath </> oFile
    ; writeFile cFilePath $ 
        "#include <stdlib.h>\n" ++
        "#include <math.h>\n" ++
        "#include \"HsFFI.h\"\n" ++
        (show . C.ppr $ cUnit)
    ; logMsg "Data.Array.Accelerate.C: runExpIO: compiling..."
    ; ec <- system $ unwords $ [cCompiler, "-c", cOpts, "-I" ++ ffiLibDir, "-o", oFilePath, cFilePath]
    ; case ec of
        ExitFailure c -> error $ "Data.Array.Accelerate.C: C compiler failed with exit code " ++ show c
        ExitSuccess   -> 
          do
          { logMsg "loading..."
          ; mFunPtr <- loadAndLookup oFilePath cFunName
          ; case mFunPtr of
              Nothing     -> error $ "Data.Array.Accelerate.C: unable to dynamically load generated code"
              Just funPtr -> 
                do
                { logMsg "running..."
                ; resultPtr <- mkExpFun funPtr
                ; logMsg "peeking..."
                ; result    <- toElt <$> peekSingleScalar (eltType (undefined::t)) resultPtr
                ; logMsg "unloading..."
                ; free resultPtr
                ; unload oFilePath
                ; logMsgLn "done"
                ; return result
                }
          } }
  where
    peekSingleScalar :: TupleType a -> Ptr a -> IO a
    peekSingleScalar (PairTuple UnitTuple (SingleTuple t)) ptr  = ((), ) <$> peekScalar t (castPtr ptr)
    peekSingleScalar _                                     _ptr = error "peekElt: impossible"
    
    peekScalar :: ScalarType a -> Ptr a -> IO a
    peekScalar (NumScalarType t)    ptr = peekNumScalar t ptr
    peekScalar (NonNumScalarType t) ptr = peekNonNumScalar t ptr
    
    peekNumScalar :: NumType a -> Ptr a -> IO a
    peekNumScalar (IntegralNumType t) ptr = peekIntegral t ptr
    peekNumScalar (FloatingNumType t) ptr = peekFloating t ptr
    
    peekIntegral :: IntegralType a -> Ptr a -> IO a
    peekIntegral TypeInt{}     ptr = peek ptr
    peekIntegral TypeInt8{}    ptr = peek ptr
    peekIntegral TypeInt16{}   ptr = peek ptr
    peekIntegral TypeInt32{}   ptr = peek ptr
    peekIntegral TypeInt64{}   ptr = peek ptr
    peekIntegral TypeWord{}    ptr = peek ptr
    peekIntegral TypeWord8{}   ptr = peek ptr
    peekIntegral TypeWord16{}  ptr = peek ptr
    peekIntegral TypeWord32{}  ptr = peek ptr
    peekIntegral TypeWord64{}  ptr = peek ptr
    peekIntegral TypeCShort{}  ptr = peek ptr
    peekIntegral TypeCUShort{} ptr = peek ptr
    peekIntegral TypeCInt{}    ptr = peek ptr
    peekIntegral TypeCUInt{}   ptr = peek ptr
    peekIntegral TypeCLong{}   ptr = peek ptr
    peekIntegral TypeCULong{}  ptr = peek ptr
    peekIntegral TypeCLLong{}  ptr = peek ptr
    peekIntegral TypeCULLong{} ptr = peek ptr
    
    peekFloating :: FloatingType a -> Ptr a -> IO a
    peekFloating TypeFloat{}   ptr = peek ptr
    peekFloating TypeDouble{}  ptr = peek ptr
    peekFloating TypeCFloat{}  ptr = peek ptr
    peekFloating TypeCDouble{} ptr = peek ptr
    
    peekNonNumScalar :: NonNumType a -> Ptr a -> IO a
    peekNonNumScalar TypeBool{}   ptr = peek ptr
    peekNonNumScalar TypeChar{}   ptr = peek ptr
    peekNonNumScalar TypeCChar{}  ptr = peek ptr
    peekNonNumScalar TypeCSChar{} ptr = peek ptr
    peekNonNumScalar TypeCUChar{} ptr = peek ptr


-- Execute an Accelerate array computation
-- ---------------------------------------

-- Compile an Accelerate array computation to C code, run it, and return the result.
--
runIO :: (Shape sh, Elt e) => Acc (Array sh e) -> IO (Array sh e)
runIO acc
  = do
    { let acc'     = convertAcc True True True acc
          cacc     = accToC EmptyEnv acc'
          cUnit    = [cunit|
                       $edecls:cshapeDefs
                       $edecl:cacc
                     |]
  
    ; tmpPath <- addTrailingPathSeparator <$> getTemporaryDirectory >>= mkdtemp
    ; logMsgLn $ "Data.Array.Accelerate.C: temporary directory: " ++ tmpPath
    ; let cFilePath = tmpPath </> cFile
          oFilePath = tmpPath </> oFile
    ; writeFile cFilePath $ 
        "#include <stdlib.h>\n" ++
        "#include <math.h>\n" ++
        "#include \"HsFFI.h\"\n" ++
        (show . C.ppr $ cUnit)
    ; logMsg "Data.Array.Accelerate.C: runExpIO: compiling..."
    ; ec <- system $ unwords $ [cCompiler, "-c", cOpts, "-I" ++ ffiLibDir, "-o", oFilePath, cFilePath]
    ; case ec of
        ExitFailure c -> error $ "Data.Array.Accelerate.C: C compiler failed with exit code " ++ show c
        ExitSuccess   ->
          do
          { logMsg "loading..."
          ; ok <- load oFilePath
          ; unless ok $
              error $ "Data.Array.Accelerate.C: unable to dynamically load generated code"
          ; logMsg "running..."
          ; result <- accExec Empty acc'
          ; logMsg "unloading..."
          ; unload oFilePath
          ; logMsgLn "done"
          ; return result
          } }


-- Constants
-- ---------

cFile :: FilePath
cFile = "accelerate.c"

oFile :: FilePath
oFile = "accelerate.o"

cCompiler :: FilePath
cCompiler = "cc"

cOpts :: String
-- cOpts = "-O2 -w"
cOpts = "-O2"

-- IMPORTANT: check this path!
--
-- The default value is for the Haskell Platform with GHC 7.6.3 on OS X.
--
ffiLibDir :: FilePath
ffiLibDir = "/Library/Frameworks/GHC.framework/Versions/Current/usr/lib/ghc-7.6.3/include/"


-- Tracing
-- -------

logMsg :: String -> IO ()
logMsg msg = hPutStr stderr msg >> hFlush stderr

logMsgLn :: String -> IO ()
logMsgLn = logMsg . (++ "\n")


-- Foreign imports
-- ---------------

foreign import ccall "dynamic"
  mkExpFun :: FunPtr (IO (Ptr a)) -> IO (Ptr a)
