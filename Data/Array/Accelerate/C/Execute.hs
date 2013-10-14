{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ForeignFunctionInterface #-}

-- |
-- Module      : Data.Array.Accelerate.C.Execute
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the C code execution for Accelerate array computations.
--

module Data.Array.Accelerate.C.Execute (
  accExec
) where

  -- standard libraries
import Foreign

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Load as Load


-- Execute an array computation
-- ----------------------------

-- Execute the generated C code while evaluating an array computation.
--
-- FIXME: At the moment, only one actual array computation is possible. (There may be additional 'use' and 'let'
--        constructs, though.)
--
accExec :: Arrays arrs => Val aenv -> OpenAcc aenv arrs -> IO arrs

accExec aenv (OpenAcc (Alet bnd body))
  = do
    { arrs <- accExec aenv bnd
    ; accExec (aenv `Push` arrs) body
    }

accExec _aenv (OpenAcc (Use arr)) = return $ toArr arr

accExec aenv acc@(OpenAcc (Map f a))
  = do
    { mFunPtr <- Load.lookup cFunName
    ; case mFunPtr of
        Nothing     -> error "Data.Array.Accelerate.C: unable to dynamically load generated code (lookup)"
        Just funPtr -> 
          do
          { argArr    <- accExec aenv a
          ; resultArr <- allocateArrayIO (shape argArr)     -- the result shape of a map is that of the argument array
            -- ADD: arrays out of 'aenv'
          ; error "Data.Array.Accelerate.C: array code execution is MISSING"
          ; return resultArr
          } }

accExec _ _ = error "D.A.A.C.Execute: unimplemented"


-- Stateful array operations
-- -------------------------

-- This is a dodgy hack!
--
allocateArrayIO :: (Shape sh, Elt e) => sh -> IO (Array sh e)
allocateArrayIO sh 
  = do
    { let arr = allocateArray sh
    ; arr `seq` return arr
    }


-- Foreign imports
-- ---------------

foreign import ccall "dynamic"
  mkAcc1Fun :: FunPtr (Ptr a1 -> IO ()) -> Ptr a1 -> IO ()

foreign import ccall "dynamic"
  mkAcc2Fun :: FunPtr (Ptr a1 -> Ptr a2 -> IO ()) -> Ptr a1 -> Ptr a2 -> IO ()

foreign import ccall "dynamic"
  mkAcc3Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> IO ()) -> Ptr a1 -> Ptr a2 -> Ptr a3 -> IO ()

foreign import ccall "dynamic"
  mkAcc4Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> IO ()) 
            -> Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> IO ()

foreign import ccall "dynamic"
  mkAcc5Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> IO ()) 
            -> Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> IO ()

foreign import ccall "dynamic"
  mkAcc6Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> IO ()) 
            -> Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> IO ()

foreign import ccall "dynamic"
  mkAcc7Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> Ptr a7 -> IO ()) 
            -> Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> Ptr a7 -> IO ()

foreign import ccall "dynamic"
  mkAcc8Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> Ptr a7 -> Ptr a8 -> IO ()) 
            -> Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> Ptr a7 -> Ptr a8 -> IO ()

foreign import ccall "dynamic"
  mkAcc9Fun :: FunPtr (Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> Ptr a7 -> Ptr a8 -> Ptr a9 -> IO ()) 
            -> Ptr a1 -> Ptr a2 -> Ptr a3 -> Ptr a4 -> Ptr a5 -> Ptr a6 -> Ptr a7 -> Ptr a8 -> Ptr a9 -> IO ()
