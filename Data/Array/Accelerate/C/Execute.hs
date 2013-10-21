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
  accExec, ValArrs(..)
) where

  -- standard libraries
import Foreign as Foreign

  -- accelerate
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Load as Load


-- Execute an array computation
-- ----------------------------

-- Valuation for an environment of array tuples.
--
data ValArrs aenv where
  EmptyArrs :: ValArrs ()
  PushArrs  :: Arrays arrs
            => ValArrs aenv -> arrs -> ValArrs (aenv, arrs)

prjValArrs :: Arrays arrs => Idx aenv arrs -> ValArrs aenv -> arrs
prjValArrs ZeroIdx      (PushArrs _    arrs) = arrs
prjValArrs (SuccIdx ix) (PushArrs aenv _)    = prjValArrs ix aenv
prjValArrs _            _                    = error "D.A.A.C.Execute: inconsistent valuation"

-- Execute the generated C code while evaluating an array computation.
--
-- FIXME: At the moment, only one actual array computation is possible. (There may be additional 'use' and 'let'
--        constructs, though.)
--
accExec :: Arrays arrs => ValArrs aenv -> OpenAcc aenv arrs -> IO arrs

accExec aenv (OpenAcc (Alet bnd body))
  = do
    { arrs <- accExec aenv bnd
    ; accExec (aenv `PushArrs` arrs) body
    }

accExec aenv (OpenAcc (Avar idx)) = return $ prjValArrs idx aenv

accExec _aenv (OpenAcc (Use arr)) = return $ toArr arr

accExec aenv acc@(OpenAcc (Map f a))
  = do
    { argArr    <- accExec aenv a
    ; resultArr <- allocateArrayIO (shape argArr)     -- the result shape of a map is that of the argument array
    ; let aenvWithArg = aenv `PushArrs` argArr
    ; invokeAccWithArrs cFunName resultArr aenvWithArg
    ; return resultArr
    }

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


-- Foreign code invocation
-- -----------------------

data PtrList = NilPL
             | forall e. 
               (:::) (Ptr e) PtrList
infixr 5 :::

(+++) :: PtrList -> PtrList -> PtrList
NilPL    +++ ys = ys
(x:::xs) +++ ys = x ::: (xs +++ ys)

-- Invoke an external array computation with result arrays and an array environment.
--
invokeAccWithArrs :: Name -> Array sh e -> ValArrs aenv -> IO ()
invokeAccWithArrs cName resultArr aenv
  = do
    { (resultShPtr, resultPtrs) <- arrToPtrList resultArr
    ; (aenvShPtrs , aenvPtrs)   <- aenvToPtrList aenv
    ; invokeAcc cName (resultPtrs +++ aenvPtrs)

        -- Array pointers are kept alive via the valuation
    ; aenv `seq` return ()
    ; mapM_ free $ resultShPtr:aenvShPtrs
    }
  where
    arrToPtrList :: forall sh e. Array sh e -> IO (Ptr Word64, PtrList)
    arrToPtrList (Array shRepr arrData)
      = do
        { let sh = toElt shRepr :: sh
        ; shArr <- Foreign.newArray . map fromIntegral . shapeToList $ sh :: IO (Ptr Word64)   
                                                              -- 'Word64' matches def of 'Ix' in 'C.A.A.C.Base.cshapeDefs'
        ; return (shArr, shArr ::: (wrapTupleList (arrayElt :: ArrayEltR (EltRepr e)) . ptrsOfArrayData $ arrData))
        }

    arrsToPtrList :: Arrays arrs => arrs -> IO ([Ptr Word64], PtrList)
    arrsToPtrList arrs = concArrTuples (arrays arrs) . fromArr $ arrs
      where
        concArrTuples :: ArraysR arrs -> arrs -> IO ([Ptr Word64], PtrList)
        concArrTuples ArraysRunit  ()  = return ([], NilPL)
        concArrTuples ArraysRarray arr       
          = do 
            { (shPtr, arrPtrs) <- arrToPtrList arr 
            ; return ([shPtr], arrPtrs)
            }
        concArrTuples (ArraysRpair r1 r2) (tl1, tl2)
          = do
            { (shPtrs1, arrPtrs1) <- concArrTuples r1 tl1
            ; (shPtrs2, arrPtrs2) <- concArrTuples r2 tl2
            ; return (shPtrs1 ++ shPtrs2, arrPtrs1 +++ arrPtrs2)
            }
   
    aenvToPtrList :: ValArrs aenv -> IO ([Ptr Word64], PtrList)
    aenvToPtrList EmptyArrs              = return ([], NilPL)
    aenvToPtrList (aenv `PushArrs` arrs)
      = do
        { (arrsShPtrs, arrsPtrs) <- arrsToPtrList arrs
        ; (aenvShPtrs, aenvPtrs) <- aenvToPtrList aenv
        ; return (arrsShPtrs ++ aenvShPtrs, arrsPtrs +++ aenvPtrs)
        }
    
    wrapTupleList :: ArrayEltR e -> ArrayPtrs e -> PtrList
    wrapTupleList ArrayEltRunit         ()       = NilPL
    wrapTupleList (ArrayEltRpair r1 r2) (p1, p2) = wrapTupleList r1 p1 +++ wrapTupleList r2 p2
    wrapTupleList ArrayEltRint          p        = p ::: NilPL
    wrapTupleList ArrayEltRint8         p        = p ::: NilPL
    wrapTupleList ArrayEltRint16        p        = p ::: NilPL
    wrapTupleList ArrayEltRint32        p        = p ::: NilPL
    wrapTupleList ArrayEltRint64        p        = p ::: NilPL
    wrapTupleList ArrayEltRword         p        = p ::: NilPL
    wrapTupleList ArrayEltRword8        p        = p ::: NilPL
    wrapTupleList ArrayEltRword16       p        = p ::: NilPL
    wrapTupleList ArrayEltRword32       p        = p ::: NilPL
    wrapTupleList ArrayEltRword64       p        = p ::: NilPL
    wrapTupleList ArrayEltRcshort       p        = p ::: NilPL
    wrapTupleList ArrayEltRcushort      p        = p ::: NilPL
    wrapTupleList ArrayEltRcint         p        = p ::: NilPL
    wrapTupleList ArrayEltRcuint        p        = p ::: NilPL
    wrapTupleList ArrayEltRclong        p        = p ::: NilPL
    wrapTupleList ArrayEltRculong       p        = p ::: NilPL
    wrapTupleList ArrayEltRcllong       p        = p ::: NilPL
    wrapTupleList ArrayEltRcullong      p        = p ::: NilPL
    wrapTupleList ArrayEltRfloat        p        = p ::: NilPL
    wrapTupleList ArrayEltRdouble       p        = p ::: NilPL
    wrapTupleList ArrayEltRcfloat       p        = p ::: NilPL
    wrapTupleList ArrayEltRcdouble      p        = p ::: NilPL
    wrapTupleList ArrayEltRbool         p        = p ::: NilPL
    wrapTupleList ArrayEltRchar         p        = p ::: NilPL
    wrapTupleList ArrayEltRcchar        p        = p ::: NilPL
    wrapTupleList ArrayEltRcschar       p        = p ::: NilPL
    wrapTupleList ArrayEltRcuchar       p        = p ::: NilPL

-- Invoke an external array computation with a variable number of pointer arguments.
--
invokeAcc cName NilPL = return ()
invokeAcc cName (ptr1 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc1Fun f ptr1
invokeAcc cName (ptr1 ::: ptr2 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc2Fun f ptr1 ptr2
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc3Fun f ptr1 ptr2 ptr3
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: ptr4 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc4Fun f ptr1 ptr2 ptr3 ptr4
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: ptr4 ::: ptr5 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc5Fun f ptr1 ptr2 ptr3 ptr4 ptr5
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: ptr4 ::: ptr5 ::: ptr6 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc6Fun f ptr1 ptr2 ptr3 ptr4 ptr5 ptr6
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: ptr4 ::: ptr5 ::: ptr6 ::: ptr7 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc7Fun f ptr1 ptr2 ptr3 ptr4 ptr5 ptr6 ptr7
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: ptr4 ::: ptr5 ::: ptr6 ::: ptr7 ::: ptr8 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc8Fun f ptr1 ptr2 ptr3 ptr4 ptr5 ptr6 ptr7 ptr8
invokeAcc cName (ptr1 ::: ptr2 ::: ptr3 ::: ptr4 ::: ptr5 ::: ptr6 ::: ptr7 ::: ptr8 ::: ptr9 ::: NilPL)
  = lookupName cName >>= \f -> mkAcc9Fun f ptr1 ptr2 ptr3 ptr4 ptr5 ptr6 ptr7 ptr8 ptr9

-- Obtain the symbol without commiting to a particular type yet.
--
lookupName :: Name -> IO (FunPtr a)
lookupName cName
  = do
    { mFunPtr <- Load.lookup cFunName
    ; case mFunPtr of
        Nothing     -> error "Data.Array.Accelerate.C: unable to dynamically load generated code (lookup)"
        Just funPtr -> return funPtr
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
