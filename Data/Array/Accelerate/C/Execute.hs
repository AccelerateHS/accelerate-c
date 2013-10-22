{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE BangPatterns #-}
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
import Control.Applicative hiding (Const)
import Control.Monad
import Foreign as Foreign

  -- accelerate
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Interpreter          (evalPrim, evalPrimConst, evalPrj)
import Data.Array.Accelerate.Array.Representation (SliceIndex(..))
import Data.Array.Accelerate.Tuple

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

accExec aenv (OpenAcc (Generate sh _f))
  = do
    { sh <- executeExp sh aenv
    ; resultArr <- allocateArrayIO sh
    ; invokeAccWithArrs cFunName resultArr aenv
    ; return resultArr
    }

accExec aenv (OpenAcc (Map _f a))
  = do
    { argArr    <- accExec aenv a
    ; resultArr <- allocateArrayIO (shape argArr)     -- the result shape of a map is that of the argument array
    ; let aenvWithArg = aenv `PushArrs` argArr
    ; invokeAccWithArrs cFunName resultArr aenvWithArg
    ; return resultArr
    }

accExec aenv (OpenAcc (ZipWith _f a1 a2))
  = do
    { arg1Arr   <- accExec aenv a1
    ; arg2Arr   <- accExec aenv a2
    ; resultArr <- allocateArrayIO (shape arg1Arr
                                    `intersect`
                                    shape arg2Arr)  -- the result shape of a zipWith is the intersection of the argument shapes
    ; let aenvWithArg = aenv `PushArrs` arg1Arr `PushArrs` arg2Arr
    ; invokeAccWithArrs cFunName resultArr aenvWithArg
    ; return resultArr
    }

accExec _ _ = error "D.A.A.C.Execute: unimplemented"


-- Scalar expression evaluation
-- ----------------------------

-- Evaluate a scalar expression.
--
--FIXME: This could as well be pure. (Except if we want to implement Foreign properly.)
executeExp :: Exp aenv t -> ValArrs aenv -> IO t
executeExp !exp !aenv = executeOpenExp exp Empty aenv

executeOpenExp :: forall env aenv exp. OpenExp env aenv exp -> Val env -> ValArrs aenv -> IO exp
executeOpenExp !rootExp !env !aenv = travE rootExp
  where
    travE :: OpenExp env aenv t -> IO t
    travE exp = case exp of
      Var ix                    -> return (prj ix env)
      Let bnd body              -> travE bnd >>= \x -> executeOpenExp body (env `Push` x) aenv
      Const c                   -> return (toElt c)
      PrimConst c               -> return (evalPrimConst c)
      PrimApp f x               -> evalPrim f <$> travE x
      Tuple t                   -> toTuple <$> travT t
      Prj ix e                  -> evalPrj ix . fromTuple <$> travE e
      Cond p t e                -> travE p >>= \x -> if x then travE t else travE e
      Iterate n f x             -> join $ iterate f <$> travE n <*> travE x
      IndexAny                  -> return Any
      IndexNil                  -> return Z
      IndexCons sh sz           -> (:.) <$> travE sh <*> travE sz
      IndexHead sh              -> (\(_  :. ix) -> ix) <$> travE sh
      IndexTail sh              -> (\(ix :.  _) -> ix) <$> travE sh
      IndexSlice ix slix sh     -> indexSlice ix <$> travE slix <*> travE sh
      IndexFull ix slix sl      -> indexFull  ix <$> travE slix <*> travE sl
      ToIndex sh ix             -> toIndex   <$> travE sh  <*> travE ix
      FromIndex sh ix           -> fromIndex <$> travE sh  <*> travE ix
      Intersect sh1 sh2         -> intersect <$> travE sh1 <*> travE sh2
      ShapeSize sh              -> size  <$> travE sh
      Shape acc                 -> shape <$> travA acc
      Index acc ix              -> (!) <$> travA acc <*> travE ix
      LinearIndex acc ix        -> join $ indexArray <$> travA acc <*> travE ix
      Foreign _ f x             -> travF1 f x

    -- Helpers
    -- -------

    travT :: Tuple (OpenExp env aenv) t -> IO t
    travT tup = case tup of
      NilTup            -> return ()
      SnocTup !t !e     -> (,) <$> travT t <*> travE e

    travA :: Arrays a => OpenAcc aenv a -> IO a
    travA !acc = accExec aenv acc

    travF1 :: Fun () (a -> b) -> OpenExp env aenv a -> IO b
    travF1 (Lam (Body f)) x = travE x >>= \a -> executeOpenExp f (Empty `Push` a) EmptyArrs
    travF1 _              _ = error "I bless the rains down in Africa"

    iterate :: OpenExp (env, a) aenv a -> Int -> a -> IO a
    iterate !f !limit !x
      = let go !i !acc
              | i >= limit      = return acc
              | otherwise       = go (i+1) =<< executeOpenExp f (env `Push` acc) aenv
        in
        go 0 x

    indexSlice :: (Elt slix, Elt sh, Elt sl)
               => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
               -> slix
               -> sh
               -> sl
    indexSlice !ix !slix !sh = toElt $! restrict ix (fromElt slix) (fromElt sh)
      where
        restrict :: SliceIndex slix sl co sh -> slix -> sh -> sl
        restrict SliceNil              ()        ()       = ()
        restrict (SliceAll   sliceIdx) (slx, ()) (sl, sz) = (restrict sliceIdx slx sl, sz)
        restrict (SliceFixed sliceIdx) (slx,  _) (sl,  _) = restrict sliceIdx slx sl

    indexFull :: (Elt slix, Elt sh, Elt sl)
              => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
              -> slix
              -> sl
              -> sh
    indexFull !ix !slix !sl = toElt $! extend ix (fromElt slix) (fromElt sl)
      where
        extend :: SliceIndex slix sl co sh -> slix -> sl -> sh
        extend SliceNil              ()        ()       = ()
        extend (SliceAll sliceIdx)   (slx, ()) (sh, sz) = (extend sliceIdx slx sh, sz)
        extend (SliceFixed sliceIdx) (slx, sz) sh       = (extend sliceIdx slx sh, sz)

    indexArray :: (Shape sh, Elt e) => Array sh e -> Int -> IO e
    indexArray arr ix = return $ arr ! (fromIndex (shape arr) ix)


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
invokeAcc :: String -> PtrList -> IO ()
invokeAcc _cName NilPL = return ()
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
invokeAcc _ _ = error "D.A.A.C.Execute.invokeAcc: too many arguments"

-- Obtain the symbol without commiting to a particular type yet.
--
lookupName :: Name -> IO (FunPtr a)
lookupName cName
  = do
    { mFunPtr <- Load.lookup cName
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
