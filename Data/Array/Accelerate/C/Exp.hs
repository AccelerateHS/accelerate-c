{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Array.Accelerate.C.Exp
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the C code generation for scalar Accelerate expressions.
--

module Data.Array.Accelerate.C.Exp (
  expToC
) where

  -- standard libraries
import Data.Char  

  -- libraries
import Data.Loc
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Type

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Type


-- Generating C code from scalar Accelerate expressions
-- ----------------------------------------------------

-- Produces a list of expression whose length corresponds to the number of tuple components of the result type.
--
expToC :: forall t. Elt t => Exp () t -> [C.Exp]
-- Let bnd body            -> elet bnd body env
-- Var ix                  -> return $ prj ix env
expToC (PrimConst c) = [primConstToC c]
expToC (Const c)     = constToC (eltType (undefined::t)) c
-- PrimApp f arg           -> return . codegenPrim f <$> cvtE arg env
-- Tuple t                 -> cvtT t env
-- Prj i t                 -> prjT i t exp env
-- Cond p t e              -> cond p t e env
-- Iterate n f x           -> iterate n f x env
-- --        While p f x             -> while p f x env
-- 
-- -- Shapes and indices
-- IndexNil                -> return []
-- IndexAny                -> return []
-- IndexCons sh sz         -> (++) <$> cvtE sh env <*> cvtE sz env
-- IndexHead ix            -> return . last <$> cvtE ix env
-- IndexTail ix            ->          init <$> cvtE ix env
-- IndexSlice ix slix sh   -> indexSlice ix slix sh env
-- IndexFull  ix slix sl   -> indexFull  ix slix sl env
-- ToIndex sh ix           -> toIndex   sh ix env
-- FromIndex sh ix         -> fromIndex sh ix env
-- 
-- -- Arrays and indexing
-- Index acc ix            -> index acc ix env
-- LinearIndex acc ix      -> linearIndex acc ix env
-- Shape acc               -> shape acc env
-- ShapeSize sh            -> shapeSize sh env
-- Intersect sh1 sh2       -> intersect sh1 sh2 env
-- 
-- --Foreign function
-- Foreign ff _ e          -> foreignE ff e env


-- Constants and numeric types
-- ---------------------------
 
constToC :: TupleType a -> a -> [C.Exp]
constToC UnitTuple           _      = []
constToC (SingleTuple ty)    c      = [scalarToC ty c]
constToC (PairTuple ty1 ty0) (cs,c) = constToC ty1 cs ++ constToC ty0 c

scalarToC :: ScalarType a -> a -> C.Exp
scalarToC (NumScalarType    ty) = numScalarToC ty
scalarToC (NonNumScalarType ty) = nonNumScalarToC ty

numScalarToC :: NumType a -> a -> C.Exp
numScalarToC (IntegralNumType ty) = integralScalarToC ty
numScalarToC (FloatingNumType ty) = floatingScalarToC ty

integralScalarToC :: IntegralType a -> a -> C.Exp
integralScalarToC ty x | IntegralDict <- integralDict ty = [cexp| ( $ty:(integralTypeToC ty) ) $exp:(cintegral x) |]

floatingScalarToC :: FloatingType a -> a -> C.Exp
floatingScalarToC (TypeFloat   _) x = C.Const (C.FloatConst (shows x "f") (toRational x) noLoc) noLoc
floatingScalarToC (TypeCFloat  _) x = C.Const (C.FloatConst (shows x "f") (toRational x) noLoc) noLoc
floatingScalarToC (TypeDouble  _) x = C.Const (C.DoubleConst (show x) (toRational x) noLoc) noLoc
floatingScalarToC (TypeCDouble _) x = C.Const (C.DoubleConst (show x) (toRational x) noLoc) noLoc

nonNumScalarToC :: NonNumType a -> a -> C.Exp
nonNumScalarToC (TypeBool   _) x = cbool x
nonNumScalarToC (TypeChar   _) x = [cexp|$char:x|]
nonNumScalarToC (TypeCChar  _) x = [cexp|$char:(chr (fromIntegral x))|]
nonNumScalarToC (TypeCUChar _) x = [cexp|$char:(chr (fromIntegral x))|]
nonNumScalarToC (TypeCSChar _) x = [cexp|$char:(chr (fromIntegral x))|]

primConstToC :: PrimConst a -> C.Exp
primConstToC (PrimMinBound ty) = minBoundToC ty
primConstToC (PrimMaxBound ty) = maxBoundToC ty
primConstToC (PrimPi       ty) = piToC ty

piToC :: FloatingType a -> C.Exp
piToC ty | FloatingDict <- floatingDict ty = floatingScalarToC ty pi

minBoundToC :: BoundedType a -> C.Exp
minBoundToC (IntegralBoundedType ty) | IntegralDict <- integralDict ty = integralScalarToC ty minBound
minBoundToC (NonNumBoundedType   ty) | NonNumDict   <- nonNumDict   ty = nonNumScalarToC   ty minBound

maxBoundToC :: BoundedType a -> C.Exp
maxBoundToC (IntegralBoundedType ty) | IntegralDict <- integralDict ty = integralScalarToC ty maxBound
maxBoundToC (NonNumBoundedType   ty) | NonNumDict   <- nonNumDict   ty = nonNumScalarToC   ty maxBound
