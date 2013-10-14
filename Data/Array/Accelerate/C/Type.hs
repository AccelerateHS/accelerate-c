{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE QuasiQuotes   #-}

-- |
-- Module      : Data.Array.Accelerate.C.Type
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module converts Accelerate types to C types. We are mapping elementary Haskell types to the C representations as
-- defined in the 'HsFFI.h' header provided by the standard Haskell FFI.
--

module Data.Array.Accelerate.C.Type (
  arrTypeToC, accTypeToC,
  tupleTypeToC, scalarTypeToC, numTypeToC, integralTypeToC, floatingTypeToC, nonNumTypeToC,
  sizeTupleType
) where

  -- libraries
import Language.C         as C
import Language.C.Quote.C as C
  
    -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Type


-- Convert an Accelerate array type to C
-- -------------------------------------

-- Determine the set of C types used to represent values of the given array type.
--
-- The (dummy) value will not be used. The implementation only depends on its type.
--
arrTypeToC :: forall sh e. (Shape sh, Elt e) => Array sh e -> [C.Type]
arrTypeToC _dummy
  = [cty| typename $id:("DIM" ++ show (dim (undefined::sh))) * |] :
    [ [cty| $ty:t * |] | t <- tupleTypeToC (eltType (undefined::e))]

-- Determine the set of C types used to represent values of the array type produced by the given array computation.
--
-- The (dummy) value will not be used. The implementation only depends on its type.
--
accTypeToC :: forall sh e aenv. (Shape sh, Elt e) => OpenAcc aenv (Array sh e) -> [C.Type]
accTypeToC _dummy = arrTypeToC (undefined::Array sh e)


-- Convert Accelerate to C types
-- -----------------------------

tupleTypeToC :: TupleType a -> [C.Type]
tupleTypeToC UnitTuple         = []
tupleTypeToC (SingleTuple  ty) = [scalarTypeToC ty]
tupleTypeToC (PairTuple t1 t0) = tupleTypeToC t1 ++ tupleTypeToC t0

scalarTypeToC :: ScalarType a -> C.Type
scalarTypeToC (NumScalarType    ty) = numTypeToC ty
scalarTypeToC (NonNumScalarType ty) = nonNumTypeToC ty

numTypeToC :: NumType a -> C.Type
numTypeToC (IntegralNumType ty) = integralTypeToC ty
numTypeToC (FloatingNumType ty) = floatingTypeToC ty

integralTypeToC :: IntegralType a -> C.Type
integralTypeToC (TypeInt8    _) = typename "HsInt8"
integralTypeToC (TypeInt16   _) = typename "HsInt16"
integralTypeToC (TypeInt32   _) = typename "HsInt32"
integralTypeToC (TypeInt64   _) = typename "HsInt64"
integralTypeToC (TypeWord8   _) = typename "HsWord8"
integralTypeToC (TypeWord16  _) = typename "HsWord16"
integralTypeToC (TypeWord32  _) = typename "HsWord32"
integralTypeToC (TypeWord64  _) = typename "HsWord64"
integralTypeToC (TypeCShort  _) = [cty|short|]
integralTypeToC (TypeCUShort _) = [cty|unsigned short|]
integralTypeToC (TypeCInt    _) = [cty|int|]
integralTypeToC (TypeCUInt   _) = [cty|unsigned int|]
integralTypeToC (TypeCLong   _) = [cty|long int|]
integralTypeToC (TypeCULong  _) = [cty|unsigned long int|]
integralTypeToC (TypeCLLong  _) = [cty|long long int|]
integralTypeToC (TypeCULLong _) = [cty|unsigned long long int|]
integralTypeToC (TypeInt     _) = typename "HsInt"
integralTypeToC (TypeWord    _) = typename "HsWord"

floatingTypeToC :: FloatingType a -> C.Type
floatingTypeToC (TypeFloat   _) = [cty|float|]
floatingTypeToC (TypeCFloat  _) = [cty|float|]
floatingTypeToC (TypeDouble  _) = [cty|double|]
floatingTypeToC (TypeCDouble _) = [cty|double|]

nonNumTypeToC :: NonNumType a -> C.Type
nonNumTypeToC (TypeBool   _) = typename "HsBool"
nonNumTypeToC (TypeChar   _) = typename "HsChar"
nonNumTypeToC (TypeCChar  _) = [cty|char|]
nonNumTypeToC (TypeCSChar _) = [cty|signed char|]
nonNumTypeToC (TypeCUChar _) = [cty|unsigned char|]


-- Tuples
-- ------

-- |Number of (flattened) components of a tuple type.
--
sizeTupleType :: TupleType a -> Int
sizeTupleType UnitTuple       = 0
sizeTupleType (SingleTuple _) = 1
sizeTupleType (PairTuple a b) = sizeTupleType a + sizeTupleType b


-- Auxilliary functions
-- --------------------

typename :: String -> C.Type
typename name = [cty| typename $id:name |]
