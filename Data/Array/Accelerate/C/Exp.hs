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
import Data.Array.Accelerate.Array.Representation (SliceIndex(..))
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Pretty
import Data.Array.Accelerate.Tuple
import Data.Array.Accelerate.Type

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Type
import qualified Data.Array.Accelerate.Analysis.Type    as Sugar


-- Generating C code from scalar Accelerate expressions
-- ----------------------------------------------------

-- De Bruijn level to name variables.
--
type Level = Int

-- Produces a list of expression whose length corresponds to the number of tuple components of the result type.
--
expToC :: Elt t => Exp () t -> [C.Exp]
expToC = expToC' 0
  where
    expToC' :: forall t aenv env. Elt t => Level -> OpenExp aenv env t -> [C.Exp]
    expToC' lvl  (Let bnd body)  = elet lvl bnd body
    expToC' lvl  (Var idx)       = [ [cexp| $id:("x" ++ show (lvl - idxToInt idx - 1) ++ "_" ++ show i) |] 
                                   | i <- [0..sizeTupleType (eltType (undefined::t)) - 1]
                                   ]
    expToC' _lvl (PrimConst c)   = [primConstToC c]
    expToC' _lvl (Const c)       = constToC (eltType (undefined::t)) c
    expToC' lvl  (PrimApp f arg) = [primToC f $ expToC' lvl arg]
    expToC' lvl  (Tuple t)       = tupToC lvl t 
    expToC' lvl  e@(Prj i t)     = prjToC lvl i t e
    expToC' lvl  (Cond p t e)    = condToC lvl p t e
    -- Iterate n f x           -> iterate n f x env
    
    -- Shapes and indices
    expToC' _lvl IndexNil                = []
    expToC' _lvl IndexAny                = []
    expToC' lvl  (IndexCons sh sz)       = expToC' lvl sh ++ expToC' lvl sz
    expToC' lvl  (IndexHead ix)          = [last $ expToC' lvl ix]
    expToC' lvl  (IndexTail ix)          = init $ expToC' lvl ix
    expToC' lvl  (IndexSlice ix slix sh) = indexSlice ix (expToC' lvl slix) (expToC' lvl sh)
    expToC' lvl  (IndexFull  ix slix sl) = indexFull  ix (expToC' lvl slix) (expToC' lvl sl)
    expToC' lvl  (ToIndex sh ix)         = toIndexToC   (expToC' lvl sh) (expToC' lvl ix)
    expToC' lvl  (FromIndex sh ix)       = fromIndexToC (expToC' lvl sh) (expToC' lvl ix)
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

    -- Scalar let expressions evaluate their terms and generate new (const) variable bindings to store these results.
    -- Variable names are unambiguously based on the de Bruijn indices and the index of the tuple component they
    -- represent.
    --
    -- FIXME: Currently we need to push lets into each binding, as we don't have a statement sequence as the prelude
    --   to the list of expressions that this function returns.
    --
    elet :: (Elt t, Elt t') => Level -> OpenExp env aenv t -> OpenExp (env, t) aenv t' -> [C.Exp]
    elet lvl bnd body
      = map (\bodyiC -> [cexp| ({ $items:inits $exp:bodyiC; }) |]) (expToC' (lvl + 1) body)
      where
        name  = "x" ++ show lvl
        inits = zipWith3 bindOneComponent [0::Int ..] (expType bnd) (expToC' lvl bnd)
        
        bindOneComponent i tyiC bndiC = [citem| $ty:tyiC $id:(name ++ "_" ++ show i) = $exp:bndiC; |]

    -- Convert an open expression into a sequence of C expressions. We retain
    -- snoc-list ordering, so the element at tuple index zero is at the end of
    -- the list. Note that nested tuple structures are flattened.
    --
    tupToC :: Level -> Tuple (OpenExp env aenv) t -> [C.Exp]
    tupToC _lvl NilTup        = []
    tupToC lvl  (SnocTup t e) = tupToC lvl t ++ expToC' lvl e

    -- Project out a tuple index. Since the nested tuple structure is flattened,
    -- this actually corresponds to slicing out a subset of the list of C
    -- expressions, rather than picking out a single element.
    --
    prjToC :: Elt t 
           => Level
           -> TupleIdx (TupleRepr t) e
           -> OpenExp env aenv t
           -> OpenExp env aenv e
           -> [C.Exp]
    prjToC lvl ix t e =
      let subset = reverse
                 . take (length      $ expType e)
                 . drop (prjToInt ix $ Sugar.preExpType Sugar.accType t)
                 . reverse
      in
      subset $ expToC' lvl t

    -- Scalar conditionals. To keep the return type as an expression list we use
    -- the ternery C condition operator (?:). 
    --
    -- FIXME: For tuples this is not particularly good, so the least we can do is make sure the predicate
    -- result is evaluated only once and bind it to a local variable.
    --
    condToC :: Elt t 
            => Level
            -> OpenExp env anev Bool
            -> OpenExp env aenv t
            -> OpenExp env aenv t
            -> [C.Exp]
    condToC lvl p t e
      = zipWith (\tiC eiC -> [cexp| $exp:pC ? $exp:tiC : $exp:eiC |]) (expToC' lvl t) (expToC' lvl e)
      where
        [pC] = expToC' lvl p    -- type guarantees singleton
        

-- Tuples
-- ------

-- Convert a tuple index into the corresponding integer. Since the internal
-- representation is flat, be sure to walk over all sub components when indexing
-- past nested tuples.
--
prjToInt :: TupleIdx t e -> TupleType a -> Int
prjToInt ZeroTupIdx     _                 = 0
prjToInt (SuccTupIdx i) (b `PairTuple` a) = prjToInt i b + sizeTupleType a
prjToInt _              t                 = error $ "D.A.A.C.Exp.prjToInt: inconsistent tuple index: " ++ show t

sizeTupleType :: TupleType a -> Int
sizeTupleType UnitTuple       = 0
sizeTupleType (SingleTuple _) = 1
sizeTupleType (PairTuple a b) = sizeTupleType a + sizeTupleType b

-- Shapes and indices
-- ------------------

-- Restrict indices based on a slice specification. In the 'SliceAll' case we elide the 'IndexAny' from the head
-- of slx, as this is not represented by any C term (Any ~ []).
--
indexSlice :: SliceIndex slix' sl co sh' -> [C.Exp] -> [C.Exp] -> [C.Exp]
indexSlice sliceIdx slix sh =
  let restrict :: SliceIndex slix sl co sh -> [C.Exp] -> [C.Exp] -> [C.Exp]
      restrict SliceNil              _       _       = []
      restrict (SliceAll   sliceIdx) slx     (sz:sl) = sz : restrict sliceIdx slx sl
      restrict (SliceFixed sliceIdx) (_:slx) ( _:sl) =      restrict sliceIdx slx sl
      restrict _ _ _ = error "D.A.A.C.Exp.indexSlice: unexpected shapes"
  in
  reverse $ restrict sliceIdx (reverse slix) (reverse sh)

-- Extend indices based on a slice specification. In the SliceAll case we
-- elide the presence of Any from the head of slx.
--
indexFull :: SliceIndex slix' sl' co sh -> [C.Exp] -> [C.Exp] -> [C.Exp]
indexFull sliceIdx slix sl =
  let extend :: SliceIndex slix sl co sh -> [C.Exp] -> [C.Exp] -> [C.Exp]
      extend SliceNil              _        _       = []
      extend (SliceAll   sliceIdx) slx      (sz:sh) = sz : extend sliceIdx slx sh
      extend (SliceFixed sliceIdx) (sz:slx) sh      = sz : extend sliceIdx slx sh
      extend _ _ _ = error "D.A.A.C.Exp.indexFull: unexpected shapes"
  in
  reverse $ extend sliceIdx (reverse slix) (reverse sl)

-- Convert between linear and multidimensional indices.
--
toIndexToC :: [C.Exp] -> [C.Exp] -> [C.Exp]
toIndexToC sh ix = [ccall "toIndex" [ccall "shape" sh, ccall "shape" ix]]

-- For the multidimensional case, we've inlined the definition of 'fromIndex' because we need to return an expression
-- for each component.
--
fromIndexToC :: [C.Exp] -> [C.Exp] -> [C.Exp]
fromIndexToC sh ix
  = reverse $ fromIndex' (reverse sh) (head ix)     -- types ensure that 'ix' is a singleton
  where
    fromIndex' :: [C.Exp] -> C.Exp -> [C.Exp]
    fromIndex' []     _ = []
    fromIndex' [_]    i = [i]
    fromIndex' (d:ds) i = [cexp| $exp:i % $exp:d |] : fromIndex' ds [cexp| $exp:i / $exp:d |]


-- Primtive functions
-- ------------------

primToC :: PrimFun p -> [C.Exp] -> C.Exp
primToC (PrimAdd              _) [a,b] = [cexp|$exp:a + $exp:b|]
primToC (PrimSub              _) [a,b] = [cexp|$exp:a - $exp:b|]
primToC (PrimMul              _) [a,b] = [cexp|$exp:a * $exp:b|]
primToC (PrimNeg              _) [a]   = [cexp| - $exp:a|]
primToC (PrimAbs             ty) [a]   = absToC ty a
primToC (PrimSig             ty) [a]   = sigToC ty a
primToC (PrimQuot             _) [a,b] = [cexp|$exp:a / $exp:b|]
primToC (PrimRem              _) [a,b] = [cexp|$exp:a % $exp:b|]
primToC (PrimIDiv            ty) [a,b] = ccall "idiv" [ccast (NumScalarType $ IntegralNumType ty) a,
                                                       ccast (NumScalarType $ IntegralNumType ty) b]
primToC (PrimMod             ty) [a,b] = ccall "mod"  [ccast (NumScalarType $ IntegralNumType ty) a,
                                                       ccast (NumScalarType $ IntegralNumType ty) b]
primToC (PrimBAnd             _) [a,b] = [cexp|$exp:a & $exp:b|]
primToC (PrimBOr              _) [a,b] = [cexp|$exp:a | $exp:b|]
primToC (PrimBXor             _) [a,b] = [cexp|$exp:a ^ $exp:b|]
primToC (PrimBNot             _) [a]   = [cexp|~ $exp:a|]
primToC (PrimBShiftL          _) [a,b] = [cexp|$exp:a << $exp:b|]
primToC (PrimBShiftR          _) [a,b] = [cexp|$exp:a >> $exp:b|]
primToC (PrimBRotateL         _) [a,b] = ccall "rotateL" [a,b]
primToC (PrimBRotateR         _) [a,b] = ccall "rotateR" [a,b]
primToC (PrimFDiv             _) [a,b] = [cexp|$exp:a / $exp:b|]
primToC (PrimRecip           ty) [a]   = recipToC ty a
primToC (PrimSin             ty) [a]   = ccall (FloatingNumType ty `postfix` "sin")   [a]
primToC (PrimCos             ty) [a]   = ccall (FloatingNumType ty `postfix` "cos")   [a]
primToC (PrimTan             ty) [a]   = ccall (FloatingNumType ty `postfix` "tan")   [a]
primToC (PrimAsin            ty) [a]   = ccall (FloatingNumType ty `postfix` "asin")  [a]
primToC (PrimAcos            ty) [a]   = ccall (FloatingNumType ty `postfix` "acos")  [a]
primToC (PrimAtan            ty) [a]   = ccall (FloatingNumType ty `postfix` "atan")  [a]
primToC (PrimAsinh           ty) [a]   = ccall (FloatingNumType ty `postfix` "asinh") [a]
primToC (PrimAcosh           ty) [a]   = ccall (FloatingNumType ty `postfix` "acosh") [a]
primToC (PrimAtanh           ty) [a]   = ccall (FloatingNumType ty `postfix` "atanh") [a]
primToC (PrimExpFloating     ty) [a]   = ccall (FloatingNumType ty `postfix` "exp")   [a]
primToC (PrimSqrt            ty) [a]   = ccall (FloatingNumType ty `postfix` "sqrt")  [a]
primToC (PrimLog             ty) [a]   = ccall (FloatingNumType ty `postfix` "log")   [a]
primToC (PrimFPow            ty) [a,b] = ccall (FloatingNumType ty `postfix` "pow")   [a,b]
primToC (PrimLogBase         ty) [a,b] = logBaseToC ty a b
primToC (PrimTruncate     ta tb) [a]   = truncateToC ta tb a
primToC (PrimRound        ta tb) [a]   = roundToC ta tb a
primToC (PrimFloor        ta tb) [a]   = floorToC ta tb a
primToC (PrimCeiling      ta tb) [a]   = ceilingToC ta tb a
primToC (PrimAtan2           ty) [a,b] = ccall (FloatingNumType ty `postfix` "atan2") [a,b]
primToC (PrimLt               _) [a,b] = [cexp|$exp:a < $exp:b|]
primToC (PrimGt               _) [a,b] = [cexp|$exp:a > $exp:b|]
primToC (PrimLtEq             _) [a,b] = [cexp|$exp:a <= $exp:b|]
primToC (PrimGtEq             _) [a,b] = [cexp|$exp:a >= $exp:b|]
primToC (PrimEq               _) [a,b] = [cexp|$exp:a == $exp:b|]
primToC (PrimNEq              _) [a,b] = [cexp|$exp:a != $exp:b|]
primToC (PrimMax             ty) [a,b] = maxToC ty a b
primToC (PrimMin             ty) [a,b] = minToC ty a b
primToC PrimLAnd                 [a,b] = [cexp|$exp:a && $exp:b|]
primToC PrimLOr                  [a,b] = [cexp|$exp:a || $exp:b|]
primToC PrimLNot                 [a]   = [cexp| ! $exp:a|]
primToC PrimOrd                  [a]   = ordToC a
primToC PrimChr                  [a]   = chrToC a
primToC PrimBoolToInt            [a]   = boolToIntToC a
primToC (PrimFromIntegral ta tb) [a]   = fromIntegralToC ta tb a
primToC p args = -- If the argument lists are not the correct length
  error $ 
    "D.A.A.C.Exp.primToC: inconsistent argument count: '" ++ (show . snd . prettyPrim $ p) ++ "' with " ++ 
    show (length args) ++ " argument(s)"


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


-- Methods from Num, Floating, Fractional and RealFrac
-- ---------------------------------------------------

absToC :: NumType a -> C.Exp -> C.Exp
absToC (FloatingNumType ty) x = ccall (FloatingNumType ty `postfix` "fabs") [x]
absToC (IntegralNumType ty) x =
  case ty of
    TypeWord _          -> x
    TypeWord8 _         -> x
    TypeWord16 _        -> x
    TypeWord32 _        -> x
    TypeWord64 _        -> x
    TypeCUShort _       -> x
    TypeCUInt _         -> x
    TypeCULong _        -> x
    TypeCULLong _       -> x
    _                   -> ccall "abs" [x]

sigToC :: NumType a -> C.Exp -> C.Exp
sigToC (IntegralNumType ty) = integralSigToC ty
sigToC (FloatingNumType ty) = floatingSigToC ty

integralSigToC :: IntegralType a -> C.Exp -> C.Exp
integralSigToC ty x = [cexp|$exp:x == $exp:zero ? $exp:zero : $exp:(ccall "copysign" [one,x]) |]
  where
    zero | IntegralDict <- integralDict ty = integralScalarToC ty 0
    one  | IntegralDict <- integralDict ty = integralScalarToC ty 1

floatingSigToC :: FloatingType a -> C.Exp -> C.Exp
floatingSigToC ty x = [cexp|$exp:x == $exp:zero ? $exp:zero : $exp:(ccall (FloatingNumType ty `postfix` "copysign") [one,x]) |]
  where
    zero | FloatingDict <- floatingDict ty = floatingScalarToC ty 0
    one  | FloatingDict <- floatingDict ty = floatingScalarToC ty 1


recipToC :: FloatingType a -> C.Exp -> C.Exp
recipToC ty x | FloatingDict <- floatingDict ty = [cexp|$exp:(floatingScalarToC ty 1) / $exp:x|]


logBaseToC :: FloatingType a -> C.Exp -> C.Exp -> C.Exp
logBaseToC ty x y = let a = ccall (FloatingNumType ty `postfix` "log") [x]
                        b = ccall (FloatingNumType ty `postfix` "log") [y]
                        in
                        [cexp|$exp:b / $exp:a|]


minToC :: ScalarType a -> C.Exp -> C.Exp -> C.Exp
minToC (NumScalarType ty@(IntegralNumType _)) a b = ccall (ty `postfix` "min")  [a,b]
minToC (NumScalarType ty@(FloatingNumType _)) a b = ccall (ty `postfix` "fmin") [a,b]
minToC (NonNumScalarType _)                   a b =
  let ty = scalarType :: ScalarType Int32
  in  minToC ty (ccast ty a) (ccast ty b)


maxToC :: ScalarType a -> C.Exp -> C.Exp -> C.Exp
maxToC (NumScalarType ty@(IntegralNumType _)) a b = ccall (ty `postfix` "max")  [a,b]
maxToC (NumScalarType ty@(FloatingNumType _)) a b = ccall (ty `postfix` "fmax") [a,b]
maxToC (NonNumScalarType _)                   a b =
  let ty = scalarType :: ScalarType Int32
  in  maxToC ty (ccast ty a) (ccast ty b)


-- Type coercions
--
ordToC :: C.Exp -> C.Exp
ordToC = ccast (scalarType :: ScalarType Int)

chrToC :: C.Exp -> C.Exp
chrToC = ccast (scalarType :: ScalarType Char)

boolToIntToC :: C.Exp -> C.Exp
boolToIntToC = ccast (scalarType :: ScalarType Int)

fromIntegralToC :: IntegralType a -> NumType b -> C.Exp -> C.Exp
fromIntegralToC _ ty = ccast (NumScalarType ty)

truncateToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
truncateToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "trunc") [x]

roundToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
roundToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "round") [x]

floorToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
floorToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "floor") [x]

ceilingToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
ceilingToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "ceil") [x]


-- Auxiliary Functions
-- -------------------

ccast :: ScalarType a -> C.Exp -> C.Exp
ccast ty x = [cexp|($ty:(scalarTypeToC ty)) $exp:x|]

postfix :: NumType a -> String -> String
postfix (FloatingNumType (TypeFloat  _)) x = x ++ "f"
postfix (FloatingNumType (TypeCFloat _)) x = x ++ "f"
postfix _                                x = x
