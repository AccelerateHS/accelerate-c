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
  expToC, openExpToC, fun1ToC, fun2ToC
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
import Data.Array.Accelerate.AST                  hiding (Val(..), prj)
import Data.Array.Accelerate.Pretty
import Data.Array.Accelerate.Tuple
import Data.Array.Accelerate.Type

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Type
import Data.Array.Accelerate.Analysis.Type


-- Generating C code from scalar Accelerate expressions
-- ----------------------------------------------------

-- Compile a closed embedded scalar expression into a list of C expression whose length corresponds to the number of tuple
-- components of the embedded type.
--
expToC :: Elt t => Exp () t -> [C.Exp]
expToC = openExpToC EmptyEnv EmptyEnv

-- Compile an open embedded scalar unary function into a list of C expression whose length corresponds to the number of
-- tuple components of the embedded result type. In addition ot the generated C, the types and names of the variables
-- that need to contain the function argument are returned.
--
-- The expression may contain free array variables according to the array variable valuation passed as a first argument.
--
fun1ToC :: forall t t' aenv. (Elt t, Elt t') => Env aenv -> OpenFun () aenv (t -> t') -> ([(C.Type, Name)], [C.Exp])
fun1ToC aenv (Lam (Body f))
  = (bnds, openExpToC env aenv f)
  where
    (bnds, env) = EmptyEnv `pushExpEnv` (undefined::OpenExp () aenv t)
fun1ToC _aenv _ = error "D.A.A.C.Exp.fun1ToC: unreachable"

-- Compile an open embedded scalar binary function into a list of C expression whose length corresponds to the number of
-- tuple components of the embedded result type. In addition ot the generated C, the types and names of the variables
-- that need to contain the function argument are returned.
--
-- The expression may contain free array variables according to the array variable valuation passed as a first argument.
--
fun2ToC :: forall t1 t2 t3 aenv. (Elt t1, Elt t2, Elt t3) 
        => Env aenv -> OpenFun () aenv (t1 -> t2 -> t3) -> ([(C.Type, Name)], [(C.Type, Name)], [C.Exp])
fun2ToC aenv (Lam (Lam (Body f)))
  = (bnds1, bnds2, openExpToC env2 aenv f)
  where
    (bnds1, env1) = EmptyEnv `pushExpEnv` (undefined::OpenExp ()       aenv t1)
    (bnds2, env2) = env1     `pushExpEnv` (undefined::OpenExp ((), t1) aenv t2)
fun2ToC _aenv _ = error "D.A.A.C.Exp.fun2ToC: unreachable"

-- Compile an open embedded scalar expression into a list of C expression whose length corresponds to the number of tuple
-- components of the embedded type.
--
-- The expression may contain free array variables according to the array variable valuation passed as a first argument.
--
openExpToC :: Elt t => Env env -> Env aenv -> OpenExp env aenv t -> [C.Exp]
openExpToC = expToC'
  where
    expToC' :: forall t env aenv. Elt t => Env env -> Env aenv -> OpenExp env aenv t -> [C.Exp]
    expToC' env  aenv  (Let bnd body)     = elet env aenv bnd body
    expToC' env  _aenv (Var idx)          = [ [cexp| $id:name |] | (_, name) <- prjEnv idx env]
    expToC' _env _aenv (PrimConst c)      = [primConstToC c]
    expToC' _env _aenv (Const c)          = constToC (eltType (undefined::t)) c
    expToC' env  aenv  (PrimApp f arg)    = [primToC f $ expToC' env aenv arg]
    expToC' env  aenv  (Tuple t)          = tupToC env aenv t 
    expToC' env  aenv  e@(Prj i t)        = prjToC env aenv i t e
    expToC' env  aenv  (Cond p t e)       = condToC env aenv p t e
    expToC' _env _aenv (Iterate _n _f _x) = error "D.A.A.C.Exp: 'Iterate' not supported"
    
    -- Shapes and indices
    expToC' _env _aenv IndexNil                = []
    expToC' _env _aenv IndexAny                = []
    expToC' env  aenv  (IndexCons sh sz)       = expToC' env aenv sh ++ expToC' env aenv sz
    expToC' env  aenv  (IndexHead ix)          = [last $ expToC' env aenv ix]
    expToC' env  aenv  (IndexTail ix)          = init $ expToC' env aenv ix
    expToC' env  aenv  (IndexSlice ix slix sh) = indexSlice ix (expToC' env aenv slix) (expToC' env aenv sh)
    expToC' env  aenv  (IndexFull  ix slix sl) = indexFull  ix (expToC' env aenv slix) (expToC' env aenv sl)
    expToC' env  aenv  (ToIndex sh ix)         = toIndexToC (expToC' env aenv sh) (expToC' env aenv ix)
    expToC' env  aenv  (FromIndex sh ix)       = fromIndexToC (expToC' env aenv sh) (expToC' env aenv ix)
    
    -- -- Arrays and indexing
    expToC' env  aenv (Index acc ix)       = indexToC aenv acc (expToC' env aenv ix)
    expToC' env  aenv (LinearIndex acc ix) = linearIndexToC aenv acc (expToC' env aenv ix)
    expToC' _env aenv (Shape acc)          = shapeToC aenv acc
    expToC' env  aenv (ShapeSize sh)       = shapeSizeToC (expToC' env aenv sh)
    expToC' env  aenv (Intersect sh1 sh2)  = intersectToC (eltType (undefined::t)) 
                                                          (expToC' env aenv sh1)
                                                          (expToC' env aenv sh2)
    
    --Foreign function
    expToC' _env _aenv (Foreign _ff _ _e) = error "D.A.A.C.Exp: 'Foreign' not supported"

    -- Scalar let expressions evaluate their terms and generate new (const) variable bindings to store these results.
    -- Variable names are unambiguously based on the de Bruijn indices and the index of the tuple component they
    -- represent.
    --
    -- FIXME: Currently we need to push lets into each binding, as we don't have a statement sequence as the prelude
    --   to the list of expressions that this function returns.
    --
    elet :: (Elt t, Elt t') => Env env -> Env aenv -> OpenExp env aenv t -> OpenExp (env, t) aenv t' -> [C.Exp]
    elet env aenv bnd body
      = map (\bodyiC -> [cexp| ({ $items:inits $exp:bodyiC; }) |]) (expToC' env_t aenv body)
      where
        (binders, env_t) = env `pushExpEnv` bnd
        inits            = zipWith bindOneComponent binders (expToC' env aenv bnd)
        
        bindOneComponent (tyiC, name) bndiC = [citem| $ty:tyiC $id:name = $exp:bndiC; |]

    -- Convert an open expression into a sequence of C expressions. We retain snoc-list ordering, so the element at
    -- tuple index zero is at the end of the list. Note that nested tuple structures are flattened.
    --
    tupToC :: Env aenv -> Env env -> Tuple (OpenExp aenv env) t -> [C.Exp]
    tupToC _env _eanv NilTup        = []
    tupToC env  aenv  (SnocTup t e) = tupToC env aenv t ++ expToC' env aenv e

    -- Project out a tuple index. Since the nested tuple structure is flattened, this actually corresponds to slicing
    -- out a subset of the list of C expressions, rather than picking out a single element.
    --
    prjToC :: Elt t 
           => Env env 
           -> Env aenv
           -> TupleIdx (TupleRepr t) e
           -> OpenExp env aenv t
           -> OpenExp env aenv e
           -> [C.Exp]
    prjToC env aenv ix t e =
      let subset = reverse
                 . take (length      $ tupleTypeToC (expType e))
                 . drop (prjToInt ix $ preExpType accType t)
                 . reverse
      in
      subset $ expToC' env aenv t

    -- Scalar conditionals. To keep the return type as an expression list we use the ternery C condition operator (?:). 
    --
    -- FIXME: For tuples this is not particularly good, so the least we can do is make sure the predicate result is
    -- evaluated only once and bind it to a local variable.
    --
    condToC :: Elt t 
            => Env env 
            -> Env aenv
            -> OpenExp env aenv Bool
            -> OpenExp env aenv t
            -> OpenExp env aenv t
            -> [C.Exp]
    condToC env aenv p t e
      = zipWith (\tiC eiC -> [cexp| $exp:pC ? $exp:tiC : $exp:eiC |]) (expToC' env aenv t) (expToC' env aenv e)
      where
        [pC] = expToC' env aenv p    -- type guarantees singleton
        

-- Tuples
-- ------

-- Convert a tuple index into the corresponding integer. Since the internal representation is flat, be sure to walk
-- over all sub components when indexing past nested tuples.
--
prjToInt :: TupleIdx t e -> TupleType a -> Int
prjToInt ZeroTupIdx     _                 = 0
prjToInt (SuccTupIdx i) (b `PairTuple` a) = prjToInt i b + sizeTupleType a
prjToInt _              t                 = error $ "D.A.A.C.Exp.prjToInt: inconsistent tuple index: " ++ show t


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

-- Project out a single scalar element from an array. The array expression does not contain any free scalar variables
-- (strictly flat data parallelism) and has been floated out to be replaced by an array variable.
--
-- FIXME: As we have a non-parametric array representation, we should bind the computed linear array index to a variable
--        and share it in the indexing of the various array components.
--
indexToC :: (Shape sh, Elt e) => Env aenv -> OpenAcc aenv (Array sh e) -> [C.Exp] -> [C.Exp]
indexToC aenv (OpenAcc (Avar idx)) ix
  = let ((_, shName):arrNames) = prjEnv idx aenv
    in
    [ [cexp| $id:arr [ $exp:(toIndexWithShape shName ix) ] |] | (_, arr) <- arrNames ]
indexToC _aenv _arr _ix = error "D.A.A.C.Exp.indexToC: array variable expected"

-- Generate linear array indexing code.
--
-- The array argument here can only be a variable, as arrays are lifted out of expressions in an earlier phase.
--
linearIndexToC :: (Shape sh, Elt e) => Env aenv -> OpenAcc aenv (Array sh e) -> [C.Exp] -> [C.Exp]
linearIndexToC aenv (OpenAcc (Avar idx)) ix
  = [ [cexp| $id:arr [ $exp:(head ix) ] |] | (_, arr) <- tail $ prjEnv idx aenv]
                                                      -- 'head (prjEnv idx aenv)' is the shape variable
linearIndexToC _aenv _arr _ix = error "D.A.A.C.Exp.linearIndexToC: array variable expected"
    
-- Generate code to compute the shape of an array.
--
-- The array argument here can only be a variable, as arrays are lifted out of expressions in an earlier phase.
--
-- The first element (always present) in an array valuation is the array's shape variable.
--
shapeToC :: forall sh e aenv. (Shape sh, Elt e) => Env aenv -> OpenAcc aenv (Array sh e) -> [C.Exp]
shapeToC aenv  (OpenAcc (Avar idx)) = cshape (sizeTupleType . eltType $ (undefined::sh)) 
                                             [cexp| * $id:(snd . head $ prjEnv idx aenv) |]
shapeToC _aenv _arr                 = error "D.A.A.C.Exp.shapeToC: array variable expected"

-- The size of a shape, as the product of the extent in each dimension.
--
shapeSizeToC :: [C.Exp] -> [C.Exp]
shapeSizeToC = (:[]) . foldl (\a b -> [cexp| $exp:a * $exp:b |]) [cexp| 1 |] 
    
-- Intersection of two shapes, taken as the minimum in each dimension.
--
intersectToC :: TupleType t -> [C.Exp] -> [C.Exp] -> [C.Exp]
intersectToC ty sh1 sh2 = zipWith (\a b -> ccall "min" [a, b]) (ccastTup ty sh1) (ccastTup ty sh2)


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
primToC (PrimIDiv            ty) [a,b] | isSignedIntegralType ty
                                       = idiv  ty (ccast (NumScalarType $ IntegralNumType ty) a)
                                                  (ccast (NumScalarType $ IntegralNumType ty) b)
                                       | otherwise
                                       = uidiv ty (ccast (NumScalarType $ IntegralNumType ty) a)
                                                  (ccast (NumScalarType $ IntegralNumType ty) b)
primToC (PrimMod             ty) [a,b] | isSignedIntegralType ty
                                       = imod  ty (ccast (NumScalarType $ IntegralNumType ty) a)
                                                  (ccast (NumScalarType $ IntegralNumType ty) b)
                                       | otherwise
                                       = uimod ty (ccast (NumScalarType $ IntegralNumType ty) a)
                                                  (ccast (NumScalarType $ IntegralNumType ty) b)
primToC (PrimBAnd             _) [a,b] = [cexp|$exp:a & $exp:b|]
primToC (PrimBOr              _) [a,b] = [cexp|$exp:a | $exp:b|]
primToC (PrimBXor             _) [a,b] = [cexp|$exp:a ^ $exp:b|]
primToC (PrimBNot             _) [a]   = [cexp|~ $exp:a|]
primToC (PrimBShiftL          _) [a,b] = [cexp|$exp:a << $exp:b|]
primToC (PrimBShiftR          _) [a,b] = [cexp|$exp:a >> $exp:b|]
primToC (PrimBRotateL        ty) [a,b] = rotateL ty a b
primToC (PrimBRotateR        ty) [a,b] = rotateR ty a b
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

ccastTup :: TupleType e -> [C.Exp] -> [C.Exp]
ccastTup ty = fst . travTup ty
  where
    travTup :: TupleType e -> [C.Exp] -> ([C.Exp],[C.Exp])
    travTup UnitTuple         xs     = ([], xs)
    travTup (SingleTuple ty') (x:xs) = ([ccast ty' x], xs)
    travTup (PairTuple l r)   xs     = let
                                         (ls, xs' ) = travTup l xs
                                         (rs, xs'') = travTup r xs'
                                       in 
                                       (ls ++ rs, xs'')
    travTup _ _                      = error "D.A.A.C.Exp.ccastTup: not enough expressions to match type"

postfix :: NumType a -> String -> String
postfix (FloatingNumType (TypeFloat  _)) x = x ++ "f"
postfix (FloatingNumType (TypeCFloat _)) x = x ++ "f"
postfix _                                x = x

isSignedIntegralType :: IntegralType a -> Bool 
isSignedIntegralType (TypeWord{})    = False
isSignedIntegralType (TypeWord8{})   = False
isSignedIntegralType (TypeWord16{})  = False
isSignedIntegralType (TypeWord32{})  = False
isSignedIntegralType (TypeWord64{})  = False
isSignedIntegralType (TypeCUShort{}) = False
isSignedIntegralType (TypeCUInt{})   = False
isSignedIntegralType (TypeCULong{})  = False
isSignedIntegralType (TypeCULLong{}) = False
isSignedIntegralType _               = True
