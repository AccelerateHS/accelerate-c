{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Array.Accelerate.C.Base
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements helper functions for C code generation.
--

module Data.Array.Accelerate.C.Base (
  Name,
  Val(..), prj, valSize, push,
  cvar, ccall, cchar, cintegral, cbool,
  rotateL, rotateR, idiv, uidiv, imod, uimod,
  cdim, cshape, {- shapeSize, indexHead -}
) where

  -- libraries
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Sugar (EltRepr)
import Data.Array.Accelerate.AST         (Idx(..))

  -- friends
import Data.Array.Accelerate.C.Type


-- Names
-- -----

type Name = String

-- Valuations
-- ----------

-- Valuating variables with lists of C variable names.
--
-- The length of variable names list corresponds to the number of tuple components of the represented value.
--
data Val env where
  Empty ::                      Val ()
  Push  :: Val env -> [Name] -> Val (env, s)

prj :: Idx env t -> Val env -> [Name]
prj ZeroIdx      (Push _   v) = v
prj (SuccIdx ix) (Push val _) = prj ix val
prj _            _            = error "D.A.A.C.Base: inconsistent valuation"

-- Determine the size of an environment.
--
valSize :: Val env -> Int
valSize Empty        = 0
valSize (Push env _) = 1 + valSize env

-- Extend the given valuation by one more variable of type 't'.
--
-- In addition to the extended valuation, yield the list of newly introduced names. The length of the list corresponds
-- to the number of tuple components of 't'. The names are based on the current size of the environment and the tuple
-- component represented by a given name.
--
push :: Val env -> TupleType (EltRepr t) -> ([Name], Val (env, t))
push env ty
  = (names, env `Push` names)
  where
    name  = "x" ++ show (valSize env)
    names = [name ++ "_" ++ show i | i <- [(0::Int)..sizeTupleType ty - 1]]


-- Common expression forms
-- -----------------------

cvar :: Name -> C.Exp
cvar x = [cexp|$id:x|]

ccall :: Name -> [C.Exp] -> C.Exp
ccall fn args = [cexp|$id:fn ($args:args)|]

cchar :: Char -> C.Exp
cchar c = [cexp|$char:c|]

cintegral :: (Integral a, Show a) => a -> C.Exp
cintegral n = [cexp|$int:n|]

cbool :: Bool -> C.Exp
cbool = cintegral . fromEnum


-- Arithmetic logic function support
-- ---------------------------------

-- Left/Right bitwise rotation
--
rotateL, rotateR :: IntegralType a -> C.Exp -> C.Exp -> C.Exp

rotateL ty x i
  = [cexp|
      ({
        const $ty:(integralTypeToC ty) x = $exp:x;
        const typename HsInt32 i8 = $exp:i & 8 * sizeof(x) - 1;
        i8 == 0 ? x : x << i8 | x >> 8 * sizeof(x) - i8;
      })
    |]

rotateR ty x i
  = [cexp|
      ({
        const $ty:(integralTypeToC ty) x = $exp:x;
        const typename HsInt32 i8 = $exp:i & 8 * sizeof(x) - 1;
        i8 == 0 ? x : x >> i8 | x << 8 * sizeof(x) - i8;
      })
    |]

-- Integer division, truncated towards negative infinity
--
idiv, uidiv :: IntegralType a -> C.Exp -> C.Exp -> C.Exp

idiv ty x y
  = [cexp| 
      ({
        const $ty:(integralTypeToC ty) x = $exp:x;
        const $ty:(integralTypeToC ty) y = $exp:y;
        x > 0 && y < 0 ? (x - y - 1) / y : (x < 0 && y > 0 ? (x - y + 1) / y : x / y);
      })
    |]

uidiv _ty x y = [cexp| $exp:x / $exp:y |]

-- Integer modulus, Haskell style
--
imod, uimod :: IntegralType a -> C.Exp -> C.Exp -> C.Exp

imod ty x y 
  = [cexp| 
      ({
        const $ty:(integralTypeToC ty) x = $exp:x;
        const $ty:(integralTypeToC ty) y = $exp:y;
        const $ty:(integralTypeToC ty) r = x % y;
        x > 0 && y < 0 || x < 0 && y > 0 ? (r != 0 ? r + y : 0) : r;
      })
    |]

uimod _ty x y = [cexp| $exp:x % $exp:y |]


-- Shape and indices support
-- -------------------------

cdim :: Name -> Int -> C.Definition
cdim name n = [cedecl|typedef typename $id:("DIM" ++ show n) $id:name;|]

-- Disassemble a struct-shape into a list of expressions accessing the fields
cshape :: Int -> C.Exp -> [C.Exp]
cshape dim sh
  | dim == 0  = []
  | dim == 1  = [sh]
  | otherwise = map (\i -> [cexp|$exp:sh . $id:('a':show i)|]) [dim-1, dim-2 .. 0]

{-
-- Calculate the size of a shape from its component dimensions
shapeSize :: Rvalue r => [r] -> C.Exp
shapeSize [] = [cexp| 1 |]
shapeSize ss = foldl1 (\a b -> [cexp| $exp:a * $exp:b |]) (map rvalue ss)

indexHead :: Rvalue r => [r] -> C.Exp
indexHead = rvalue . last
-}