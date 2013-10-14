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
  Name, expNames, accNames, cFunName,
  Env(..), prjEnv, envSize, pushExpEnv, pushAccEnv,
  cvar, ccall, cchar, cintegral, cbool,
  rotateL, rotateR, idiv, uidiv, imod, uimod,
  cshapeDefs, cdim, cshape, csize, toIndexWithShape
) where

  -- libraries
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Type

  -- friends
import Data.Array.Accelerate.C.Type


-- Names
-- -----

type Name = String

-- Given a base name and the number of tuple components, yield the component names for a scalar variable.
--
expNames :: Name -> Int -> [Name]
expNames name n = [name ++ "_" ++ show i | i <- [(0::Int)..n-1]]

-- Given a base name and a list of numbers of tuple components, yield the component names for a tuple of array
-- variables.
--
accNames :: Name -> [Int] -> [Name]
accNames name ns = concat [(name ++ show n ++ "_sh") : [name ++ show n ++ "_" ++ show i | i <- [(0::Int)..n-1]] | n <- ns]

-- Base name for C functions implementing Accelerate code.
--
cFunName :: Name
cFunName = "acc"


-- Environments
-- ------------

-- C environment of variables as lists of C variable names and their types.
--
-- The length of variable names list corresponds
--
-- * for scalar values, to the number of tuple components of the represented value and
-- * for array values, to the number of tuple components of the represented values (one array per component) plus one
--   extra name (the first one) for the shape.
--
data Env env where
  EmptyEnv ::                                Env ()
  PushEnv  :: Env env -> [(C.Type, Name)] -> Env (env, s)

prjEnv :: Idx env t -> Env env -> [(C.Type, Name)]
prjEnv ZeroIdx      (PushEnv _   v) = v
prjEnv (SuccIdx ix) (PushEnv env _) = prjEnv ix env
prjEnv _            _               = error "D.A.A.C.Base: inconsistent valuation"

-- Determine the size of an environment.
--
envSize :: Env env -> Int
envSize EmptyEnv        = 0
envSize (PushEnv env _) = 1 + envSize env

-- Extend the given scalar environment by one more variable of type 't'.
--
-- In addition to the extended environment, yield the list of newly introduced names and their C types. The length of
-- the list corresponds to the number of tuple components of 't'. The names are based on the current size of the
-- environment and the tuple component represented by a given name.
--
-- The second argument will not be demanded. We are only interested in its type.
--
pushExpEnv :: forall env aenv t. Elt t => Env env -> OpenExp env aenv t -> ([(C.Type, Name)], Env (env, t))
pushExpEnv env _e
  = (names, env `PushEnv` names)
  where
    ctys  = tupleTypeToC . eltType $ (undefined::t)
    name  = "x" ++ show (envSize env)
    names = zip ctys (expNames name (length ctys))

-- Extend the given array environment by a tuple of array-valued variables
--
-- In addition to the extended environment, yield the list of newly introduced names and their C types. The length of
-- the list corresponds to the sum of the number of tuple components per array in the tuple plus one extra name per
-- array. The names are based on the current size of the environment and the tuple component represented by a given
-- name. The extra name per array is that of the array shape. It preceeds the name of the first array component in the
-- list.
--
-- The second argument will not be demanded. We are only interested in its type.
--
pushAccEnv :: forall arrs aenv e. Arrays arrs 
           => Env aenv -> OpenAcc aenv arrs -> ([(C.Type, Name)], Env (aenv, e))
pushAccEnv env _acc
  = (names, env `PushEnv` names)
  where
    ctys  = arrayTys (arrays (undefined::arrs))
    name  = "a" ++ show (envSize env)
    names = zip (concat ctys) (accNames name (map ((subtract 1) . length) ctys))  -- subtract 1 to account for shape ty
    
    arrayTys :: forall arrs. ArraysR arrs -> [[C.Type]]
    arrayTys ArraysRunit                     = []
    arrayTys (ArraysRarray :: ArraysR arrs') = [arrTypeToC (undefined::arrs')]
    arrayTys (ArraysRpair l r)               = arrayTys l ++ arrayTys r


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

cshapeDefs :: [C.Definition]
cshapeDefs
  = [cunit|
      typedef typename HsWord64                         Ix;
      typedef void*                                     DIM0;
      typedef struct { Ix a0; }                         DIM1;
      typedef struct { Ix a1,a0; }                      DIM2;
      typedef struct { Ix a2,a1,a0; }                   DIM3;
      typedef struct { Ix a3,a2,a1,a0; }                DIM4;
      typedef struct { Ix a4,a3,a2,a1,a0; }             DIM5;
      typedef struct { Ix a5,a4,a3,a2,a1,a0; }          DIM6;
      typedef struct { Ix a6,a5,a4,a3,a2,a1,a0; }       DIM7;
      typedef struct { Ix a7,a6,a5,a4,a3,a2,a1,a0; }    DIM8;
      typedef struct { Ix a8,a7,a6,a5,a4,a3,a2,a1,a0; } DIM9;  
    |]

cdim :: Name -> Int -> C.Definition
cdim name n = [cedecl|typedef typename $id:("DIM" ++ show n) $id:name;|]

-- Disassemble a struct-shape into a list of expressions accessing the fields.
--
cshape :: Int -> C.Exp -> [C.Exp]
cshape dim sh = map (\i -> [cexp| $exp:sh . $id:('a':show i) |]) [dim-1, dim-2 .. 0]

-- Generate code calculating the size of an array from its shape, given then shape struct and its dimension.
--
csize :: Int -> C.Exp -> C.Exp
csize n sh = foldl cmul [cexp| 1 |] [[cexp| $exp:sh . $id:('a':show i) |] | i <- [0..n - 1]]
  where
    cmul e1 e2 = [cexp| $exp:e1 * $exp:e2 |]

-- Generate code to calculate a linear from a multi-dimensional index (given an array shape).
--
toIndexWithShape :: Name -> [C.Exp] -> C.Exp
toIndexWithShape shName is
  = toIndex [(0::Int)..] (reverse is)    -- we use a row-major representation
  where
    toIndex _dims  []     = [cexp| NULL |]
    toIndex _dims  [i]    = i
    toIndex (d:ds) (i:is) = [cexp| $exp:(toIndex ds is) * $id:shName.$id:('a':show d) + $exp:i |]
    toIndex _      _      = error "D.A.A.C.Base.toIndexWithShape: oops"
