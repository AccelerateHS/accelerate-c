{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Array.Accelerate.C.Acc
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the C code generation for Accelerate array computations.
--

module Data.Array.Accelerate.C.Acc (
  accToC
) where

  -- libraries
import Data.List
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST                  hiding (Val(..), prj)

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Exp
import Data.Array.Accelerate.C.Type


-- Generating C code from Accelerate computations
-- ----------------------------------------------

-- Compile an open Accelerate computation into a function definition.
--
-- The computation may contain free array variables according to the array variable environment passed as a first argument.
--
accToC :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> C.Definition

accToC aenv' (OpenAcc (Alet bnd body))
  = accToC aenv_bnd body
  where
    (_, aenv_bnd) = aenv' `pushAccEnv` bnd

accToC _aenv' (OpenAcc (Use _))
  = [cedecl| int dummy_declaration; |]

accToC aenv' acc@(OpenAcc (Generate _sh f))
  = [cedecl|
      void $id:cFunName ( $params:(cresParams ++ cenvParams) )
      {
        const typename HsWord64 size = $exp:(csize (accDim acc) accSh);
        for (typename HsWord64 i = 0; i < size; i++)
        {
          $items:assigns
        }
      }
    |]
  where
    cresTys    = accTypeToC acc
    cresNames  = accNames "res" [length cresTys - 1]
    cresParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams = aenvToCargs aenv'
    --
    shName     = head cresNames
    accSh       = [cexp| * $id:shName |]    
    (bnds, es) = fun1ToC aenv' f 
    assigns    = [ [citem| const $ty:argTy $id:arg = $exp:d; |] 
                 | (d, (argTy, arg)) <- zip (fromIndexWithShape shName "i" (length bnds)) bnds
                 ]
                 ++
                 [ [citem| $id:resArr [i] = $exp:e; |] 
                 | (resArr, e) <- zip (tail cresNames) es             -- head is the shape variable
                 ]

accToC aenv' acc@(OpenAcc (Map f arr))
  = [cedecl|
      void $id:cFunName ( $params:(cresParams ++ cenvParams ++ cargParams) )
      {
        const typename HsWord64 size = $exp:(csize (accDim arr) argSh);
        for (typename HsWord64 i = 0; i < size; i++)
        {
          $items:assigns
        }
      }
    |]
  where
    cresTys    = accTypeToC acc
    cresNames  = accNames "res" [length cresTys - 1]
    cresParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams = aenvToCargs aenv'
    --
    cargTys    = accTypeToC arr
    cargNames  = accNames "arg" [length cargTys - 1]
    cargParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cargTys cargNames]
    --
    argSh      = [cexp| * $id:(head cargNames) |]
    (bnds, es) = fun1ToC aenv' f 
    assigns    = [ [citem| {
                     const $ty:argTy $id:arg = $id:argArr [i]; 
                     $id:resArr [i] = $exp:e; 
                   } |] 
                 | (resArr, argArr, (argTy, arg), e) <- zip4 (tail cresNames) (tail cargNames)  -- head is the shape variable
                                                             bnds es
                 ]

accToC aenv' acc@(OpenAcc (ZipWith f arr1 arr2))
  = [cedecl|
      void $id:cFunName ( $params:(cresParams ++ cenvParams ++ carg1Params ++ carg2Params) )
      {
        const typename HsWord64 size = $exp:(csize (accDim acc) accSh);
        for (typename HsWord64 i = 0; i < size; i++)
        {
          $items:assigns
        }
      }
    |]
  where
    cresTys     = accTypeToC acc
    cresNames   = accNames "res" [length cresTys - 1]
    cresParams  = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams  = aenvToCargs aenv'
    --
    carg1Tys    = accTypeToC arr1
    carg1Names  = accNames "arg1_" [length carg1Tys - 1]
    carg1Params = [ [cparam| $ty:t $id:name |] | (t, name) <- zip carg1Tys carg1Names]
    --
    carg2Tys    = accTypeToC arr2
    carg2Names  = accNames "arg2_" [length carg2Tys - 1]
    carg2Params = [ [cparam| $ty:t $id:name |] | (t, name) <- zip carg2Tys carg2Names]
    --
    accSh       = [cexp| * $id:(head cresNames) |]
    (bnds1, 
     bnds2, 
     es)        = fun2ToC aenv' f 
    assigns     = [ [citem| {
                      const $ty:arg1Ty $id:arg1 = $id:arg1Arr [i]; 
                      const $ty:arg2Ty $id:arg2 = $id:arg2Arr [i]; 
                      $id:resArr [i] = $exp:e; 
                    } |] 
                  | (resArr, arg1Arr, arg2Arr, (arg1Ty, arg1), (arg2Ty, arg2), e) 
                      <- zip6 (tail cresNames) (tail carg1Names) (tail carg2Names)  -- head is the shape variable
                              bnds1 bnds2 es
                  ]

accToC _ _ = error "D.A.A.C.Acc: unimplemented"


-- Environments
-- ------------

aenvToCargs :: Env aenv -> [C.Param]
aenvToCargs EmptyEnv              = []
aenvToCargs (aenv `PushEnv` bnds) = aenvToCargs aenv ++ [ [cparam| $ty:t $id:name |] | (t, name) <- bnds]


-- Shapes
-- ------

-- Determine the dimensionality of an array.
--
arrDim :: forall sh e. (Shape sh, Elt e) => Array sh e -> Int
arrDim _dummy = dim (undefined::sh)

accDim :: forall sh e aenv. (Shape sh, Elt e) => OpenAcc aenv (Array sh e) -> Int
accDim _dummy = arrDim (undefined::Array sh e)
