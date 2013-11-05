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
  OpenAccWithName(..), OpenExpWithName, OpenFunWithName, 
  accToC
) where

  -- libraries
import Control.Monad.Trans.State
import Data.List
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST                  hiding (Val(..), prj)
import Data.Array.Accelerate.Tuple

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Exp
import Data.Array.Accelerate.C.Type


-- Code generation monad
-- ---------------------

-- State to generate unique names and collect generated definitions.
--
data CGstate = CGstate
               { unique :: Int
               , cdefs  :: [C.Definition]   -- opposite order in which they are stored
               }

initialCGstate :: CGstate
initialCGstate = CGstate 0 []

-- State monad encapsulating the code generator state.
--
type CG = State CGstate

-- Produce a new unique name on the basis of the given base name.
--
newName :: Name -> CG Name
newName name = state $ \s@(CGstate {unique = unique}) -> (name ++ show unique, s {unique = unique + 1})

-- Store a C definition.
--
define :: C.Definition -> CG ()
define cdef = state $ \s -> ((), s {cdefs = cdef : cdefs s})


-- Generating C code from Accelerate computations
-- ----------------------------------------------

-- Name each array computation with the name of the C function that implements it.
--
data OpenAccWithName aenv t = OpenAccWithName Name (PreOpenAcc OpenAccWithName aenv t)

-- Compile an open Accelerate computation into C definitions and an open Accelerate computation, where each array
-- computation has been named. The name of an array computation may correspond to the name of the C definition
-- implementing that array computation.
--
-- The computation may contain free array variables according to the array variable environment passed as a first argument.
--
accToC :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> ([C.Definition], OpenAccWithName aenv arrs)
accToC aenv acc
  = let (acc', state) = runState (accCG aenv acc) initialCGstate
    in
    (cdefs state, acc')

-- Compile an open Accelerate computation in the 'CG' monad.
--
accCG :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> CG (OpenAccWithName aenv arrs)
accCG aenv' (OpenAcc (Alet bnd body))
  = do
    { bnd'  <- accCG aenv' bnd
    ; body' <- accCG aenv_bnd body
    ; return $ OpenAccWithName noName (Alet bnd' body')
    }
  where
    (_, aenv_bnd) = aenv' `pushAccEnv` bnd

accCG _aenv' (OpenAcc (Avar ix))
  = return $ OpenAccWithName noName (Avar ix)

accCG _aenv' (OpenAcc (Use arr))
  = return $ OpenAccWithName noName (Use arr)

accCG aenv' acc@(OpenAcc (Generate sh f))
  = do
    { funName <- newName cFunName
    ; define $
        [cedecl|
          void $id:funName ( $params:(cresParams ++ cenvParams) )
          {
            const typename HsWord64 size = $exp:(csize (accDim acc) accSh);
            for (typename HsWord64 i = 0; i < size; i++)
            {
              $items:assigns
            }
          }
        |]
    ; return $ OpenAccWithName funName (Generate (adaptExp sh) (adaptFun f))
    }
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

accCG aenv' acc@(OpenAcc (Map f arr))
  = do
    { arr'    <- accCG aenv' arr
    ; funName <- newName cFunName
    ; define $
        [cedecl|
        void $id:funName ( $params:(cresParams ++ cenvParams ++ cargParams) )
        {
          const typename HsWord64 size = $exp:(csize (accDim arr) argSh);
          for (typename HsWord64 i = 0; i < size; i++)
          {
            $items:assigns
          }
        }
      |]
    ; return $ OpenAccWithName funName (Map (adaptFun f) arr')
    }
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

accCG aenv' acc@(OpenAcc (ZipWith f arr1 arr2))
  = do
    { arr1'   <- accCG aenv' arr1
    ; arr2'   <- accCG aenv' arr2
    ; funName <- newName cFunName
    ; define $
        [cedecl|
          void $id:funName ( $params:(cresParams ++ cenvParams ++ carg1Params ++ carg2Params) )
          {
            const typename HsWord64 size = $exp:(csize (accDim acc) accSh);
            for (typename HsWord64 i = 0; i < size; i++)
            {
              $items:assigns
            }
          }
        |]
    ; return $ OpenAccWithName funName (ZipWith (adaptFun f) arr1' arr2')
    }
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

accCG aenv' acc@(OpenAcc (Fold f (z::PreExp OpenAcc aenv e) arr))
  = do
    { arr'    <- accCG aenv' arr
    ; funName <- newName cFunName
    ; define $
        -- We iterate over the result shape, and then, execute a separate loop over the innermost dimension of the
        -- argument, to fold along that dimension per element of the result.
        [cedecl|
          void $id:funName ( $params:(cresParams ++ cenvParams ++ cargParams) )
          {
            const typename HsWord64 resSize   = $exp:(csize (accDim acc) accSh);
            const typename Ix       innerSize = $exp:argSh . a0;
            for (typename HsWord64 i = 0; i < resSize; i++)
            {
              $items:initAccum
              for (typename Ix j = 0; j < innerSize; j++)
              {
                $items:assignsAccum
              }
              $items:assignsRes
            }
          }
        |]
    ; return $ OpenAccWithName funName (Fold (adaptFun f) (adaptExp z) arr')
    }
  where
    cresTys      = accTypeToC acc
    cresNames    = accNames "res" [length cresTys - 1]
    cresParams   = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams   = aenvToCargs aenv'
    --
    cargTys      = accTypeToC arr
    cargNames    = accNames "arg" [length cargTys - 1]
    cargParams   = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cargTys cargNames]
    --
    argSh        = [cexp| * $id:(head cargNames) |]
    accSh        = [cexp| * $id:(head cresNames) |]
    (bnds1, 
     bnds2, 
     es)         = fun2ToC aenv' f 
    assignsAccum = [ [citem| {
                       const $ty:argTy   $id:arg   = $id:argArr [i * innerSize + j];
                       const $ty:accumTy $id:accum = $id:accumName;
                       $id:accumName = $exp:e; 
                     } |] 
                   | (resArr, argArr, (argTy, arg), (accumTy, accum), accumName, e) 
                       <- zip6 (tail cresNames) (tail cargNames)  -- head is the shape variable
                               bnds1 bnds2 accumNames es
                   ]
    assignsRes   = [ [citem| $id:resArr [i] = $id:accumName; |]
                   | (resArr, accumName) <- zip (tail cresNames)  -- head is the shape variable
                                                accumNames
                   ]
    --
    zTys         = tupleTypeToC (eltType (undefined::e))
    accumNames   = expNames "accum" (length zTys)
    zes          = openExpToC EmptyEnv aenv' z
    initAccum    = [ [citem| $ty:zTy $id:accName = $exp:ze; |]
                   | (zTy, accName, ze) <- zip3 zTys accumNames zes
                   ]

accCG _ _ = error "D.A.A.C.Acc: unimplemented array operation"

type OpenExpWithName = PreOpenExp OpenAccWithName

-- Ensure that embedded array computations are of the named variety.
--
adaptExp :: OpenExp env aenv t -> OpenExpWithName env aenv t
adaptExp e
  = case e of
      Var ix                    -> Var ix
      Let bnd body              -> Let (adaptExp bnd) (adaptExp body)
      Const c                   -> Const c
      PrimConst c               -> PrimConst c
      PrimApp f x               -> PrimApp f (adaptExp x)
      Tuple t                   -> Tuple (adaptTuple t)
      Prj ix e                  -> Prj ix (adaptExp e)
      Cond p t e                -> Cond (adaptExp p) (adaptExp t) (adaptExp e)
      Iterate n f x             -> Iterate (adaptExp n) (adaptExp f) (adaptExp x)
      IndexAny                  -> IndexAny
      IndexNil                  -> IndexNil
      IndexCons sh sz           -> IndexCons (adaptExp sh) (adaptExp sz)
      IndexHead sh              -> IndexHead (adaptExp sh)
      IndexTail sh              -> IndexTail (adaptExp sh)
      IndexSlice ix slix sh     -> IndexSlice ix (adaptExp slix) (adaptExp sh)
      IndexFull ix slix sl      -> IndexFull ix (adaptExp slix) (adaptExp sl)
      ToIndex sh ix             -> ToIndex (adaptExp sh) (adaptExp ix)
      FromIndex sh ix           -> FromIndex (adaptExp sh) (adaptExp ix)
      Intersect sh1 sh2         -> Intersect (adaptExp sh1) (adaptExp sh2)
      ShapeSize sh              -> ShapeSize (adaptExp sh)
      Shape acc                 -> Shape (adaptAcc acc)
      Index acc ix              -> Index (adaptAcc acc) (adaptExp ix)
      LinearIndex acc ix        -> LinearIndex (adaptAcc acc) (adaptExp ix)
      Foreign fo f x            -> Foreign fo (adaptFun f) (adaptExp x)
  where
    adaptTuple :: Tuple (OpenExp env aenv) t -> Tuple (OpenExpWithName env aenv) t
    adaptTuple NilTup          = NilTup
    adaptTuple (t `SnocTup` e) = adaptTuple t `SnocTup` adaptExp e
    
    -- No need to traverse embedded arrays as they must have been lifted out as part of sharing recovery.
    adaptAcc (OpenAcc (Avar ix)) = OpenAccWithName noName (Avar ix)
    adaptAcc _                   = error "D.A.A.C: unlifted array computation"

type OpenFunWithName = PreOpenFun OpenAccWithName

adaptFun :: OpenFun env aenv t -> OpenFunWithName env aenv t
adaptFun (Body e) = Body $ adaptExp e
adaptFun (Lam  f) = Lam  $ adaptFun f


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
