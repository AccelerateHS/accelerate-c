{-# LANGUAGE ScopedTypeVariables #-}
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
--  Val(..), prj,
  cvar, ccall, cchar, cintegral, cbool
) where

  -- standard libraries

  -- libraries
import qualified 
       Language.C         as C
import Language.C.Quote.C as C


-- Names
-- -----

type Name = String

{-
-- Valuations
-- ----------

-- Valuating variables with tuples of C variable names.
--
data Val env where
  Empty ::                      Val ()
  Push  :: Val env -> [Name] -> Val (env, s)

prj :: Idx env t -> Val env -> [Name]
prj ZeroIdx      (Push _   v) = v
prj (SuccIdx ix) (Push val _) = prj ix val
prj _            _            = error "D.A.A.C.Base: inconsistent valuation"
-}

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
