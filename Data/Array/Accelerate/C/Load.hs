-- |
-- Module      : Data.Array.Accelerate.C.Load
-- Copyright   : [2013] Manuel M T Chakravarty

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements dynamic code loading of compiled C functions.
--

module Data.Array.Accelerate.C.Load (
  load, unload
) where

  -- GHC API
import BasicTypes
import ObjLink

  -- standard libraries
import Control.Applicative
import Foreign


-- |Load the given object file and resolve the given symbol.
--
load :: FilePath -> String -> IO (Maybe (FunPtr a))
load fname symbol
  = do
    { initObjLinker
    ; loadObj fname
    ; successStatus <- resolveObjs
    ; case successStatus of
        Succeeded -> fmap castPtrToFunPtr <$> lookupSymbol symbol
        Failed    -> return Nothing
    }

-- |Unload the given object file.
--
unload :: FilePath -> IO ()
unload = unloadObj
