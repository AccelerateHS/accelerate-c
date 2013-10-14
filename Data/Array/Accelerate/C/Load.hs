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
  load, lookup, loadAndLookup, unload
) where

  -- GHC API
import BasicTypes
import ObjLink

  -- standard libraries
import Control.Applicative
import Foreign
import Prelude              hiding (lookup)


-- |Load the given object file.
--
load :: FilePath -> IO Bool
load fname 
  = do
    { initObjLinker
    ; loadObj fname
    ; succeeded <$> resolveObjs
    }

-- Resolve the given symbol.
--
lookup :: String -> IO (Maybe (FunPtr a))
lookup symbol = fmap castPtrToFunPtr <$> lookupSymbol symbol

-- |Load the given object file and resolve the given symbol.
--
loadAndLookup :: FilePath -> String -> IO (Maybe (FunPtr a))
loadAndLookup fname symbol
  = do
    { ok <- load fname
    ; if ok then
        lookup symbol
      else
        return Nothing
    }

-- |Unload the given object file.
--
unload :: FilePath -> IO ()
unload = unloadObj
