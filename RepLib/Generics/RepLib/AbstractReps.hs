{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables,
    MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeSynonymInstances, GADTs
  #-}


-----------------------------------------------------------------------------
-- |
-- Module      :  RepLib.LibADT
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Abstract Reps for Common Abstract Datatypes
--
-----------------------------------------------------------------------------
module Generics.RepLib.AbstractReps where

import Generics.RepLib.R
import Generics.RepLib.Derive
import Language.Haskell.TH

import qualified Data.Map
import qualified Data.Set

$(derive_abstract [''Data.Map.Map, ''Data.Set.Set])