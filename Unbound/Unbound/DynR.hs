{-# LANGUAGE GADTs, ScopedTypeVariables
  #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.RepR
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  sweirich@cis.upenn.edu
-- Portability :  GHC only (-XKitchenSink)
--
-- A Dynamic type based on type representations.
-- This module should probably be added to RepLib instead of Unbound
-- However, it is currently used only in an experimental function
-- (Unbound.Subst.substPats).
module Unbound.DynR (Dyn, toDyn, fromDyn, fromDynR) where

import Generics.RepLib

-- | Dynamic type based on type representations (replib)
data Dyn where 
  Dyn :: Rep a => a -> Dyn

-- | Coerce to a Dynamic type         
toDyn :: Rep a => a -> Dyn 
toDyn = Dyn 

-- | Coerce using an explicit type representation
toDynR :: R a -> a -> Dyn
toDynR ra = withRep ra toDyn

-- | Dynamic cast from the dynamic type (could fail)
fromDyn :: forall a. Rep a => Dyn -> Maybe a 
fromDyn (Dyn x) = cast x

-- | Dyynamic cast using explicit type representation
fromDynR :: forall a. R a -> Dyn -> Maybe a
fromDynR r1 (Dyn x) = castR rep r1 x
