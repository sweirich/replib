{-# LANGUAGE CPP #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Util
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Portability :  GHC only (-XKitchenSink)
--
-- Various utilities for the Unbound library.
----------------------------------------------------------------------

module Unbound.Util where

import Data.Maybe (catMaybes)
import Data.Monoid
import qualified Data.Foldable as F

import qualified Data.Set as S
import qualified Data.Map as M

------------------------------------------------------------
-- Convenient Monoid syntax
------------------------------------------------------------

-- As of base-4.5, (<>) is exported by Data.Monoid.

#if MIN_VERSION_base(4,5,0)
#else
(<>) :: Monoid m => m -> m -> m
(<>) = mappend
#endif

------------------------------------------------------------
-- Collections
------------------------------------------------------------

-- | Collections are foldable types that support empty, singleton,
--   union, and map operations.  The result of a free variable
--   calculation may be any collection.  Instances are provided for
--   lists, sets, and multisets.
class F.Foldable f => Collection f where

  -- | An empty collection. Must be the identity for @union@.
  emptyC    :: f a

  -- | Create a singleton collection.
  singleton :: a -> f a

  -- | An associative combining operation.  The @Ord@ constraint is in
  --   order to accommodate sets.
  union     :: Ord a => f a -> f a -> f a

  -- | Collections must be functorial.  The normal @Functor@ class
  --   won't do because of the @Ord@ constraint on sets.
  cmap      :: (Ord a, Ord b) => (a -> b) -> f a -> f b


-- | Combine a list of containers into one.
unions :: (Ord a, Collection f) => [f a] -> f a
unions = foldr union emptyC

-- | Create a collection from a list of elements.
fromList :: (Ord a, Collection f) => [a] -> f a
fromList = unions . map singleton

-- | Remove the @Nothing@s from a collection.
filterC :: (Collection f, Ord a) => f (Maybe a) -> f a
filterC = fromList . catMaybes . F.toList

-- | Lists are containers under concatenation.  Lists preserve
--   ordering and multiplicity of elements.
instance Collection [] where
  emptyC    = []
  singleton = (:[])
  union     = (++)
  cmap      = map

-- | A simple representation of multisets.
newtype Multiset a = Multiset (M.Map a Int)

instance F.Foldable Multiset where
  fold (Multiset m) = M.foldrWithKey (\a n x -> mconcat (x : replicate n a)) mempty m

-- | Multisets are containers which preserve multiplicity but not
--   ordering.
instance Collection Multiset where
  emptyC                              = Multiset M.empty
  singleton                           = Multiset . flip M.singleton 1
  (Multiset m1) `union` (Multiset m2) = Multiset $ M.unionWith (+) m1 m2
  cmap f (Multiset m)                 = Multiset $ M.mapKeys f m

-- | Sets are containers under union, which preserve only occurrence,
--   not multiplicity or ordering.
instance Collection S.Set where
  emptyC    = S.empty
  singleton = S.singleton
  union     = S.union
  cmap      = S.map

disjoint :: Ord a => S.Set a -> S.Set a -> Bool
disjoint s1 s2 = S.null( S.intersection s1 s2 )

