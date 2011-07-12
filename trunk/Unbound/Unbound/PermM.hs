----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Perm
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Portability :  portable
--
-- A slow, but hopefully correct implementation of permutations.
--
----------------------------------------------------------------------

module Unbound.PermM (
    Perm(..), single, compose, apply, support, isid, join, empty, restrict, mkPerm
  ) where

import Data.Monoid
import Data.List
import Data.Map (Map)
import Data.Function (on)
import qualified Data.Map as Map

-- | A /permutation/ is a bijective function from names to names
--   which is the identity on all but a finite set of names.  They
--   form the basis for nominal approaches to binding, but can
--   also be useful in general.
newtype Perm a = Perm (Map a a)

instance Ord a => Eq (Perm a) where
  (Perm p1) == (Perm p2) =
    all (\x -> Map.findWithDefault x x p1 == Map.findWithDefault x x p2) (Map.keys p1) &&
    all (\x -> Map.findWithDefault x x p1 == Map.findWithDefault x x p2) (Map.keys p2)

instance Show a => Show (Perm a) where
  show (Perm p) = show p

-- | Apply a permutation to an element of the domain.
apply :: Ord a => Perm a -> a -> a
apply (Perm p) x = Map.findWithDefault x x p

-- | Create a permutation which swaps two elements.
single :: Ord a => a -> a -> Perm a
single x y = if x == y then Perm Map.empty else
    Perm (Map.insert x y (Map.insert y x Map.empty))

-- | The empty (identity) permutation.
empty :: Perm a
empty = Perm Map.empty

-- | Compose two permutations.  The right-hand permutation will be
--   applied first.
compose :: Ord a => Perm a -> Perm a -> Perm a
compose (Perm b) (Perm a) =
  Perm (Map.fromList ([ (x,Map.findWithDefault y y b) | (x,y) <- Map.toList a]
         ++ [ (x, Map.findWithDefault x x b) | x <- Map.keys b, Map.notMember x a]))

-- | Permutations form a monoid under composition.
instance Ord a => Monoid (Perm a) where
  mempty  = empty
  mappend = compose

-- | Is this the identity permutation?
isid :: Ord a => Perm a -> Bool
isid (Perm p) =
     Map.foldrWithKey (\ a b r -> r && a == b) True p

-- | /Join/ two permutations by taking the union of their relation
--   graphs. Fail if they are inconsistent, i.e. map the same element
--   to two different elements.
join :: Ord a => Perm a -> Perm a -> Maybe (Perm a)
join (Perm p1) (Perm p2) =
     let overlap = Map.intersectionWith (==) p1 p2 in
     if Map.fold (&&) True overlap then
       Just (Perm (Map.union p1 p2))
       else Nothing

-- | The /support/ of a permutation is the set of elements which are
--   not fixed.
support :: Ord a => Perm a -> [a]
support (Perm p) = [ x | x <- Map.keys p, Map.findWithDefault x x p /= x]

-- | Restrict a permutation to a certain domain.
restrict :: Ord a => Perm a -> [a] -> Perm a
restrict (Perm p) l = Perm (foldl' (\p' k -> Map.delete k p') p l)

-- | @mkPerm l1 l2@ creates a permutation that sends @l1@ to @l2@.
--   Fail if there is no such permutation, either because the lists
--   have different lengths or because they are inconsistent (which
--   can only happen if @l1@ or @l2@ have repeated elements).
mkPerm :: Ord a => [a] -> [a] -> Maybe (Perm a)
mkPerm xs ys
  | inconsistent xs ys     = Nothing
  | otherwise              = Just . mconcat $ zipWith single xs ys
  where inconsistent xs ys = length xs /= length ys ||
          (any (not . repeated) . (map . map) snd . groupBy ((==) `on` fst) . sort $ zip xs ys)
        repeated = singletonList . group
        singletonList [_] = True
        singletonList _   = False
