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
    Perm, single, compose, apply, support, isid, join, empty, restrict, mkPerm
  ) where

import Data.Monoid
import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import System.IO.Unsafe

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

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
  | length xs == length ys = foldl' (\mp p -> mp >>= join p)
                                    (Just empty)
                                    (zipWith single xs ys)
  | otherwise = Nothing

---------------------------------------------------------------------
seteq :: Ord a => [a] -> [a] -> Bool
seteq x y = nub (sort x) == nub (sort y)


assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
     tests_apply
     tests_isid
     tests_support
     tests_join

tests_join = do
  assert "j1" $ join empty (empty :: Perm Int) == Just empty
  assert "j2" $ join (single 1 2) empty == Just (single 1 2)
  assert "j3" $ join (single 1 2) (single 2 1) == Just (single 1 2)
  assert "j4" $ join (single 1 2) (single 1 3) == Nothing

tests_apply = do
  assert "a1" $ apply empty 1 == 1
  assert "a2" $ apply (single 1 2) 1 == 2
  assert "a3" $ apply (single 2 1) 1 == 2
  assert "a4" $ apply ((single 1 2) <> (single 2 1)) 1 == 1

tests_isid = do
  assert "i1" $ isid (empty :: Perm Int) == True
  assert "i2" $ isid (single 1 2) == False
  assert "i3" $ isid (single 1 1) == True
  assert "i4" $ isid ((single 1 2) <> (single 1 2)) == True
  assert "i5" $ isid ((single 1 2) <> (single 2 1)) == True
  assert "i6" $ isid ((single 1 2) <> (single 3 2)) == False

tests_support = do
  assert "s1" $ support (empty :: Perm Int) `seteq` []
  assert "s2" $ support (single 1 2) `seteq` [1,2]
  assert "s3" $ support (single 1 1) `seteq` []
  assert "s4" $ support ((single 1 2) <> (single 1 2)) `seteq` []
  assert "s5" $ support ((single 1 2) <> (single 2 1)) `seteq` []
  assert "s6" $ support ((single 1 2) <> (single 3 2)) `seteq` [1,2,3]