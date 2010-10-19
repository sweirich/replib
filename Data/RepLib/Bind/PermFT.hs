{-# LANGUAGE MultiParamTypeClasses #-}
----------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib.Bind.Perm
-- Copyright   :  ???
-- License     :  ???
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  portable
--
-- A slow, but hopefully correct implementation of permutations.
--
----------------------------------------------------------------------

module Data.RepLib.Bind.PermFT (
    Perm, single, (<>), apply, support, isid
  ) where

import Data.List
import qualified Data.Set as S
import Data.FingerTree ((><))
import qualified Data.FingerTree as FT

import Data.Monoid
import qualified Data.Foldable as F

import System.IO.Unsafe


-- | A permutation of values of type 'a'.
newtype Perm a = Perm (FT.FingerTree (S.Set a) (Swap a))

-- Permutations are represented as a list of swaps, to be applied from
-- right to left.  The list is stored in a fingertree for efficiency.
-- At the nodes of the fingertree we cache the set of names mentioned
-- by the permutation, so we don't have to recompute it every time we
-- want to compute the support.
--
-- XXX todo: design a monoid to compute and cache the support
-- directly?

-- | Data structure representing a single swap of two elements.
--   Invariant: the two elements are not equal.
data Swap a = Swap a a
  deriving (Eq, Ord, Show)

-- | Apply a swap.
swap :: Eq a => Swap a -> a -> a
swap (Swap x y) s
    | x == s    = y
    | y == s    = x
    | otherwise = s

instance Ord a => FT.Measured (S.Set a) (Swap a) where
  measure (Swap x y) = S.fromList [x,y]

-- | Two permutations are equal if they have the same behavior when
--   applied, i.e. they send the same objects to the same objects.
instance Ord a => Eq (Perm a) where
   p1 == p2 = all (\x -> apply p1 x == apply p2 x) (support p1)
              && support p1 == support p2

-- | Permutations form a monoid:
--
--     * 'mempty' is the identity permutation which has no effect.
--
--     * 'mappend' is composition of permutations
--       (the right-hand permutation is applied first).
instance Monoid (Perm a) where
  mempty                        = Perm FT.empty
  (Perm p1) `mappend` (Perm p2) = Perm $ p1 >< p2

-- | Create a singleton permutation.  @'single' x y@ exchanges @x@ and
--   @y@ but leaves all other values alone.
single :: Eq a => a -> a -> Perm a
single x y
    | x == y    = mempty
    | otherwise = Perm $ FT.singleton (Swap x y)

-- | Compose two permutations.  The right-hand permutation will be
--   applied first.
(<>) :: Perm a -> Perm a -> Perm a
(<>) = mappend

-- | Apply a permutation to an object, possibly resulting in a
--   different object.
apply :: Eq a => Perm a -> a -> a
apply (Perm p) a = F.foldr swap a p

-- | Return a set of all the objects mentioned by a permutation.
names :: Perm a -> S.Set a
names (Perm p) = FT.measure p

-- | Return a set of all objects that are changed by this permutation.
support :: Eq a => Perm a -> S.Set a
support (Perm p) = S.filter (\x -> apply p x /= x) (names p)

-- | Is this permutation the identity?
isid :: Eq a => Perm a -> Bool
isid = S.null . support

-- Testing

assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
     tests_apply
     tests_isid
     tests_support

tests_apply = do
  assert "a1" $ apply mempty 1 == 1
  assert "a2" $ apply (single 1 2) 1 == 2
  assert "a3" $ apply (single 2 1) 1 == 2
  assert "a4" $ apply ((<>) (single 1 2) (single 2 1)) 1 == 1

tests_isid = do
  assert "i1" $ isid (mempty :: Perm Int) == True
  assert "i2" $ isid (single 1 2) == False
  assert "i3" $ isid (single 1 1) == True
  assert "i4" $ isid ((<>) (single 1 2) (single 1 2)) == True
  assert "i5" $ isid ((<>) (single 1 2) (single 2 1)) == True
  assert "i6" $ isid ((<>) (single 1 2) (single 3 2)) == False

tests_support = do
  assert "s1" $ support (mempty :: Perm Int) == S.empty
  assert "s2" $ support (single 1 2) == S.fromList [1,2]
  assert "s3" $ support (single 1 1) == S.empty
  assert "s4" $ support ((<>) (single 1 2) (single 1 2)) == S.empty
  assert "s5" $ support ((<>) (single 1 2) (single 2 1)) == S.empty
  assert "s6" $ support ((<>) (single 1 2) (single 3 2)) == S.fromList [1,2,3]

-- need a generator for perms for this to work
{-
p_isid p = forAll (arbitrary :: Gen Int) $ \x ->
    isid p == True ==> apply p x == x
-}