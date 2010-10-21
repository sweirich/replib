
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

module Data.RepLib.Bind.Perm (
    Perm, single, (<>), apply, support, isid
  ) where

import Data.Monoid
import Data.List
import System.IO.Unsafe

-- | A permutation of values of type 'a'.
data Perm a = Empty
            | Single a a
            | Join (Perm a) (Perm a)
  deriving (Show)

-- Permutations are represented as a list of swaps, to be applied from
-- right to left.  The list is stored as a join-list for efficiency.

-- | Two permutations are equal if they have the same behavior when
--   applied, i.e. they send the same objects to the same objects.
instance Ord a => Eq (Perm a) where
   p1 == p2 = all (\x -> apply p1 x == apply p2 x) (support p1)
              && support p1 `seteq` support p2

-- | Permutations form a monoid:
--
--     * 'mempty' is the identity permutation which has no effect.
--
--     * 'mappend' is composition of permutations
--       (the right-hand permutation is applied first).
instance Monoid (Perm a) where
  mempty            = Empty
  Empty `mappend` p = p
  p `mappend` Empty = p
  p1 `mappend` p2   = Join p1 p2

-- | Create a singleton permutation.  @'single' x y@ exchanges @x@ and
--   @y@ but leaves all other values alone.
single :: Eq a => a -> a -> Perm a
single = Single

-- | Compose two permutations.  The right-hand permutation will be
--   applied first.
(<>) :: Perm a -> Perm a -> Perm a
(<>) = mappend

-- | Apply a permutation to an object, possibly resulting in a
--   different object.
apply :: Eq a => Perm a -> a -> a
apply Empty        a = a
apply (Single x y) a = sw x y a
apply (Join p1 p2) a = apply p1 (apply p2 a)

-- | Possibly split a permutation into a single swap and a remaining
--   permutation.  Return 'Nothing' if the permutation is the identity.
first :: Perm a -> Maybe ((a,a), Perm a)
first Empty        = Nothing
first (Single a b) = Just ((a,b), Empty)
first (Join p1 p2) = case first p1 of
   Nothing -> first p2
   Just (s, p1') -> Just (s, Join p1' p2)

-- | Return a list of all the objects mentioned by a permutation.
names :: Eq a => Perm a -> [a]
names Empty        = []
names (Single x y) = [x , y]
names (Join p1 p2) =
   names p1 ++ names p2

-- | Return a list of all objects that are changed by this permutation.
support :: Eq a => Perm a -> [a]
support p = [ x | x <- names p, not (apply p x == x) ]

-- | Is this permutation the identity?
isid :: Eq a => Perm a -> Bool
isid Empty = True
isid (Single x y) = x == y
isid p = support p == []

seteq :: Ord a => [a] -> [a] -> Bool
seteq x y = nub (sort x) == nub (sort y)

sw :: Eq a => a -> a -> a -> a
sw x y s | x==s = y
         | y==s = x
         | True = s

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
  assert "a1" $ apply Empty 1 == 1
  assert "a2" $ apply (Single 1 2) 1 == 2
  assert "a3" $ apply (Single 2 1) 1 == 2
  assert "a4" $ apply (Join (Single 1 2) (Single 2 1)) 1 == 1

tests_isid = do
  assert "i1" $ isid (Empty :: Perm Int) == True
  assert "i2" $ isid (Single 1 2) == False
  assert "i3" $ isid (Single 1 1) == True
  assert "i4" $ isid (Join (Single 1 2) (Single 1 2)) == True
  assert "i5" $ isid (Join (Single 1 2) (Single 2 1)) == True
  assert "i6" $ isid (Join (Single 1 2) (Single 3 2)) == False

tests_support = do
  assert "s1" $ support (Empty :: Perm Int) `seteq` []
  assert "s2" $ support (Single 1 2) `seteq` [1,2]
  assert "s3" $ support (Single 1 1) `seteq` []
  assert "s4" $ support (Join (Single 1 2) (Single 1 2)) `seteq` []
  assert "s5" $ support (Join (Single 1 2) (Single 2 1)) `seteq` []
  assert "s6" $ support (Join (Single 1 2) (Single 3 2)) `seteq` [1,2,3]

-- need a generator for perms for this to work
{-
p_isid p = forAll (arbitrary :: Gen Int) $ \x ->
    isid p == True ==> apply p x == x
-}