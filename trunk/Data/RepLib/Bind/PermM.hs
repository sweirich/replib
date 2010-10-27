----------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib.Bind.Perm
-- Copyright   :  ???
-- License     :  BSD
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  portable
--
-- A slow, but hopefully correct implementation of permutations.
--
----------------------------------------------------------------------

module Data.RepLib.Bind.PermM (
    Perm, single, (<>), apply, support, isid, join, empty
  ) where

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import System.IO.Unsafe

newtype Perm a = Perm (Map a a) 

instance Ord a => Eq (Perm a) where
  (Perm p1) == (Perm p2) = 
    all (\x -> Map.findWithDefault x x p1 == Map.findWithDefault x x p2) (Map.keys p1) &&
    all (\x -> Map.findWithDefault x x p1 == Map.findWithDefault x x p2) (Map.keys p2)

instance Show a => Show (Perm a) where
  show (Perm p) = show p
  

apply :: Ord a => Perm a -> a -> a
apply (Perm p) x = Map.findWithDefault x x p

single :: Ord a => a -> a -> Perm a 
single x y = if x == y then Perm Map.empty else 
    Perm (Map.insert x y (Map.insert y x Map.empty))

empty :: Perm a 
empty = Perm Map.empty

-- | Compose two permutations.  The right-hand permutation will be
--   applied first.
(<>) :: Ord a => Perm a -> Perm a -> Perm a
(Perm b) <> (Perm a) = 
  Perm (Map.fromList ([ (x,Map.findWithDefault y y b) | (x,y) <- Map.toList a]
         ++ [ (x, Map.findWithDefault x x b) | x <- Map.keys b, Map.notMember x a]))

-- | isid -- do all keys map to themselves?
isid :: Ord a => Perm a -> Bool
isid (Perm p) = 
     Map.foldrWithKey (\ a b r -> r && a == b) True p 

-- | Join two permutation. Fail if the two permutations map the same 
-- name to two different variables.
join :: Ord a => Perm a -> Perm a -> Maybe (Perm a)
join (Perm p1) (Perm p2) = 
     let overlap = Map.intersectionWith (\x y -> (x,y)) p1 p2 in
     if Map.fold (\ (n1, n2) b -> b && n1 == n2) True overlap then 
       Just (Perm (Map.union p1 p2))
       else Nothing  

support :: Ord a => Perm a -> [a] 
support (Perm p) = [ x | x <- Map.keys p, Map.findWithDefault x x p /= x]

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