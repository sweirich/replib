import Unbound.PermM

import Data.Maybe (isJust)
import Data.Monoid
import Data.List (nub, sort)
import qualified Data.Map as M
import System.IO.Unsafe

import Test.QuickCheck

instance (Ord a, Arbitrary a) => Arbitrary (Perm a) where
  arbitrary = (mconcat . map (uncurry single)) `fmap` arbitrary

---------------------------------------------------------------------
(<>) :: Monoid m => m -> m -> m
(<>) = mappend

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

prop_isid :: Perm Int -> Bool
prop_isid p = isid p == (all (\x -> apply p x == x) $ support p)

tests_support = do
  assert "s1" $ support (empty :: Perm Int) `seteq` []
  assert "s2" $ support (single 1 2) `seteq` [1,2]
  assert "s3" $ support (single 1 1) `seteq` []
  assert "s4" $ support ((single 1 2) <> (single 1 2)) `seteq` []
  assert "s5" $ support ((single 1 2) <> (single 2 1)) `seteq` []
  assert "s6" $ support ((single 1 2) <> (single 3 2)) `seteq` [1,2,3]

prop_support :: Perm Int -> Int -> Bool
prop_support p i = (apply p i /= i) == (i `elem` support p)

------------------------------------------------------------

prop_support_empty :: Bool
prop_support_empty = support (empty :: Perm Int) == []

prop_compose_empty_l :: Perm Int -> Int -> Bool
prop_compose_empty_l p i = apply p i == apply (compose empty p) i

prop_compose_empty_r :: Perm Int -> Int -> Bool
prop_compose_empty_r p i = apply p i == apply (compose p empty) i

prop_compose :: Perm Int -> Perm Int -> Int -> Bool
prop_compose p1 p2 i = apply (compose p1 p2) i == apply p1 (apply p2 i)

prop_mkPerm_perm :: [Int] -> [Int] -> Bool
prop_mkPerm_perm xs ys | Just p <- mkPerm xs ys = map (apply p) xs == ys
                       | otherwise = True

prop_mkPerm_fail :: [Int] -> [Int] -> Property
prop_mkPerm_fail xs ys = length xs == length ys && nub xs == xs && nub ys == ys ==> isJust (mkPerm xs ys)