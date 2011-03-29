{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) The University of Pennsylvania, 2006
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A file demonstrating the use of RepLib
--
-----------------------------------------------------------------------------

module Basic where

import Generics.RepLib
import Language.Haskell.TH


-- For each datatype that we define, we need to also create its representation.
-- The template Haskell function derive does this automatically for
-- each type.

data Tree a = Leaf a | Node (Tree a) (Tree a)
$(derive [''Tree])

data Day = Monday | Tuesday | Wednesday | Thursday | Friday | Saturday | Sunday

$(derive [''Day])

-- Note, for mutually recursive datatypes, use "derive" and give list
-- of type names.

-- Note also that the functions of RepLib can cooperate with the
-- traditional 'deriving' mechanism
data Company   = C [Dept]                 deriving (Eq, Ord, Show)
data Dept      = D String Manager [CUnit] deriving (Eq, Ord, Show)
data Manager   = M Employee               deriving (Eq, Ord, Show)
data CUnit     = PU Employee | DU Dept    deriving (Eq, Ord, Show)
data Employee  = E Person Salary          deriving (Eq, Ord, Show)
data Person    = P String                 deriving (Eq, Ord, Show)
data Salary    = S Float                  deriving (Eq, Ord, Show)

$(derive
    [''Company,
     ''Dept,
     ''CUnit,
     ''Employee,
 	  ''Manager,
 	  ''Person,
 	  ''Salary])


--
-- Some sample data for these types
--
t1 :: Tree Int
t1 = Node (Node (Leaf 3) (Leaf 4)) (Node (Leaf 5) (Leaf 6))

t2 :: Tree Int
t2 = Node (Node (Leaf 0) (Leaf 7)) (Leaf 20)

s1 :: Company
s1 = C [D "Types" (M (E (P "Stephanie") (S 1000.0)))
            [PU (E (P "Michael") (S 50)),
             PU (E (P "Samuel") (S 50)),
             PU (E (P "Theodore") (S 50))],
        D "Terms" (M (E (P "Stephanie") (S 200)))
            [DU (D "Shipping" (M (E (P "Alice") (S 3000)))
                [])]]


--
-- Prelude operations.
--
-- Note that we didn't derive Eq, Ord, Bounded or Show for "Day" and "Tree". We can
-- do that now with operations from RepLib.PreludeLib.

-- for Day
instance Eq Day      where
  (==) = eqR1 rep1
instance Ord Day     where
  compare = compareR1 rep1
instance Bounded Day where
  minBound = minBoundR1 rep1
  maxBound = maxBoundR1 rep1
instance Show Day    where
  showsPrec = showsPrecR1 rep1

-- for Tree
instance (Rep a, Eq a) => Eq (Tree a)     where (==) = eqR1 rep1
instance (Rep a, Show a) => Show (Tree a) where showsPrec = showsPrecR1 rep1
instance (Rep a, Ord a) => Ord (Tree a)   where compare = compareR1 rep1

-- Besides the prelude operations, RepLib provides a number of other
-- type-indexed operations.

--
-- Instances for RepLib.Lib operations
--

-- Generate creates arbitrary elements of a type, up to a certain depth.
instance Generate Day
instance Generate a => Generate (Tree a)
instance Generate Company
instance Generate Dept
instance Generate Manager
instance Generate CUnit
instance Generate Employee
instance Generate Person
instance Generate Salary


-- Sum adds together all of the Ints in a datastructure
instance GSum a => GSum (Tree a)
instance GSum Company
instance GSum Dept
instance GSum Manager
instance GSum CUnit
instance GSum Employee
instance GSum Person
instance GSum Salary

-- Shrink creates smaller versions of a data structure.
instance Shrink a => Shrink (Tree a)

--
-- SYB Style operations
--
-- RepLib also supports many of the combinators from the SYB library. For example,
-- we can include the following code from the "Paradise" benchmark that gives everyone
-- in the company a raise.

-- Increase salary by percentage
increase :: Float -> Company -> Company
increase k = everywhere (mkT (incS k))

-- "interesting" code for increase
incS :: Float -> Salary -> Salary
incS k (S s) = S (s * (1+k))


--
-- Generalized folds
--
-- finally, we define generalized versions of fold left and
-- fold right for the Tree type constructor.
instance Fold Tree where
  foldRight op = rreduceR1 (rTree1 (RreduceD { rreduceD = op })
                                   (RreduceD { rreduceD = foldRight op}))
  foldLeft  op = lreduceR1 (rTree1 (LreduceD { lreduceD = op })
                                   (LreduceD { lreduceD = foldLeft op }))

assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")


main = do
   assert "m1" (minBound == Monday)
   assert "m2" (maxBound == Sunday)

   assert "e1" (t1 == Node (Node (Leaf 3) (Leaf 4)) (Node (Leaf 5) (Leaf 6)))

   assert "o3" (Monday < Tuesday)
   assert "o4" (not (t1 < t2))
--
   assert "g1" (generate 7 == [Monday,Tuesday,Wednesday,Thursday,Friday,Saturday,Sunday])
   assert "g2" ((generate 3 :: [Tree Int]) == [Leaf 0,Leaf 1,Leaf 2,Node (Leaf 0) (Leaf 0),Node (Leaf 0) (Leaf 1),Node (Leaf 0) (Node (Leaf 0) (Leaf 0)),Node (Leaf 1) (Leaf 0),Node (Leaf 1) (Leaf 1),Node (Leaf 1) (Node (Leaf 0) (Leaf 0)),Node (Node (Leaf 0) (Leaf 0)) (Leaf 0),Node (Node (Leaf 0) (Leaf 0)) (Leaf 1),Node (Node (Leaf 0) (Leaf 0)) (Node (Leaf 0) (Leaf 0))])

--
   assert "s1" (subtrees t1 == [Node (Leaf 3) (Leaf 4),Node (Leaf 5) (Leaf 6)])
   assert "s2" (gsum t1 == 18)
   assert "s3" (gsum t2 == 27)
--
   assert "i1" (increase 0.1 s1 == C [D "Types" (M (E (P "Stephanie") (S 1100.0))) [PU (E (P "Michael") (S 55.0)),PU (E (P "Samuel") (S 55.0)),PU (E (P "Theodore") (S 55.0))],D "Terms" (M (E (P "Stephanie") (S 220.0))) [DU (D "Shipping" (M (E (P "Alice") (S 3300.0))) [])]])

   assert "i2" (s1 < (increase 0.2 s1))
--
   assert "f1" (gproduct t1 == 360)
   assert "f2" (count t1 == 4)

