{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables #-}

----------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib.Bind.PermR
-- License     :  BSD
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A type-indexed family of permutations
--
----------------------------------------------------------------------
module Data.RepLib.Bind.PermR  (
    Perm, empty, single, (<>), apply, isid, join, 
  ) where

import Data.RepLib hiding (GT)
import qualified Data.RepLib.Bind.PermM as P

-- A pair of a type representation and a permutation for that type
data RepPerm = forall a. (Rep a, Ord a) => RepPerm (P.Perm a)

-- An "association list", keyed by type representations
newtype Perm = Perm [ RepPerm ]

-- | An empty permutation
empty :: Perm
empty = Perm []

-- | Singleton
single :: (Rep a, Ord a) => a -> a -> Perm
single n1 n2 = Perm [RepPerm (P.single n1 n2)]

-- | Compose two permutations together
(<>) :: Perm -> Perm -> Perm
(Perm []) <> l2 = l2
l1 <> (Perm []) = l1
(Perm (RepPerm (p1 :: P.Perm a) : l1)) <> (Perm (RepPerm (p2 :: P.Perm b) : l2)) = 
     case gcast p2 of
       Just p2' -> let 
          p3 =  p1 P.<> p2'
          Perm p4 = (Perm l1) <> (Perm l2)
          in Perm (RepPerm p3 : p4)
       Nothing -> case compareR (rep :: R a) (rep :: R b) of 
             LT -> Perm (RepPerm p1 : p) where
                     Perm p = (Perm l1) <> Perm (RepPerm p2 : l2)
             GT -> Perm (RepPerm p2 : p) where
                     Perm p = Perm (RepPerm p1 : l1) <> Perm l2
             EQ -> error "Impossible"

-- | merge two permutations, failing if they disagree
join :: Perm -> Perm -> Maybe Perm
join (Perm []) l2 = return l2
join l1 (Perm []) = return l1
join (Perm (RepPerm (p1 :: P.Perm a) : l1))
     (Perm (RepPerm (p2 :: P.Perm b) : l2)) = 
     case gcast p2 of
       Just p2' -> do 
          p3 <- P.join p1 p2'
          Perm p4 <- join (Perm l1) (Perm l2)
          return $ Perm (RepPerm p3 : p4)
       Nothing -> case compareR (rep :: R a) (rep :: R b) of 
             LT -> do 
                     Perm p <- join (Perm l1) (Perm (RepPerm p2 : l2))
                     return $ Perm (RepPerm p1 : p)
             GT -> do 
                     Perm p <- join (Perm (RepPerm p1 : l1)) (Perm l2)
                     return $ Perm (RepPerm p2 : p)
             EQ -> error "Impossible"

find :: R a -> [RepPerm] -> Maybe (P.Perm a)
find r [] = Nothing
find r (RepPerm (p1 :: P.Perm b) : tl) = 
  case gcastR (rep :: R b) r p1 of
    Just p2 -> Just p2
    Nothing -> find r tl

apply :: forall a. (Rep a, Ord a) => Perm -> a -> a
apply (Perm ps) a = 
  case find (rep :: R a) ps of 
    Just p -> P.apply p a
    Nothing -> a

isid :: Perm -> Bool
isid (Perm l) = all isid1 l where
   isid1 :: RepPerm -> Bool
   isid1 (RepPerm p) = P.isid p

composes :: [Perm] -> Perm
composes = foldl (<>) empty






