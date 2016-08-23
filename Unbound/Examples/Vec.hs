{-# LANGUAGE TemplateHaskell
           , UndecidableInstances
           , TypeOperators
           , GADTs
           , FlexibleInstances
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , KindSignatures
           , RankNTypes
           , StandaloneDeriving
           , OverlappingInstances
 #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Vec
-- Copyright   :  (c) the Unbound team (see LICENSE)
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------

module Vec where

import Unbound.LocallyNameless hiding (Nil)

data Z
data S n

data Vec :: * -> * -> * where
  Nil   :: Vec Z a
  Cons  :: a -> Vec n a -> Vec (S n) a

deriving instance Show a => Show (Vec n a)

data Term = Var (Name Term) 
          | Lit (Vec (S (S Z)) Int) 
          | Pair Term Term
  deriving Show

$(derive [''Z, ''S, ''Vec, ''Term])

instance (Alpha a, Rep n) => Alpha (Vec n a)
instance Alpha Term

instance Subst Term Term where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing

instance (Rep n, Rep a) => Subst Term (Vec n a)

t :: Term
t = Pair (Var (s2n "x")) (Lit (Cons 1 (Cons 2 Nil)))