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
-- Module      :  TaggedTerm
-- Copyright   :  (c) the Unbound team (see LICENSE)
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------

module TaggedTerm where

import Unbound.LocallyNameless hiding (Con)

data Term
data Pattern

data Expr :: * -> * where
         -- Note: be very careful here!  Name (Expr a) -> Expr a does
         -- not work since the names in patterns will not get
         -- connected up with names in terms.
  Var :: Name (Expr Term) -> Expr a
  App :: Expr a ->  Expr a -> Expr a
  Lam :: Bind (Expr Pattern) (Expr Term) -> Expr Term
  Con :: String -> [Expr a] -> Expr a

deriving instance Show (Expr a)

$(derive [''Term, ''Pattern, ''Expr])

instance (Rep t) => Alpha (Expr t)

instance Subst (Expr Term) (Expr Term) where
  isvar (Var x) = Just (SubstName x)
  isvar _       = Nothing

instance Subst (Expr Term) (Expr Pattern)

test1 :: Expr Term
test1 = Lam (bind (Con "Pair" [Var $ s2n "y", Var $ s2n "z"]) (Con "Pair" [Var (s2n "y"), Var (s2n "x")]))

test2 :: Expr Term
test2 = subst (s2n "y") (Con "Unit" [] :: Expr Term) test1

test3 :: Expr Term
test3 = subst (s2n "x") (Con "Unit" [] :: Expr Term) test1
