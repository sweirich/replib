{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , GADTs
           , ScopedTypeVariables
           , RankNTypes
  #-}

module Unbound.Nominal.Subst where

import Generics.RepLib

import Unbound.Nominal.Name
import Unbound.Nominal.Alpha
import Unbound.Nominal.Types
import Unbound.Nominal.Fresh

---------------------------------
-- Public API
---------------------------------
subst :: (Fresh m, Subst b a) => Name b -> b -> a -> m a
subst = subst' Term

data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b

class (Rep1 (SubstD b) a) => Subst b a where
  isvar :: a -> Maybe (SubstName a b)
  isvar _ = Nothing

  subst' :: (Fresh m) => AlphaCtx -> Name b -> b -> a -> m a
  subst' c n u x =
    case (isvar x :: Maybe (SubstName a b)) of
      Just (SubstName m) -> return $ if m == n then u else x
      Nothing -> substR1 rep1 c n u x

data SubstD b a = SubstD {
  isvarD :: a -> Maybe (SubstName a b)
  , substD :: forall m. (Fresh m) => AlphaCtx -> Name b -> b -> a -> m a
}

instance Subst b a => Sat (SubstD b a) where
  dict = SubstD isvar subst'

-----------------------------------------
-- Generic Implementations
-----------------------------------------
substR1 :: (Fresh m) => R1 (SubstD b) a -> AlphaCtx -> Name b -> b -> a -> m a
substR1 (Data1 _ cons) = \ctx n u d ->
  case (findCon cons d) of
    Val c rec kids -> do
      kids' <- (mapM_l (\w -> substD w ctx n u) rec kids)
      return $ to c kids'
substR1 _ = \_ _ _ d -> return d

------------------------------------------
-- Instances for binders
------------------------------------------
instance (Alpha p, Alpha t, Subst b p, Subst b t) => Subst b (Bind p t) where
  subst' Term n u b@(Bind _ _) = do
    (p, t) <- unbind b
    p' <- subst' Pat n u p
    t' <- subst' Term n u t
    return $ Bind p' t'

  subst' Pat _ _ _ = error "subst called on Bind in Pat"

instance (Alpha p, Subst b p) => Subst b (Rec p) where
  subst' Term _ _ _ = error "subst' called on Rec in Term"
  subst' Pat n u (Rec p) = do
    p' <- subst' Pat n u p
    return $ Rec p'

instance (Alpha t, Subst b t) => Subst b (Embed t) where
  subst' Pat n u (Embed t) =
    Embed <$> subst' Term n u t
  subst' Term n u (Embed t) = error "subst' called on Embed in Term"

instance (Alpha p, Alpha q, Subst b p, Subst b q) => Subst b (Rebind p q) where
  subst' Term _ _ _ = error "subst' called on Rebind in Term"

  subst' Pat n u (Rebind p q) = do
    p2 <- subst' Pat n u p
    q2 <- subst' Pat n u q
    return $ Rebind p2 q2

instance Subst b Int
instance Subst b Bool
instance Subst b ()
instance Subst b Char
instance Subst b Integer
instance Subst b Float
instance Subst b Double

instance Subst b AnyName
instance Rep a => Subst b (R a)
instance Rep a => Subst b (Name a)

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)
