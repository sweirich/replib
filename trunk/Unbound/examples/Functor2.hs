{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances,
             GADTs #-}

module Functor2 where

import Unbound.LocallyNameless hiding (Int)
import Control.Monad
import Control.Monad.Trans.Error
import Data.List as List

{- This is the right way to formalize modules and functors
 -}

type TyName = Name Type
type ModName = Name Module

data Type = TyVar TyName
          | Int
          | Bool
          | Path Module String
   deriving Show

data ModDef =  TyDef  TyName  (Maybe (Embed Type))
            |  ModDef ModName (Embed Module)

   deriving Show
data Module =  Struct  (Bind (Rec [(String,ModDef)]) ())
            |  Functor (Bind TyName Module)
            |  ModApp Module Type
            |  ModVar (Name Module)
   deriving Show

$(derive [''Type, ''ModDef, ''Module])

------------------------------------------------------
instance Alpha Type where
instance Alpha Module where
instance Alpha ModDef where

instance Subst Module Type where

instance Subst Module ModDef
instance Subst Module Module where
  isvar (ModVar x) = Just (SubstName x)
  isvar _ = Nothing

instance Subst Type Module where
instance Subst Type ModDef where
instance Subst Type Type where
  isvar (TyVar x) = Just (SubstName x)
  isvar _ = Nothing


t :: TyName
t = string2Name "t"

u :: TyName
u = string2Name "u"

x :: TyName
x = string2Name "x"

g :: ModName
g = string2Name "G"

f :: Module
f = Functor (bind x
             (Struct (bind (rec
                  [("t", TyDef t (Just (Embed Bool))),
                   ("u", TyDef u (Just (Embed (TyVar x))))]) ())))

m :: Module
m = Struct (bind (rec [("t", TyDef t (Just (Embed Int))),
                       ("g", ModDef g (Embed (ModApp f (TyVar t))))]) ())


red :: Fresh m => Module -> m Module
red (ModApp m1 t) = do
  m1' <- red m1
  case m1' of
    Functor bnd -> do
       (x, m1'') <- unbind bnd
       red (subst x t m1'')
    _ -> return (ModApp m1 t)
red (Struct s) = do
    (r,()) <- unbind s
    defs <- mapM redDef (unrec r)
    return (Struct (bind (rec defs) ()))
red m = return m

redDef :: Fresh m => (String,ModDef) -> m (String,ModDef)
redDef (s,ModDef f (Embed m)) = do
  m' <- red m
  return (s,ModDef f (Embed m'))
redDef d = return d

m2 :: Module
m2 = runFreshM (red m)

