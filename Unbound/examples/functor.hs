{-# LANGUAGE TemplateHaskell, 
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances, 
             GADTs #-}

module Functor where

import Generics.RepLib hiding (Int)
import Generics.RepLib.Bind.LocallyNameless
import Control.Monad
import Control.Monad.Trans.Error
import Data.List as List

{- So we can't actually do modules like I was thinking of. 
   Substitution in modules only "delays" capture not avoids it.
 -}

type TyName = Name Type
type ModName = Name Module 

data Type = TyVar TyName
          | Int
          | Bool
          | Path Module TyName
   deriving Show

data ModDef =  TyDef TyName (Maybe (Annot Type))
            |  ModDef ModName Module 
                 -- here is the question. For submodules should 
                 -- it be Annot Module or just Module?  For the 
                 -- former, then the "binding" names of the submodule
                 -- could be bound by the outer module. For the latter
                 -- a submodule can't use the same name as the outer 
                 -- module.
   deriving Show
data Module =  Struct  (Rec [ModDef])
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
             (Struct (rec [TyDef t (Just (Annot Bool)), 
             TyDef u (Just (Annot (TyVar x)))])))

m :: Module
m = Struct (rec [TyDef t (Just (Annot Int)), 
                 ModDef g (ModApp f (TyVar t))])


red :: Fresh m => Module -> m Module 
red (ModApp m1 t) = do 
  m1' <- red m1
  case m1' of 
    Functor bnd -> do 
       (x, m1'') <- unbind bnd
       red (subst x t m1'')
    _ -> return (ModApp m1 t)
red (Struct s) = do 
    defs <- mapM redDef (unrec s)
    return (Struct (rec defs))  
red m = return m

redDef :: Fresh m => ModDef -> m ModDef
redDef (ModDef f m) = do 
  m' <- red m
  return (ModDef f m')
redDef d = return d

m3 = Struct (rec [TyDef t Nothing, 
                  TyDef u (Just (Annot (TyVar t)))])

m2 :: Module
m2 = runFreshM (red m)
       
         