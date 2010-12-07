{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , MultiParamTypeClasses
           , FlexibleContexts
           , UndecidableInstances
  #-}

module LF where

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

-- Kinds
data Kind = KPi (Bind (Name Tm, Annot Ty) Kind)
          | Star
  deriving Show

-- Types, also called "Families"
data Ty   = TyPi (Bind (Name Tm, Annot Ty) Ty)
          | TyApp Ty Tm
          | TyConst (Name Ty)
  deriving Show

-- Terms, also called "Objects"
data Tm   = Lam (Bind (Name Tm, Annot Ty) Tm)
          | TmApp Tm Tm
          | TmVar (Name Tm)
          | TmConst (Name Tm)
  deriving Show

$(derive [''Kind, ''Ty, ''Tm])

instance Alpha Kind
instance Alpha Ty
instance Alpha Tm

