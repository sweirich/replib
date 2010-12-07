{- Type checker for LF, based on algorithm in Harper and Pfennig, "On
   Equivalence and Canonical Forms in the LF Type Theory", ACM
   Transactions on Computational Logic, 2000.
-}

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

import qualified Data.Set as S

-- Kinds
data Kind = KPi (Bind (Name Tm, Annot Ty) Kind) -- {x:ty} k
          | Type                                -- type
  deriving Show

-- Types, also called "Families"
data Ty   = TyPi (Bind (Name Tm, Annot Ty) Ty)  -- {x:ty} ty
          | TyApp Ty Tm                         -- ty tm
          | TyConst (Name Ty)                   -- a
  deriving Show

-- Terms, also called "Objects"
data Tm   = Lam (Bind (Name Tm, Annot Ty) Tm)   -- [x:ty] tm
          | TmApp Tm Tm                         -- tm tm
          | TmVar (Name Tm)                     -- x
  deriving Show
  -- Note, Harper and Pfennig distinguish between term variables and
  -- constants.  Variables are things which can be bound by a lambda
  -- or pi; constants are things which are bound in a signature.  For
  -- our purposes there is little value in distinguishing between
  -- them.

$(derive [''Kind, ''Ty, ''Tm])

instance Alpha Kind
instance Alpha Ty
instance Alpha Tm

-- There are no term variables in types or kinds, so we can just
-- use the default structural Subst instances.
instance Subst Tm Kind
instance Subst Tm Ty

-- For Tm we must implement isvar so the Subst instance knows about
-- term variables.
instance Subst Tm Tm where
  isvar (TmVar v) = Just (v, id)
  isvar _         = Nothing

-- A declaration is either a type constant declaration (a name and a kind)
-- or a term constant declaration (a name, type, and optional definition).
data Decl = DeclTy (Name Ty) (Annot Kind)
          | DeclTm (Name Tm) (Annot Ty) (Maybe (Annot Tm))  -- is this right?

-- A program is a sequence of declarations, where each name is bound
-- in the remainder of the program.
data Prog = Nil
          | Cons (Bind Decl Prog)

-- A signature is a set of declarations.
type Sig = S.Set Decl