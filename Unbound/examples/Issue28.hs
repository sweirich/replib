{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses  #-}

module Issue28 where

import Unbound.LocallyNameless

type Var = Name Term

data Term
  = V Var
  | Unit
  | Pi (Bind (Var, Embed Term) Term)
  | LetRec (Bind (Rec Decl) Term)
    deriving (Show)

data Decl = 
  -- a recursive declaration  x : A = m
  -- where x may occur in m but not in A
  Decl {
    declVar :: Var
    , declClass :: Shift (Embed Term)
    , declVal :: Embed Term
    }
  deriving (Show)

$(derive [''Term, ''Decl])

instance Alpha Term
instance Alpha Decl
instance Subst Term Decl 
instance Subst Term Term where
  isvar (V x) = Just (SubstName x)
  isvar _ = Nothing

x :: Var
x = s2n "x"

letrec :: Decl -> Term -> Term
letrec d e = LetRec $ bind (rec d) e

decl :: Var -> Term -> Term -> Decl
decl v klass e = Decl v (Shift (Embed klass)) (embed e)


m0 = letrec (decl x Unit Unit) Unit

-- >> show m1
--     "LetRec (<[Decl {declVar = x, declClass = {{V x}}, declVal = {V 0@0}}]> V 0@0)"
m1 = letrec (decl x (V x) (V x)) (V x)

-- substitution shows that binding is as we expect,
-- >> subst x Unit m1
--     "LetRec (<[Decl {declVar = x, declClass = {{Unit}}, declVal = {V 0@0}}]> V 0@0)"


-- >> show m2
--     "Pi (<(x,{Unit})> LetRec (<[Decl {declVar = x, declClass = {{V 0@0}}, declVal = {V 0@0}}]> V 0@0))"
--
--     looks a little strange, but the shift is still there
m2 = Pi (bind (x, embed Unit) m1)





