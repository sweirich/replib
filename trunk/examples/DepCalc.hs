{-# LANGUAGE PatternGuards
           , MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}

{- A simple dependent calculus.

     M := x | * | \D. M | M [N] | Pi D. B | c
     D := . | D, x:A

     typing rules:

     x:A \in G
     -----------
     G |- x : A

     G, D |- B : *
     ---------------
     G |- Pi D.B : *

     G, D |- M : B
     ----------------------
     G |- \D.M : Pi D. B

     G |- M : Pi D.B      G |- [N] : D
     ----------------------------------
     G |- M [N] : B[D |-> [N]]

     G |- * : *



     G |- N : B    A === B    (G |- [N] : D)[x |-> N]
     ----------------------------------
     G |- N, [N] : x:A,D


-}

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

import Control.Monad
import Control.Monad.Trans.Maybe

data Exp = EVar (Name Exp)
         | EStar
         | ELam (Bind Tele Exp)
         | EApp Exp [Exp]
         | EPi (Bind Tele Exp)
  deriving Show

data Tele = Empty
          | Cons (Rebind (Name Exp, Annot Exp) Tele)
  deriving Show

$(derive [''Exp, ''Tele])

instance Alpha Exp
instance Alpha Tele

instance Subst Exp Exp where
  isvar (EVar v) = Just (v, id)
  isvar _        = Nothing

instance Subst Exp Tele

evar :: String -> Exp
evar = EVar . string2Name

elam :: [(String, Exp)] -> Exp -> Exp
elam t b = ELam (bind (mkTele t) b)

epi :: [(String, Exp)] -> Exp -> Exp
epi t b = EPi (bind (mkTele t) b)

mkTele :: [(String, Exp)] -> Tele
mkTele []          = Empty
mkTele ((x,e) : t) = Cons (rebind (string2Name x, Annot e) (mkTele t))

appTele :: Tele -> Tele -> Tele
appTele Empty     t2 = t2
appTele (Cons rb) t2 = Cons (rebind p (appTele t1' t2))
  where (p, t1') = reopen rb

lookUp :: (MonadPlus m) => Name Exp -> Tele -> m Exp
lookUp _ Empty     = error "Not found"
lookUp v (Cons rb) | v == x    = return a
                   | otherwise = lookUp v t'
  where ((x, Annot a), t') = reopen rb

{- Polymorphic identity function:

*Main> elam [("A", EStar), ("x", evar "A")] (evar "x")
ELam (<(Cons (<<(A,Annot EStar)>> Cons (<<(x,Annot (EVar A))>> Empty)))> EVar 0@1)
-}

type M = MaybeT LFreshM
ok = return ()

infer :: Tele -> Exp -> M Exp
infer g (EVar x)  = lookUp x g
infer _ EStar     = return EStar
infer g (ELam bnd) = do
  lunbind bnd $ \(delta, m) -> do
    b <- infer (g `appTele` delta) m
    return . EPi $ bind delta b
infer g (EApp m ns) = do
  EPi bnd <- infer g m
  lunbind bnd $ \(delta, b) -> do
    checkList g ns delta
    multiSubst delta ns b
infer g (EPi bnd) = do
  lunbind bnd $ \(delta, b) -> do
    check (g `appTele` delta) b EStar
    return EStar

check :: Tele -> Exp -> Exp -> M ()
check g m a = do
  b <- infer g m
  checkEq b a

checkList :: Tele -> [Exp] -> Tele -> M ()
checkList _ [] Empty = ok
checkList g (e:es) (Cons rb) = do
  let ((x, Annot a), t') = reopen rb
  check g e a
  checkList (subst x e g) (subst x e es) (subst x e t')
checkList _ _ _ = error "Unequal lengths in checkList" -- mismatched lengths

multiSubst :: Tele -> [Exp] -> Exp -> M Exp
multiSubst Empty     [] e = return e
multiSubst (Cons rb) (e1:es) e = multiSubst t' es e'
  where ((x,_), t') = reopen rb
        e' = subst x e1 e
multiSubst _ _ _ = error "Unequal lengths in multiSubst"   -- mismatched lengths

checkEq :: Exp -> Exp -> M ()
checkEq e1 e2 = if aeq e1 e2 then return () else error $ "Not equal: " ++ show e1 ++ " " ++ show e2
  -- actually, this is not correct!

{- BUG:

*Main> let Just (EPi bnd) = runLFreshM . runMaybeT $ infer Empty (elam [("A", EStar), ("x", evar "A")] (evar "x"))
*Main> bnd
<Cons (<<(A,Annot EStar)>> Cons (<<(x,Annot (EVar 0@0))>> Empty))> EVar 0@0
*Main> runLFreshM $ lunbind bnd $ \(delta, m) -> error (show delta ++ " " ++ show m)
*** Exception: Cons (<<(A,Annot EStar)>> Cons (<<(x,Annot (EVar 0@0))>> Empty)) EVar A

The 0@0 in the last line ought to be A.

-}