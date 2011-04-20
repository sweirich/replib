{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, MultiParamTypeClasses, StandaloneDeriving
 #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  STLC
-- Copyright   :  (c) The University of Pennsylvania, 2010
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
--
-----------------------------------------------------------------------------

module STLC where

import Unbound.LocallyNameless
import Data.Set as S

data Ty = TInt | TUnit | Arr Ty Ty
  deriving (Show, Eq)

data Exp = Lit Int
         | Var (Name Exp)
         | Lam (Bind (Name Exp) Exp)
         | App Exp Ty Exp
         | EUnit
  deriving Show

-- Use RepLib to derive representation types
$(derive [''Ty,''Exp])

-- With representation types, default implementations of these
-- classes are available.
instance Alpha Ty where
instance Alpha Exp where

instance Subst Exp Ty where
instance Subst Exp Exp where
   isvar (Var x) = Just (SubstName x)
   isvar _       = Nothing

type Ctx = [(Name Exp, Ty)]

type M a = LFreshM a

-- A type checker for STLC terms
tc :: Ctx -> Exp -> Ty -> M Bool
tc g (Var n) ty =
  case lookup n g of
    Just ty' -> return (ty == ty')
    Nothing  -> return False
tc g (Lam bnd) (Arr t1 t2) = do
  lunbind bnd $ \ (x , e) ->
    tc ((x,t1) : g) e t2
tc g (App e1 t1 e2) t2= do
  b1 <- tc g e1 (Arr t1 t2)
  b2 <- tc g e2 t1
  return $ b1 && b2
tc g EUnit TUnit = return True
tc g (Lit i) TInt = return True
tc g e t = return False


-- beta-eta equivalence, from Karl Crary's ATTAPL chapter
-- assumes both terms type check
algeq :: Exp -> Exp -> Ty -> M Bool
algeq e1 e2 TInt  = do
  e1' <- wh e1
  e2' <- wh e2
  patheq e1' e2'
algeq e1 e2 TUnit = return True
algeq e1 e2 (Arr t1 t2) = do
  x <- lfresh (s2n "x")
  algeq (App e1 t1 (Var x)) (App e2 t1 (Var x)) t2

-- path equivalence (for terms in weak-head normal form)
patheq :: Exp -> Exp -> M Bool
patheq (Var x) (Var y) | x == y = return True
patheq (Lit x) (Lit y) | x == y = return True
patheq (App e1 ty e2) (App e1' ty' e2') | ty == ty' = do
 b1 <- patheq e1 e1'
 b2 <- algeq e2 e2' ty
 return $ b1 && b2
patheq _ _ = return False

-- weak-head reduction
wh :: Exp -> M Exp
wh (App e1 ty e2) = do
   e1' <- wh e1
   case e1' of
     Lam bnd ->
       lunbind bnd $ \ (x, e1') ->
       wh (subst x e2 e1')
     _ -> return $ App e1' ty e2
wh e = return e

--- A different equivalence algorithm, based on reduce and compare.
--- (Doesn't support eta equivalences for the unit type.)

-- Parallel beta-eta reduction, prefers beta reductions to
-- eta reductions
red :: Exp -> M Exp
red (App e1 t e2) = do
  e1' <- red e1
  e2' <- red e2
  case e1' of
    Lam bnd ->
      lunbind bnd $ \ (x, e1'') ->
        return $ subst x e2' e1''
    _ -> return $ App e1' t e2'
red (Lam bnd) =
   lunbind bnd $ \ (x, e) -> do
    e' <- red e
    case e of
     -- look for an eta-reduction
     App e1 t (Var y) | y == x && x `S.notMember` fv e1 -> return e1
     otherwise -> return e
red e = return $ e

-- Reduce both sides until you find a match.
redcomp :: Exp -> Exp -> M Bool
redcomp e1 e2 = if e1 `aeq` e2 then return True                                         else do
    e1' <- red e1
    e2' <- red e2
    if e1' `aeq` e1 && e2' `aeq` e2
      then return False
      else redcomp e1' e2'

---------------------------------------------------------------------
-- TDPE ???
{-
data RExp a where
   RVar  :: Name a -> RExp a
   RLam  :: (Bind (Name b) (Exp b)) -> Exp (a -> b)
   RApp  :: RExp (a -> b) -> (RExp a) -> RExp b
   RUnit :: RExp ()

reify   :: (Fresh m, Rep a) => Exp a -> m a
reify e = case rep of
           Unit -> return ()
           (Arr a b) -> do
              e' <- reflect x --here's the rub!
              return $ \ x -> reify (RApp e e')

reflect :: (Fresh m, Rep a) => a -> m (RExp a)
reflect m = case rep of
   Unit -> return RUnit
   (Arr a b) -> do
      x <- fresh "x"
      e' <- reflect (m (reify (RVar x)))
      return $ RLam (bind x e')
-}
---------------------------------------------------------------------

assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

assertM :: (a -> Bool) -> String -> M a -> IO ()
assertM f s c =
  if f (runLFreshM c) then return ()
  else print ("Assertion " ++ s ++ " failed")

name1, name2 :: Name Exp
name1 = s2n "x"
name2 = s2n "y"

main :: IO ()
main = do
  -- \x.x === \x.y
  assert "a1" $ Lam (bind name1 (Var name1)) `aeq` Lam (bind name2 (Var name2))
  -- \x.x /= \x.y
  assert "a2" . not $ Lam (bind name1 (Var name2)) `aeq` Lam (bind name1 (Var name1))
  -- [] |- \x. x : () -> ()
  assertM id "tc1" $ tc [] (Lam (bind name1 (Var name1))) (Arr TUnit TUnit)
  -- [] |- \x. x ()  : (Unit -> Int) -> Int
  assertM id "tc2" $ tc []
     (Lam (bind name1
        (App (Var name1) TUnit EUnit))) (Arr (Arr TUnit TInt) TInt)
  -- \x. x  === \x. () :: Unit -> Unit
  assertM id "be1" $
     algeq (Lam (bind name1 (Var name1)))
           (Lam (bind name2 EUnit))
           (Arr TUnit TUnit)
  -- \x. f x === f  :: Int -> Int
  assertM id "be2" $
     algeq (Lam (bind name1 (App (Var name2) TInt (Var name1))))
           (Var name2)
           (Arr TInt TInt)
