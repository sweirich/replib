{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, MultiParamTypeClasses, StandaloneDeriving
 #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  LC
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

-- | A very simple example demonstration of the binding library
-- based on the untyped lambda calculus.
module LCRec where

import Unbound.LocallyNameless
import Control.Monad.Reader (Reader, runReader)
import Data.Set as S
import Data.List as L

-- | A Simple datatype for the Lambda Calculus
data Exp = Var (Name Exp)
         | Lam (Bind (Name Exp) Exp)
         | App Exp Exp
         | Letrec (Bind (Rec [(Name Exp, Embed Exp)]) Exp)
  deriving Show

-- Use RepLib to derive representation types
$(derive [''Exp])

-- | With representation types, tbe default implementation of Alpha
-- provides alpha-equivalence and free variable calculation.
instance Alpha Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance Subst Exp Exp where
   isvar (Var x) = Just (SubstName x)
   isvar _       = Nothing


-- | All new functions should be defined in a monad that can generate
-- locally fresh names.

type M a = FreshM a

-- | Beta-Eta equivalence for lambda calculus terms.
-- If the terms have a normal form
-- then the algorithm will terminate. Otherwise, the algorithm may
-- loop for certain inputs.
(=~) :: Exp -> Exp -> M Bool
e1 =~ e2 | e1 `aeq` e2 = return True
e1 =~ e2 = do
    e1' <- red e1
    e2' <- red e2
    if e1' `aeq` e1 && e2' `aeq` e2
      then return False
      else e1' =~ e2'


-- | Parallel beta-eta reduction for lambda calculus terms.
-- Do as many reductions as possible in one step, while still ensuring
-- termination.
red :: Exp -> M Exp
red (App e1 e2) = do
  e1' <- red e1
  e2' <- red e2
  case e1' of
    -- look for a beta-reduction
    Lam bnd -> do
        (x, e1'') <- unbind bnd
        return $ subst x e2' e1''
    otherwise -> return $ App e1' e2'
red (Lam bnd) = do
   (x, e) <- unbind bnd
   e' <- red e
   case e of
     -- look for an eta-reduction
     App e1 (Var y) | y == x && x `S.notMember` fv e1 -> return e1
     otherwise -> return (Lam (bind x e'))
red (Var x) = return $ (Var x)
red (Letrec bnd) = do
  (r, body) <- unbind bnd
  -- get the variable definitions
  let vars = unrec r
  -- substitute them all (once) throughout the body, iteratively
  let newbody = foldr (\ (x,Embed rhs) body -> subst x rhs body) body vars
  let fvs = fv newbody
  -- garbage collect, if possible
  if (L.any (\ (x,_) -> x `S.member` fvs) vars) then
    return $ Letrec (bind (rec vars) newbody)
  else return newbody

---------------------------------------------------------------------
-- Some testing code to demonstrate this library in action.

assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

assertM :: String -> M Bool -> IO ()
assertM s c =
  if (runFreshM c) then return ()
  else print ("Assertion " ++ s ++ " failed")

x :: Name Exp
x = string2Name "x"

y :: Name Exp
y = string2Name "y"

z :: Name Exp
z = string2Name "z"

s :: Name Exp
s = string2Name "s"

lam :: Name Exp -> Exp -> Exp
lam x y = Lam (bind x y)

zero  = lam s (lam z (Var z))
one   = lam s (lam z (App (Var s) (Var z)))
two   = lam s (lam z (App (Var s) (App (Var s) (Var z))))
three = lam s (lam z (App (Var s) (App (Var s) (App (Var s) (Var z)))))

plus = lam x (lam y (lam s (lam z (App (App (Var x) (Var s)) (App (App (Var y) (Var s)) (Var z))))))

true = lam x (lam y (Var x))
false = lam x (lam y (Var y))
if_ x y z = (App (App x y) z)

e = Letrec (bind (rec [(y, Embed(Var x)), (x, Embed (Var z))]) (Var y))

main :: IO ()
main = do
  -- \x.x == \x.y
  assert "a1" $ lam x (Var x) `aeq` lam y (Var y)
  -- \x.x /= \x.y
  assert "a2" $ not (lam x (Var y) `aeq` lam x (Var x))
  -- \x.(\y.x) (\y.y) == \y.y
  assertM "be1" $ lam x (App (lam y (Var x)) (lam y (Var y))) =~ (lam y (Var y))
  -- \x. f x === f
  assertM "be2" $ lam x (App (Var y) (Var x)) =~ Var y
  assertM "be3" $ if_ true (Var x) (Var y) =~ Var x
  assertM "be4" $ if_ false (Var x) (Var y) =~ Var y
  assertM "be5" $ App (App plus one) two =~ three

