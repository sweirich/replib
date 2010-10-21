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
module LC where

import Data.RepLib 
import Data.RepLib.Bind.LocallyNameless 
    (Name, string2Name,
     Bind, bind, 
     LFresh, lunbind,
     Alpha, fv,
     Subst(isvar), subst
     rName, rBind
    )
import Control.Monad.Reader (Reader, runReader)

-- | A Simple datatype for the Lambda Calculus
data Exp = Var Name               
         | Lam (Bind Name Exp)    
         | App Exp Exp 
  deriving Show

-- Use RepLib to derive representation types
$(derive [''Exp])

-- | With representation types, tbe default implementation of Alpha
-- provides alpha-equivalence and free variable calculation.
instance Alpha Exp where

-- | Equivalence for bind expressions is alpha equivalence. So we can't derive Eq 
-- for Exp until we've first made it a member of the Alpha class
deriving instance Eq Exp

-- | The subst class uses generic programming to implement capture
-- avoiding substitution. It just needs to know where the variables
-- are.
instance Subst Exp Exp where
   isvar (Var x) = Just (x,id)
   isvar _       = Nothing


-- | All new functions should be defined in a monad that can generate 
-- locally fresh names. One such monad is the Reader Monad. (Automatically
-- a member of the class LFresh.
type M a = Reader Integer a 

-- | Beta-Eta equivalence for lambda calculus terms.
-- If the terms have a normal form 
-- then the algorithm will terminate. Otherwise, the algorithm may 
-- loop for certain inputs.
(=~) :: Exp -> Exp -> M Bool
e1 =~ e2 | e1 == e2 = return True  
e1 =~ e2 = do 
    e1' <- red e1
    e2' <- red e2
    if e1' == e1 && e2' == e2   
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
      (x, e1'') <- lunbind bnd
      return $ subst x e2' e1''
    otherwise -> return $ App e1' e2'
red (Lam bnd) = do 
   (x, e) <- lunbind bnd
   e' <- red e 
   case e of 
     -- look for an eta-reduction
     App e1 (Var y) | y == x && x `notElem` fv e1 -> return e1
     otherwise -> return (Lam (bind x e')) 
red (Var x) = return $ (Var x)


---------------------------------------------------------------------
-- Some testing code to demonstrate this library in action.

assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed") 

assertM :: String -> M Bool -> IO ()
assertM s c = 
  if (runReader c (0 :: Integer)) then return ()
  else print ("Assertion " ++ s ++ " failed") 

x :: Name
x = string2Name "x"

y :: Name 
y = string2Name "y"

z :: Name 
z = string2Name "z"

s :: Name 
s = string2Name "s"

lam :: Name -> Exp -> Exp
lam x y = Lam (bind x y)

zero  = lam s (lam z (Var z))
one   = lam s (lam z (App (Var s) (Var z)))
two   = lam s (lam z (App (Var s) (App (Var s) (Var z))))
three = lam s (lam z (App (Var s) (App (Var s) (App (Var s) (Var z)))))

plus = lam x (lam y (lam s (lam z (App (App (Var x) (Var s)) (App (App (Var y) (Var s)) (Var z))))))

true = lam x (lam y (Var x))
false = lam x (lam y (Var y))
if_ x y z = (App (App x y) z)

tests = do 
  -- \x.x == \x.y
  assert "a1" $ lam x (Var x) == lam y (Var y)
  -- \x.x /= \x.y
  assert "a2" $ lam x (Var y) /= lam x (Var x)
  -- \x.(\y.x) (\y.y) == \y.y
  assertM "be1" $ lam x (App (lam y (Var x)) (lam y (Var y))) =~ (lam y (Var y))
  -- \x. f x === f  
  assertM "be2" $ lam x (App (Var y) (Var x)) =~ Var y
  assertM "be3" $ if_ true (Var x) (Var y) =~ Var x
  assertM "be4" $ if_ false (Var x) (Var y) =~ Var y
  assertM "be5" $ App (App plus one) two =~ three
  
