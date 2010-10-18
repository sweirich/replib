{-# OPTIONS -fglasgow-exts #-}
{-# OPTIONS -fallow-undecidable-instances #-}
{-# OPTIONS -fallow-overlapping-instances #-}
{-# OPTIONS -fth #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  UnifyExp
-- Copyright   :  (c) Ben Kavanagh 2008
-- License     :  BSD
-- 
-- Maintainer  :  ben.kavanagh@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A file demonstrating the use of Data.Replib.Unify
--
-----------------------------------------------------------------------------

module UnifyExp
where

import Data.RepLib
import Data.RepLib.Unify
import Test.HUnit
import Control.Monad.Error



data Exp = Var Int
	 | Plus Exp Exp
	 | K String
	 deriving (Show, Eq)
$(derive [''Exp])

instance HasVar Int Exp where
    is_var (Var i) = Just i
    is_var _ = Nothing
    var = Var

-- A = "f" ==> [(A, "f")]
test1 :: Maybe [(Int, Exp)]
test1 = solveUnification [(Var 1, K "f")]


-- A = "f" + A  ==>   fails occurs check
test2 :: Maybe [(Int, Exp)]
test2 = solveUnification [(Var 1, Plus (K "f") (Var 1))]


-- A + B = B + B ==> A = B
test3 :: Maybe [(Int, Exp)]
test3 = solveUnification [(Plus (Var 1) (Var 2), Plus (Var 2) (Var 2))]

-- A + B = B + C ==> [(A, C), (B, C)]
test4 :: Maybe [(Int, Exp)]
test4 = solveUnification [(Plus (Var 1) (Var 2), Plus (Var 2) (Var 3))]




data Term = TVar Int
	  | K2 String
	  | App Term Term
	 deriving (Show, Eq)
$(derive [''Term])

instance HasVar Int Term where
    is_var (TVar i) = Just i
    is_var _ = Nothing
    var = TVar

-- There are two ways to override the unify [Char] [Char] problem. the first is to implement
-- unify and only offer the case for K2, defaulting to generic unify in other cases. The other 
-- is to implement unify for String using equality, overriding the default Cons/Nil case handling


-- special instance of unify for String
-- Writing an instance for String which leaves 'special' term 'a' abstract has a problem with case a = String,
-- which leads to overlap with a a case.. So we can only specialise String for a known 'special' term (here Term)
instance (Eq n, Show n, HasVar n Term) => Unify n Term String where
    unifyStep _ x y = if x == y 
		      then return ()
		      else throwError $ strMsg ("unify failed when testing equality for " ++ show x ++ " = " ++ show y) 




-- f(g(A)) = f(B)  ==>   [(B, g(A))]
test5 :: Maybe [(Int, Term)]
test5 = solveUnification [(App (K2 "f") (App (K2 "g") (TVar 1)), App (K2 "f") (TVar 2))]


-- f(g(A), A) = f(B, xyz) ==> [(A, xyz), (B, g(xyz))]
test6 :: Maybe [(Int, Term)]
test6 = solveUnification [(App (App (K2 "f") (App (K2 "g") (TVar 1))) (TVar 1), App (App (K2 "f") (TVar 2)) (K2 "xyz"))]

-- f(A) = f(B, C) ==> fail. constructor mismatch. App vs K2. This is in essence an 'arity' failure. 
-- in a term datatype that had Application as an arity plus list, the arity would not be equal and would call failure. 
-- I'm not sure the error message would be adequate. Perhaps I could use a typeclass/newtype to get better error messages 
-- on equality failures.
test7 :: Maybe [(Int, Term)]
test7 = solveUnification [(App (K2 "f") (TVar 1),  App (App (K2 "f") (TVar 2)) (TVar 3))]

-- f(A) = f(B) ==> [(A, B)]
test8 :: Maybe [(Int, Term)]
test8 = solveUnification [(App (K2 "f") (TVar 1), App (K2 "f") (TVar 2))]

-- A = B, B = abc  ==>  [(B, abc), (A, abc)]
test9 :: Maybe [(Int, Term)]
test9 = solveUnification [(TVar 1, TVar 2), (TVar 2, K2 "abc")]

-- A = abc, xyz = X, A = X  ==>  fails with built in equality since we effectively ask abc = xyz
test10 :: Maybe [(Int, Term)]
test10 = solveUnification [(TVar 1, K2 "abc"), (K2 "xyz", TVar 2), (TVar 1, TVar 2)]



-- Test that unification works with surrounding term structure (other datatypes) which are closed, i.e. they have no free variables.
data OuterTerm =  K3 String
	       | Inner Term
	       | App3 OuterTerm OuterTerm
	 deriving (Show, Eq)
$(derive [''OuterTerm])


-- H(f(g(A), A)) = H(f(B, xyz)) ==> [(A, xyz), (B, g(xyz))]  where H is outer
test11 :: Maybe [(Int, Term)]
test11 = solveUnification' 
	   (undefined :: Proxy (Int, Term))
	   [(App3 (K3 "H") (Inner $ App (App (K2 "f") (App (K2 "g") (TVar 1))) (TVar 1)), 
	     App3 (K3 "H") (Inner $ App (App (K2 "f") (TVar 2)) (K2 "xyz")))]


-- H(f(g(A), A)) = H(f(B, xyz)) ==> [(A, xyz), (B, g(xyz))]  where H is outer
test12 :: Maybe [(Int, Term)]
test12 = solveUnification' 
	   (undefined :: Proxy (Int, Term))
	   [(App3 (K3 "H") (Inner $ App (App (K2 "f") (App (K2 "g") (TVar 1))) (TVar 1)), 
	     App3 (K3 "I") (Inner $ App (App (K2 "f") (TVar 2)) (K2 "xyz")))]




-- todo. fix tests so that errors are tested properly. 
tests = test [ test1 ~?= Just [(1,K "f")], 
	       test2 ~?= error "***Exception: occurs check failed", 
	       test3 ~?= Just [(1,Var 2)], 
	       test4 ~?= Just [(1,Var 3),(2,Var 3)],
	       test5 ~?= Just [(2,App (K2 "g") (TVar 1))],
	       test6 ~?= Just [(2,App (K2 "g") (K2 "xyz")),(1,K2 "xyz")],
	       test7 ~?= error "*** Exception: constructor mismatch",
	       test8 ~?= Just [(1,TVar 2)],
	       test9 ~?= Just [(2,K2 "abc"),(1,K2 "abc")],
	       test10 ~?= error "*** Exception: unify failed in built in equality",
	       test11 ~?= Just [(2,App (K2 "g") (K2 "xyz")),(1,K2 "xyz")],
	       test12 ~?= error "*** Exception: unify failed when testing equality for \"H\" = \"I\""]


main = runTestTT tests

