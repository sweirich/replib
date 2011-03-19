{-# LANGUAGE TemplateHaskell
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , ScopedTypeVariables
           , UndecidableInstances
  #-}

module Generics.RepLib.Bind.LocallyNameless.Test where

import qualified Data.Set as S

import System.IO.Unsafe

import Generics.RepLib hiding (GT)
import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib.Bind.LocallyNameless.Alpha
import Generics.RepLib.Bind.LocallyNameless.Name
import Generics.RepLib.Bind.PermM

-------------------- TESTING CODE --------------------------------
data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp) deriving (Show)

$(derive [''Exp])

instance Alpha Exp
instance Subst Exp Exp where
   isvar (V n) = Just (SubstName n)
   isvar _     = Nothing

nameA, nameB, nameC :: Name Exp
nameA = integer2Name 1
nameB = integer2Name 2
nameC = integer2Name 3

assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
   tests_aeq
   tests_fv
   tests_big
   tests_nth
   tests_acompare

perm = single nameA nameB

naeq x y = not (aeq x y)

tests_aeq = do
   assert "a1" $ (bind nameA nameA) `naeq` (bind nameA nameB)
   assert "a2" $ (bind nameA nameA) `aeq` (bind nameA nameA)
   assert "a3" $ (bind nameA nameA) `aeq` (bind nameB nameB)
   assert "a4" $ (bind nameA nameB) `naeq` (bind nameB nameA)
   assert "a5" $ (bind (nameA, Annot nameB) nameA) `naeq`
                 (bind (nameA, Annot nameC) nameA)
   assert "a6" $ (bind (nameA, Annot nameB) nameA) `aeq`
                 (bind (nameA, Annot nameB) nameA)
   assert "a7" $ (bind (nameA, Annot nameB) nameA) `aeq`
                 (bind (nameB, Annot nameB) nameB)
   assert "a8" $ rebind nameA nameB `naeq` rebind nameB nameB
   assert "a9" $ rebind nameA nameA `naeq` rebind nameB nameB
   assert "a9" $ (bind (rebind nameA (Annot nameA)) nameA) `aeq`
                 (bind (rebind nameB (Annot nameB)) nameB)
   assert "a10" $ bind (rebind (nameA, Annot nameA) ()) nameA `aeq`
                  bind (rebind (nameB, Annot nameA) ()) nameB
   assert "a11" $ bind (rebind (nameA, Annot nameA) ()) nameA `naeq`
                  bind (rebind (nameB, Annot nameB) ()) nameB
   assert "a12" $ bind (Annot nameA) () `naeq` bind (Annot nameB) ()
   assert "a13" $ bind (Annot nameA) () `aeq` bind (Annot nameA) ()
   assert "a14" $ bind (rebind (Annot nameA) ()) () `naeq`
                  bind (rebind (Annot nameB) ()) ()
   assert "a15" $ (rebind (nameA, Annot nameA) ()) `naeq`
                  (rebind (name4, Annot nameC) ())
   assert "a16" $ bind (nameA, nameB) nameA `naeq` bind (nameB, nameA) nameA
   assert "a17" $ bind (nameA, nameB) nameA `naeq` bind (nameA, nameB) nameB
   assert "a18" $ (nameA, nameA) `naeq` (nameA, nameB)
   assert "a19" $ match (nameA, nameA) (nameB, nameC) == Nothing

emptyNE :: S.Set (Name Exp)
emptyNE = S.empty

tests_fv = do
   assert "f1" $ fv (bind nameA nameA) == emptyNE
   assert "f2" $ fv' (pat initial) (bind nameA nameA) == S.empty
   assert "f4" $ fv (bind nameA nameB) == S.singleton nameB
   assert "f5" $ fv (bind (nameA, Annot nameB) nameA) == S.singleton nameB
   assert "f7" $ fv (bind (nameB, Annot nameB) nameB) == S.singleton nameB
   assert "f8" $ fv (rebind nameA nameB) == S.fromList [nameA, nameB]
   assert "f9" $ fv' (pat initial) (rebind nameA nameA) == S.empty
   assert "f3" $ fv (bind (rebind nameA (Annot nameA)) nameA) == emptyNE
   assert "f10" $ fv (rebind (nameA, Annot nameA) ()) == S.singleton nameA
   assert "f11" $ fv' (pat initial) (rebind (nameA, Annot nameA) ()) == S.singleton (AnyName nameA)
   assert "f12" $ fv (bind (Annot nameA) ()) == S.singleton nameA
   assert "f14" $ fv (rebind (Annot nameA) ()) == emptyNE

mkbig :: [Name Exp] -> Exp -> Exp
mkbig (n : names) body =
    L (bind n (mkbig names (A (V n) body)))
mkbig [] body = body

big1 = mkbig (map integer2Name (take 100 [1 ..])) (V name11)
big2 = mkbig (map integer2Name (take 101 [1 ..])) (V name11)


tests_nth = do
  assert "n1" $ nthpat ([nameA],nameB) 0 == AnyName nameA
  assert "n2" $ nthpat ([nameA],nameB) 1 == AnyName nameB
  assert "n3" $ nthpat (nameA, nameB) 0 == AnyName nameA
  assert "p1" $ findpat ([nameA],nameB) (AnyName nameA) == Just 0
  assert "p2" $ findpat ([nameA],nameB) (AnyName nameB) == Just 1
  assert "p3" $ findpat ([nameA],nameB) (AnyName nameC) == Nothing

tests_big = do
   assert "b1" $ big1 `naeq` big2
   assert "b2" $ fv big1 == emptyNE
   assert "b3" $ big1 `aeq` subst name11 (V name11) big1

tests_acompare = do
   -- Names compare in the obvious way.
   assert "ac1" $ acompare nameA nameB == LT
   assert "ac2" $ acompare nameB nameB == EQ
   assert "ac3" $ acompare nameB nameA == GT
   -- structured date compares lexicographically
   assert "ac4" $ acompare (A (V nameA) (V nameA)) (A (V nameA) (V nameA)) == EQ
   assert "ac5" $ acompare (A (V nameA) (V nameA)) (A (V nameA) (V nameB)) == LT
   assert "ac6" $ acompare (A (V nameA) (V nameB)) (A (V nameA) (V nameA)) == GT
   assert "ac7" $ acompare (A (V nameA) (V nameA)) (A (V nameB) (V nameA)) == LT
   assert "ac8" $ acompare (A (V nameB) (V nameA)) (A (V nameA) (V nameA)) == GT
   assert "ac9" $ acompare (A (V nameB) (V nameA)) (A (V nameA) (V nameB)) == GT
   -- comparison goes under binders, alpha-respectingly.
   assert "ac10" $ acompare (bind nameA (A (V nameA) (V nameA))) (bind nameA (A (V nameA) (V nameA))) == EQ
   assert "ac11" $ acompare (bind nameA (A (V nameA) (V nameA))) (bind nameA (A (V nameA) (V nameB))) == GT
   assert "ac12" $ acompare (bind nameC (A (V nameC) (V nameA))) (bind nameA (A (V nameA) (V nameB))) == LT
   -- non-matching binders handled alpha-respectingly.
   assert "ac13" $ acompare (bind [nameA] nameA) (bind [nameA,nameB] nameA)
                 ==  acompare (bind [nameC] nameC) (bind [nameA,nameB] nameA)
   assert "ac14" $ acompare (bind [nameA,nameB] nameA) (bind [nameA] nameA)
                 ==  acompare (bind [nameC,nameB] nameC) (bind [nameA] nameA)
   -- non-binding stuff in patterns gets compared
   assert "ac15" $ acompare (Annot nameA) (Annot nameB) == LT
   assert "ac16" $ acompare (bind (nameC, Annot nameA) (A (V nameC) (V nameC)))
                            (bind (nameC, Annot nameB) (A (V nameC) (V nameC))) == LT
   assert "ac17" $ acompare (bind (nameC, Annot nameA) (A (V nameB) (V nameB)))
                          (bind (nameC, Annot nameB) (A (V nameA) (V nameA))) == LT
   -- TODO: do we need anything special for rebind? For AnyName?

-- properties
-- if match t1 t2 = Some p then swaps p t1 = t2
