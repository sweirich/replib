{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, TemplateHaskell, TypeOperators, ScopedTypeVariables, TypeSynonymInstances, RankNTypes, GADTs, EmptyDataDecls, StandaloneDeriving #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Nominal.Test
-- License     :  BSD-like (see LICENSE)
--
--------------------------------------------------------------------------
module Unbound.Nominal.Test where

import Unbound.Nominal

-------------------- TESTING CODE --------------------------------
data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp) deriving (Show)

$(derive [''Exp])

instance Alpha Exp
instance Subst Exp Exp where
   isvar (V n) = Just (n, id)
   isvar _     = Nothing

-- deriving instance Eq Exp
-- deriving instance Ord Exp

nameA, nameB, nameC :: Name Exp
nameA = string2Name "A"
nameB = string2Name "B"
nameC = string2Name "C"

assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
   tests_aeq
   tests_fv
   tests_big
   tests_subst

perm = single (AnyName nameA)(AnyName nameB)

naeq x y = not (aeq x y)

a10a = bind (rebind (nameA, Embed nameC) ()) nameA
a10b = bind (rebind (nameB, Embed nameC) ()) nameB

a10c = bind (rebind (nameA, Embed nameA) ()) nameA
a10d = bind (rebind (nameB, Embed nameA) ()) nameB

tests_aeq = do
   assert "a1" $ (bind nameA nameA) `naeq` (bind nameA nameB)
   assert "a2" $ (bind nameA nameA) `aeq` (bind nameA nameA)
   assert "a3" $ (bind nameA nameA) `aeq` (bind nameB nameB)
   assert "a4" $ (bind nameA nameB) `naeq` (bind nameB nameA)
   assert "a5" $ (bind (nameA, Embed nameB) nameA) `naeq`
                 (bind (nameA, Embed nameC) nameA)
   assert "a6" $ (bind (nameA, Embed nameB) nameA) `aeq`
                 (bind (nameA, Embed nameB) nameA)
   assert "a7" $ (bind (nameA, Embed nameB) nameA) `aeq`
                 (bind (nameB, Embed nameB) nameB)
   assert "a8" $ rebind nameA nameB `naeq` rebind nameB nameB
   assert "a9" $ rebind nameA nameA `naeq` rebind nameB nameB
   assert "a9a" $ (bind (rebind nameA (Embed nameA)) nameA) `aeq`
                  (bind (rebind nameB (Embed nameB)) nameB)
   assert "a10" $ bind (rebind (nameA, Embed nameA) ()) nameA `aeq`
                  bind (rebind (nameB, Embed nameA) ()) nameB
   assert "a10a" $ a10a `aeq` a10b
   assert "a11" $ bind (rebind (nameA, Embed nameA) ()) nameA `naeq`
                  bind (rebind (nameB, Embed nameB) ()) nameB
   assert "a12" $ bind (Embed nameA) () `naeq` bind (Embed nameB) ()
   assert "a13" $ bind (Embed nameA) () `aeq` bind (Embed nameA) ()
   assert "a14" $ bind (rebind (Embed nameA) ()) () `naeq`
                  bind (rebind (Embed nameB) ()) ()
   assert "a15" $ (rebind (nameA, Embed nameA) ()) `naeq`
                  (rebind (name4, Embed nameC) ())
   assert "a16" $ bind (nameA, nameB) nameA `naeq`
                  bind (nameB, nameA) nameA
   assert "a17" $ bind (nameA, nameB) nameA `naeq` bind (nameA, nameB) nameB
   assert "a18" $ (nameA, nameA) `naeq` (nameA, nameB)
   assert "a19" $ match (nameA, nameA) (nameB, nameC) == Nothing
   assert "a20" $ (L (bind name2 (L (bind name3 (L (bind name4  (A (V name2) (A (V name3) (V name4))))))))) `aeq`  (L (bind name1 (L (bind name2 (L (bind name3  (A (V name1) (A (V name2) (V name3)))))))))

emptyNE :: Set (Name Exp)
emptyNE = S.empty

tests_fv = do
   assert "f1" $ fv (bind nameA nameA) == emptyNE
   assert "f2" $ fv' Pat (bind nameA nameA) == S.empty
   assert "f3" $ fv (bind (rebind nameA (Embed nameA)) nameA) == emptyNE
   assert "f4" $ fv (bind nameA nameB) == S.singleton nameB
   assert "f5" $ fv (bind (nameA, Embed nameB) nameA) == S.singleton nameB
   assert "f7" $ fv (bind (nameB, Embed nameB) nameB) == S.singleton nameB
   assert "f8" $ fv (rebind nameA nameB) == S.fromList [nameA, nameB]
   assert "f9" $ fv' Pat (rebind nameA nameA) == S.empty
   assert "f9a" $ fv (rebind nameA (Embed nameA)) == S.singleton nameA
   assert "f9b" $ fv' Pat (rebind nameA (Embed nameA)) == S.empty
   assert "f10" $ fv (rebind (nameA, Embed nameA) ()) == S.singleton nameA
   assert "f11" $ fv' Pat (rebind (nameA, Embed nameA) ()) == S.singleton (AnyName nameA)
   assert "f10a" $ fv (rebind (nameA, Embed nameB) ()) == S.singleton nameA
   assert "f11a" $ fv' Pat (rebind (nameA, Embed nameB) ()) == S.singleton (AnyName nameB)


   assert "f12" $ fv (bind (Embed nameA) ()) == S.singleton nameA
   assert "f12a" $ fv' Pat (bind (Embed nameA) ()) == S.singleton (AnyName nameA)

   assert "f14" $ fv (rebind (Embed nameA) ()) == emptyNE
   assert "f14a" $ fv' Pat (rebind (Embed nameA) ()) == S.singleton (AnyName nameA)

tests_subst = do
   assert "s1" $ subst nameA (V nameB) (V nameA) `aeq` (V nameB)
   assert "s2" $ subst nameA (V nameB) (V nameC) `aeq` (V nameC)
   assert "s3" $ subst nameA (V nameB) (L (bind nameA (V nameA))) `aeq`
                                       (L (bind nameA (V nameA)))

   assert "s4" $ subst nameA (V nameB) (L (bind nameB (V nameB))) `aeq`
                                       (L (bind nameA (V nameA)))

   assert "s5" $ subst nameA (V nameB) (L (bind nameC (V nameA))) `aeq`
                                       (L (bind nameC (V nameB)))

   assert "s6" $ subst nameA (V nameA) (L (bind nameC (V nameA))) `aeq`
                                       (L (bind nameC (V nameA)))

   assert "s7" $ subst nameA (V nameA) (L (bind nameA (V nameB))) `aeq`
                                       (L (bind nameA (V nameB)))
   assert "s9" $ subst name1 (V name1)
                  (L (bind name1 (L (bind name2 (L (bind name3
                           (A (V name1) (A (V name2) (V name3))))))))) `aeq`
                  (L (bind name1 (L (bind name2 (L (bind name3
                           (A (V name1) (A (V name2) (V name3)))))))))


mkbig :: [Name Exp] -> Exp -> Exp
mkbig (n : names) body =
    L (bind n (mkbig names (A (V n) body)))
mkbig [] body = body

big1 = mkbig (map integer2Name (take 100 [1 ..])) (V name11)
big2 = mkbig (map integer2Name (take 101 [1 ..])) (V name11)

tests_big = do
   assert "b1" $ big1 `naeq` big2
   assert "b2" $ fv big1 == emptyNE
   assert "b3" $ big1 `aeq` subst name11 (V name11) big1


