{-# LANGUAGE FlexibleContexts
           , GADTs
           , TypeFamilies
           , TemplateHaskell
           , FlexibleInstances
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module NominalTest where

import Generics.RepLib
import Unbound.Nominal.Fresh
import Unbound.Nominal.Ops
import Unbound.Nominal.Name
import Unbound.Nominal.Types
import Unbound.Nominal.Alpha

------------------------------------
-- Inline tests
------------------------------------
nameX :: N
nameX = s2n "x"

nameY :: N
nameY = s2n "y"

nameZ :: N
nameZ = s2n "z"

type N = Name Expr

data Expr = App Expr Expr
          | Abs (Bind N Expr)
          | Var N
          | Let (Bind (Rec [(N, Embed Expr)]) Expr) -- ^ recursive binding
          deriving (Show)

$(derive [''Expr])

-- Derive Alpha
instance Alpha Expr

-- Simple tests
xy  = App (Var nameX) (Var nameY)
xyAeqXy = aeq' Term xy xy
xy' = runFreshM $ freshen' Term xy
xyNAeqXy' = aeq' Term xy (fst xy')

fvXy = fv' Term xy
fvXy' = fv' Term (fst xy')

-- Simple Abs
idx = Abs (bind nameX (Var nameX))
idy = Abs (bind nameY (Var nameY))
idxAeqIdY = aeq idx idy
fvIdx = fv idx
bindersIdx = binders idx

-- Simple Let
yx = App (Var nameY) (Var nameX)
xEqY = (nameX, Embed $ Var nameY)
yEqX = (nameY, Embed $ Var nameX)
zEqW = (nameZ, Embed $ Var (s2n "w"))
letBinders = [xEqY, yEqX]
letXY = Let (bind (Rec letBinders) yx)
bindersLet = binders' Pat letBinders
bindersLetXY = binders' Term letXY
fvLetXY = fv letXY

letYX = Let (bind (Rec $ reverse letBinders) xy)
letXYZ = Let (bind (Rec (letBinders ++ [zEqW])) xy)
absXY = Abs (bind nameX (App (Var nameX) (Var nameY)))

-------------------------------------------------
-- More testing code
-------------------------------------------------

data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp)
         deriving (Show)
$(derive [''Exp])

instance Alpha Exp

nameA, nameB, nameC :: Name Exp
nameA = s2n "A"
nameB = s2n "B"
nameC = s2n "C"

name1, name2, name3, name4 :: Name Exp
name1 = s2n "n1"
name2 = s2n "n2"
name3 = s2n "n3"
name4 = s2n "n4"

assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: IO ()
do_tests = do
  tests_aeq

naeq x y = not $ aeq x y
naeq' c x y = not $ aeq' c x y

naeqP :: (Alpha a) => a -> a -> Bool
naeqP = naeq' Pat

aeqP :: (Alpha a) => a -> a -> Bool
aeqP = aeq' Pat

a10a = bind (rebind (nameA, Embed nameC) ()) nameA
a10b = bind (rebind (nameB, Embed nameC) ()) nameB

a10c = bind (rebind (nameA, Embed nameA) ()) nameA
a10d = bind (rebind (nameB, Embed nameA) ()) nameB

tests_aeq :: IO ()
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
  assert "a8" $ rebind nameA nameB `naeqP` rebind nameB nameB
  assert "a9" $ rebind nameA nameA `aeqP` rebind nameA nameA
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
  -- assert "a19" $ match (nameA, nameA) (nameB, nameC) == Nothing
  assert "a20" $ (L (bind name2
                     (L (bind name3
                         (L (bind name4
                             (A (V name2)
                              (A (V name3)
                               (V name4))))))))) `aeq`
                  (L (bind name1
                      (L (bind name2
                          (L (bind name3
                              (A (V name1)
                               (A (V name2)
                                (V name3)))))))))

main :: IO ()
main = do
  do_tests
  putStrLn "Finished testing"
