{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, MultiParamTypeClasses, StandaloneDeriving
 #-}

module Set where

import Generics.RepLib
import Unbound.LocallyNameless
import Data.List
import Data.Set

data Ty = All (Bind [Name Ty] Ty)
        | Var (Name Ty)
        | Arr Ty Ty deriving Show

$(derive [''Ty])

$(derive_abstract [''Set])

instance Alpha Ty

a, b, c :: Name Ty
a = s2n "a"
b = s2n "b"
c = s2n "c"

sall :: [Name Ty] -> Ty -> Ty
sall ns t = All (setbind ns t)

s1 = sall [a, b] (Arr (Var a) (Var b))
s2 = sall [a, b] (Arr (Var b) (Var a))
s3 = sall [b, a] (Arr (Var a) (Var b))
s4 = sall [b, a] (Arr (Var b) (Var a))
s5 = sall [b, a, c] (Arr (Var b) (Var a))
s6 = sall [a, c] (Arr (Var a) (Var c))

pall :: [Name Ty] -> Ty -> Ty
pall ns t = All (permbind ns t)

p1 = pall [a, b] (Arr (Var a) (Var b))
p2 = pall [a, b] (Arr (Var b) (Var a))
p3 = pall [b, a] (Arr (Var a) (Var b))
p4 = pall [b, a] (Arr (Var b) (Var a))
p5 = pall [b, a, c] (Arr (Var b) (Var a))
p6 = pall [a, c] (Arr (Var a) (Var c))



assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

main :: IO ()
main = do
  assert "s1" $ s1 `aeq` s2
  assert "s2" $ s1 `aeq` s3
  assert "s3" $ s1 `aeq` s4
  assert "s4" $ s1 `aeq` s5
  assert "s5" $ s1 `aeq` s6

  assert "a11" $ p1 `aeq` p2
  assert "a12" $ p1 `aeq` p3
  assert "a13" $ p1 `aeq` p4
  assert "a14" $ not (p1 `aeq` p5)
  assert "a15" $ p1 `aeq` p6

