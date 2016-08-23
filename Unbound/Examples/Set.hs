{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, MultiParamTypeClasses, StandaloneDeriving
 #-}

module Set where

import Unbound.LocallyNameless
import Unbound.LocallyNameless.Types
import Data.List
import Data.Set

data Ty = All (SetPlusBind [Name Ty] Ty)
        | Var (Name Ty)
        | Arr Ty Ty deriving Show

$(derive [''Ty])

instance Alpha Ty

a, b, c :: Rep a => Name a
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


data E =
  L (Bind (Name E) E)
  | V (Name E)
  | A E E
  | C Int
  | LR (SetBind (Rec [(Name E,Embed E)]) E)
  deriving Show
           
$(derive [''E])           
 
instance Alpha E  
  
letrec :: [(Name E, Embed E)] -> E -> E
letrec ns t = LR (permbind (Rec ns) t)

p1 = letrec [(a, Embed (V a)), (b, Embed (C 2))] (A (V a) (V b))
p2 = letrec [(b, Embed (V 2)), (a, Embed (V a))] (A (V a) (V b))

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

  -- NOTE: this assertion fails. This is a bug. Perm binds don't do what we want. 
  assert "a11" $ p1 `aeq` p2

