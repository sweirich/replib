{-# LANGUAGE PatternGuards
           , MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}

{- A "simple" core dependent calculus.

term     M ::= x | * | \D. M | M [N] | Pi D. B 
             | T | c 
             | case M with y of [ c [x] => N ]

tele     D ::= . | x:A, D

ctx      G ::= . | G, x:A          

judgement forms:
    G |- D wf         telescope wellformedness
    G |- [ M ] : D    check a list of terms against a telescope
    G |- chk M : A    check that term M has type A
    G |- inf M : A    infer the type of M (which is A)
    G |- A == B       check that A & B are equal

typing rules:

     telescope well formedness   (checkTele)

     G |-chk A : *    G,x:A |- D wf
     ----------------------------- cons
     G |- x:A, D wf

     ------------- nil
     G |- [] wf

     list of terms vs a telescope   (checks)

     G |-chk N : A    (G |- [N] : D)[x |-> N]
     -------------------------------------- cons
     G |- N, [N] : x:A,D

     -------------- nil
     G |- [] : .

     terms (check && infer)

     x:A \in G
     -----------
     G |- inf x : A

     G |- D wf        G, D |- chk B : *              
     --------------------------------
     G |- inf Pi D.B : *

     G |- D wf        G, D |- inf M : B
     -------------------------------
     G |- inf \D.M : Pi D. B
 
     G |- inf M : Pi D.B      G |- [N] : D
     ---------------------------------------      
     G |- inf M [N] : B [ D |-> [N] ]          ** note: simultaneous substitution **

     ----------
     G |- inf * : *

     G |- inf  M : A    G |- A == B      
     ----------------------------
     G |- chk  M : B

     A = Pi D . *
     T : A \in Sigma 
     ---------------------  
     G |- inf T : A

     dom(D) = [x]
     A = Pi D. Pi D'. T [x]
     c: A \in Sigma
     -------------
     G |- inf c : A 

     G |- inf M : T [ P ] 
     for each i,  
         ci : Pi D. Pi Di. T [x] \in Sigma  where dom(D) = [x] 
         (G, Di, y : M = C [w] |- chk N : A) [ D |-> [N] ]    
    ------------------------------------------------------
     G |- inf case M in A with y of [ c [w] => N ] : A 

-}

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

import Data.Monoid
import Control.Monad
import Control.Monad.Trans.Error

data TyCon    -- tags for the names of type constructors
data DataCon  -- and data constructors so that we don't get them
              -- confused with variables

-- initial context of data and type constructors
sigmaData :: [(Name DataCon, Exp)]
sigmaData = undefined

sigmaTy  :: [(Name TyCon, Exp)]
sigmaTy = undefined


data Exp = EVar (Name Exp)
         | EStar
         | ELam (Bind Tele Exp)
         | EApp Exp [Exp]
         | EPi (Bind Tele Exp)
         | ETyCon (Name TyCon)
         | EDataCon (Name DataCon)
         | ECase Exp (Bind (Name Exp)
                           [Bind [Name Exp] Exp])
  deriving Show

data Tele = Empty
          | Cons (Rebind (Name Exp, Annot Exp) Tele)
  deriving Show

type Ctx  = [ (Name Exp, Exp) ]

$(derive [''TyCon, ''DataCon, ''Exp, ''Tele])

instance Alpha Exp    
instance Alpha Tele

instance Subst Exp Exp where
  isvar (EVar v) = Just (v, id)
  isvar _        = Nothing

instance Subst Exp Tele

------------------------------------------------

-- for examples

evar :: String -> Exp
evar = EVar . string2Name

elam :: [(String, Exp)] -> Exp -> Exp
elam t b = ELam (bind (mkTele t) b)

epi :: [(String, Exp)] -> Exp -> Exp
epi t b = EPi (bind (mkTele t) b)

earr :: Exp -> Exp -> Exp
earr t1 t2 = epi [("_", t1)] t2

eapp :: Exp -> Exp -> Exp
eapp a b = EApp a [b]

mkTele :: [(String, Exp)] -> Tele
mkTele []          = Empty
mkTele ((x,e) : t) = Cons (rebind (string2Name x, Annot e) (mkTele t))

{- Polymorphic identity function -}

pid :: Exp 
pid = elam [("A", EStar), ("x", evar "A")] (evar "x")

{-
ELam (<(Cons (<<(A,{EStar})>> Cons (<<(x,{EVar 0@0})>> Empty)))> EVar 0@1)
-}

{- Polymorphic identity type: -}
sid :: Exp 
sid = epi [("A", EStar), ("x", evar "A")] (evar "A")

{-
EPi (<(Cons (<<(A,{EStar})>> Cons (<<(x,{EVar 0@0})>> Empty)))> EVar 0@0)
-}

{- Polymorphic identity type: -}
sid2 :: Exp 
sid2 = epi [("B", EStar), ("y", evar "B")] (evar "B")


----------------------------------------------------------
-- Type checker

type M = ErrorT String FreshM
ok = return ()

runM :: M a -> a 
runM m = case (runFreshM (runErrorT m)) of 
   Left s  -> error s
   Right a -> a 

lookUp :: Name a -> [(Name a, b)] -> M b
lookUp n []     = throwError $ "Not in scope: " ++ show n
lookUp v ((x,a):t') | v == x    = return a
                    | otherwise = lookUp v t'



unPi :: Ctx -> Exp -> M (Bind Tele Exp)
unPi g (EPi bnd) = return bnd
unPi g e         = throwError $ "Expected pi type, got " ++ show e ++ " instead"

unVar :: Exp -> M (Name Exp)
unVar (EVar x) = return x
unVar e        = throwError $ "Expected variable, got " ++ show e ++ " instead"

-- Check a telescope and push it onto the context
checkTele :: Ctx -> Tele -> M Ctx
checkTele g Empty = return g
checkTele g (Cons rb) = do 
  let ((x,Annot t), tele) = unrebind rb 
  a <- infer g t
  check g a EStar
  checkTele ((x,t) : g) tele

infer :: Ctx -> Exp -> M Exp
infer g (EVar x)  = lookUp x g
infer _ EStar     = return EStar
infer g (ELam bnd) = do
    (delta, m) <- unbind bnd
    g' <- checkTele g delta
    b <- infer g' m
    return . EPi $ bind delta b
infer g (EApp m ns) = do
    bnd <- (unPi g) =<< infer g m
    (delta, b) <- unbind bnd
    checks g ns delta  --- ensures that the length ns == length (binders delta)
    return $ substs (binders delta) ns b
infer g (EPi bnd) = do
    (delta, b) <- unbind bnd
    g' <- checkTele g delta
    check g' b EStar
    return EStar
infer g (ETyCon n) = do
    bnd <- (unPi g) =<< lookUp n sigmaTy
    (delta, t) <- unbind bnd
    checkEq g t EStar
    return $ EPi bnd
infer g (EDataCon c) = do 
  bnd <- (unPi g) =<< lookUp c sigmaData
  (delta, t) <- unbind bnd
  bnd' <- unPi g t
  (delta', EApp (ETyCon _) vars) <- unbind bnd'
  vs <- mapM unVar vars
  if vs == binders delta then return $ EPi bnd
     else throwError $ "incorrect result type for " ++ show (EDataCon c)
infer g (ECase m a bnd) = do 
   (y, brs) <- unbind bnd
   t <- infer g m
   (n, ps)  <- unTApp g t
   _ <- mapM (checkBr y) brs


check :: Ctx -> Exp -> Exp -> M ()
check g m a = do
  b <- infer g m
  checkEq g b a

checks :: Ctx -> [Exp] -> Tele -> M ()
checks _ [] Empty = ok
checks g (e:es) (Cons rb) = do
  let ((x, Annot a), t') = unrebind rb
  check g e a
  checks (subst x e g) (subst x e es) (subst x e t')
checks _ _ _ = throwError $ "Unequal number of parameters and arguments"


-- A conservative, inexpressive notion of equality, just for the sake
-- of the example.
checkEq :: Ctx -> Exp -> Exp -> M ()
checkEq _ e1 e2 = if aeq e1 e2 then return () else throwError $ "Couldn't match: " ++ show e1 ++ " " ++ show e2

