{-# LANGUAGE TemplateHaskell, 
             ScopedTypeVariables,
             FlexibleInstances,
             MultiParamTypeClasses,
             FlexibleContexts,
             UndecidableInstances, 
             GADTs #-}

module F where

import Generics.RepLib
import Generics.RepLib.Bind.LocallyNameless
import Control.Monad
import Control.Monad.Trans.Error
import Data.List as List

-- System F with type and term variables 

type TyName = Name Ty
type TmName = Name Tm

data Ty = TyVar TyName
        | Arr Ty Ty 
        | All (Bind TyName Ty)
   deriving Show

data Tm = TmVar TmName
        | Lam Ty (Bind TmName Tm) 
        | TLam   (Bind TyName Tm)
        | App Tm Tm
        | TApp Tm Ty
   deriving Show

$(derive [''Ty, ''Tm])

------------------------------------------------------  
instance Alpha Ty where
instance Alpha Tm where

instance Subst Tm Ty where
instance Subst Tm Tm where
  isvar (TmVar x) = Just (SubstName x)
instance Subst Ty Ty where
  isvar (TyVar x) = Just (SubstName x)
------------------------------------------------------
type Delta = [ TyName ]
type Gamma = [ (TmName, Ty) ]

data Ctx = Ctx { getDelta :: Delta , getGamma :: Gamma }
emptyCtx = Ctx { getDelta = [], getGamma = [] }

type M = ErrorT String FreshM

runM :: M a -> a 
runM m = case (runFreshM (runErrorT m)) of
   Left s  -> error s
   Right a -> a 

checkTyVar :: Ctx -> TyName -> M ()
checkTyVar g v = do 
    if List.elem v (getDelta g) then 
      return ()
    else 
      throwError "NotFound" 

lookupTmVar :: Ctx -> TmName -> M Ty
lookupTmVar g v = do 
    case lookup v (getGamma g) of 
      Just s -> return s
      Nothing -> throwError "NotFound"

extendTy :: TyName -> Ctx -> Ctx 
extendTy n ctx = ctx { getDelta =  n : (getDelta ctx) }
                       
extendTm :: TmName -> Ty -> Ctx -> Ctx
extendTm n ty ctx = ctx { getGamma = (n, ty) : (getGamma ctx) }

tcty :: Ctx -> Ty -> M ()
tcty g  (TyVar x) = 
   checkTyVar g x 
tcty g  (All b) = do 
   (x, ty') <- unbind b
   tcty (extendTy x g) ty'
tcty g  (Arr t1 t2) = do 
   tcty g  t1 
   tcty g  t2

ti :: Ctx -> Tm -> M Ty
ti g (TmVar x) = lookupTmVar g x 
ti g (Lam ty1 bnd) = do 
  (x, t) <- unbind bnd
  tcty g ty1
  ty2 <- ti (extendTm x ty1 g) t
  return (Arr ty1 ty2)
ti g (App t1 t2) = do 
  ty1 <- ti g t1
  ty2 <- ti g t2
  case ty1 of 
    Arr ty11 ty21 | ty2 `aeq` ty11 -> 
      return ty21
    _ -> throwError "TypeError" 
ti g (TLam bnd) = do 
  (x, t) <- unbind bnd
  ty <- ti (extendTy x g) t
  return (All (bind x ty))
ti g (TApp t ty) = do
  tyt <- ti g t
  case tyt of
   (All b) -> do 
      tcty g  ty 
      (n1, ty1) <- unbind b
      return $ subst n1 ty ty1

---------------------------------------

