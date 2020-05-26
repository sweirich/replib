{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
           , TypeFamilies
           , GADTs
           , ScopedTypeVariables
  #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless.Subst
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Portability :  GHC only (-XKitchenSink)
--
-- The @Subst@ type class for generic capture-avoiding substitution.
----------------------------------------------------------------------
module Unbound.LocallyNameless.Subst where

import Data.List (find)

import Generics.RepLib

import Data.Proxy

import Unbound.DynR
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha

------------------------------------------------------------
-- Substitution
------------------------------------------------------------

-- | See 'isvar'.
data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b
  
-- | See 'isCoerceVar'  
data SubstCoerce a b where  
  SubstCoerce :: Name b -> (b -> Maybe a) -> SubstCoerce a b

-- | Immediately substitute for a (single) bound variable
-- in a binder, without first naming that variable.
substBind :: Subst a b => Bind (Name a) b -> a -> b
substBind (B _ t) u = substPat initial u t


-- | The @Subst@ class governs capture-avoiding substitution.  To
--   derive this class, you only need to indicate where the variables
--   are in the data type, by overriding the method 'isvar'.
class (Rep1 (SubstD b) a) => Subst b a where

  -- | This is the only method which normally needs to be implemented
  --   explicitly.  If the argument is a variable, return its name
  --   wrapped in the 'SubstName' constructor.  Return 'Nothing' for
  --   non-variable arguments.  The default implementation always
  --   returns 'Nothing'.
  isvar :: a -> Maybe (SubstName a b)
  isvar _ = Nothing
  
  -- | This is an alternative version to 'isvar', useable in the case 
  --   that the substituted argument doesn't have *exactly* the same type
  --   as the term it should be substituted into.
  --   The default implementation always returns 'Nothing'.
  isCoerceVar :: a -> Maybe (SubstCoerce a b)
  isCoerceVar _ = Nothing

  -- | @'subst' nm sub tm@ substitutes @sub@ for @nm@ in @tm@.  It has
  --   a default generic implementation in terms of @isvar@.
  subst :: Name b -> b -> a -> a
  subst n u x | isFree n =
     case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) -> if  m == n then u else x
        Nothing -> case (isCoerceVar x :: Maybe (SubstCoerce a b)) of 
           Just (SubstCoerce m f) -> if m == n then maybe x id (f u) else x
           Nothing -> substR1 rep1 n u x
  subst m _ _ = error $ "Cannot substitute for bound variable " ++ show m

  -- | Perform several simultaneous substitutions.  This method also
  --   has a default generic implementation in terms of @isvar@.
  substs :: [(Name b, b)] -> a -> a
  substs ss x
    | all (isFree . fst) ss =
      case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) ->
          case find ((==m) . fst) ss of
            Just (_, u) -> u
            Nothing     -> x
        Nothing -> case isCoerceVar x :: Maybe (SubstCoerce a b) of 
            Just (SubstCoerce m f) ->
              case find ((==m) . fst) ss of 
                  Just (_, u) -> maybe x id (f u)
                  Nothing -> x
            Nothing -> substsR1 rep1 ss x
    | otherwise =
      error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)


  -- Pattern substitution (single variable)
  -- call this using the top level function (substBind)
  substPat ::AlphaCtx -> b -> a -> a
  substPat ctx u x = 
     case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName (Bn r j 0)) | level ctx == j -> u
        _ -> substPatR1 rep1 ctx u x

  -- Pattern substitution (all variables in a single pattern)
  -- TODO: make this return Maybe when the dynamic chack fails
  -- i.e. when there aren't the right number/sort of arguments
  -- for the pattern.  This function isn't yet exposed.
  substPats :: Proxy b -> AlphaCtx -> [ Dyn ] -> a -> a
  substPats p ctx us x = 
     case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName (Bn r j i)) | level ctx == j &&  i < length us ->
          case fromDynR r (us !!  i) of
            Just tm -> tm
            Nothing -> error "internal error: sort mismatch"
        _ -> substPatsR1 rep1 p ctx us x

-- | Reified class dictionary for 'Subst'.
data SubstD b a = SubstD {
  isvarD  :: a -> Maybe (SubstName a b),
  substD  ::  Name b -> b -> a -> a ,
  substsD :: [(Name b, b)] -> a -> a ,
  substPatD :: AlphaCtx -> b -> a -> a ,
  substPatsD :: Proxy b -> AlphaCtx -> [ Dyn ] -> a -> a
}

instance Subst b a => Sat (SubstD b a) where
  dict = SubstD isvar subst substs substPat substPats

substDefault :: Rep1 (SubstD b) a => Name b -> b -> a -> a
substDefault = substR1 rep1

substR1 :: R1 (SubstD b) a -> Name b -> b -> a -> a
substR1 (Data1 _dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substD w x y) rec kids
      in (to c z)
substR1 _               = \ _ _ c -> c

substsR1 :: R1 (SubstD b) a -> [(Name b, b)] -> a -> a
substsR1 (Data1 _dt cons) = \ s d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substsD w s) rec kids
      in (to c z)
substsR1 _               = \ _ c -> c

substPatsR1 :: R1 (SubstD b) a -> Proxy b -> AlphaCtx -> [ Dyn ] -> a -> a
substPatsR1 (Data1 _dt cons) = \ p ct s d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substPatsD w p ct s) rec kids
      in (to c z)
substPatsR1 _               = \ _ _ _ c -> c

substPatR1 :: R1 (SubstD b) a -> AlphaCtx -> b -> a -> a
substPatR1 (Data1 _dt cons) = \ ct s d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substPatD w ct s) rec kids
      in (to c z)
substPatR1 _               = \ _ _ c -> c


-- instances for types that change the de Bruijn levels of the context

instance (Rep order, Rep card, Alpha p, Alpha t, Subst b p, Subst b t) => Subst b (GenBind order card p t) where
   substPat c us (B p t) = 
     B (substPat (pat c) us p) (substPat (incr c) us t)
   substPats pr c us (B p t) = 
     B (substPats pr (pat c) us p) (substPats pr (incr c) us t)
  
instance (Alpha p, Alpha q, Subst b p, Subst b q) => Subst b (Rebind p q) where
   substPat     c us (R p q) = R (substPat     c us p) (substPat     (incr c) us q)
   substPats pr c us  (R p q) = R (substPats pr c us p) (substPats pr (incr c) us q)
   
instance (Alpha p, Subst b p) => Subst b (Rec p) where
   substPat     c us (Rec p) = Rec (substPat     (incr c) us p)
   substPats pr c us (Rec p) = Rec (substPats pr (incr c) us p)

instance (Alpha t, Subst b t) => Subst b (Embed t) where
   substPat c us (Embed x) = case mode c of
     Pat  -> Embed (substPat (term c) us x)
     Term -> error "substPat on Embed"
   substPats pr c us (Embed x) = case mode c of
     Pat  -> Embed (substPats pr (term c) us x)
     Term -> error "substPat on Embed"

instance (Alpha a, Subst b a) => Subst b (Shift a) where
  substPat      c us (Shift x) = Shift (substPat     (decr c) us x)
  substPats pr  c us (Shift x) = Shift (substPats pr (decr c) us x)

   




instance Subst b Int
instance Subst b Bool
instance Subst b ()
instance Subst b Char
instance Subst b Integer
instance Subst b Float
instance Subst b Double

instance Subst b AnyName
instance Rep a => Subst b (R a)
instance Rep a => Subst b (Name a)

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)



