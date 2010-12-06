{-# LANGUAGE TemplateHaskell, UndecidableInstances, MagicHash,
    ScopedTypeVariables, GADTs, Rank2Types
  #-} 
-----------------------------------------------------------------------------
-- |
-- Module      :  RepAux
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Auxiliary operations to aid in the definition of type-indexed functions
--
-----------------------------------------------------------------------------
module Data.RepLib.RepAux (
  -- ** Casting operations 
  eqR, cast, castR, gcast, gcastR,

  -- ** Comparison
  compareR,

  -- ** Operations for heterogeneous lists 
  findCon, Val(..), foldl_l, foldr_l, map_l, mapQ_l, mapM_l, fromTup, fromTupM, toList,

  -- ** SYB style operations (Rep)
  Traversal, Query, MapM, 
  gmapT, gmapQ, gmapM,

  -- ** SYB style operations (Rep1)
  Traversal1, Query1, MapM1,
  gmapT1, gmapQ1, gmapM1,

  -- ** SYB Reloaded
  Typed(..),Spine(..), toSpine, fromSpine
) where

import Data.RepLib.R
import Data.RepLib.R1
import GHC.Base (unsafeCoerce#)


------ Casting

-- | Determine if two reps are for the same type
eqR :: R a -> R b -> Bool
eqR Int Int = True
eqR Char Char = True
eqR Float Float = True
eqR Integer Integer = True
eqR Double Double = True
eqR (IO t1) (IO t2) = eqR t1 t2
eqR IOError IOError = True
eqR (Arrow t1 t2) (Arrow s1 s2) = eqR t1 s1 && eqR t2 s2
eqR (Data rc1 _) (Data rc2 _) = eqDT rc1 rc2
eqR (Abstract rc1) (Abstract rc2) = eqDT rc1 rc2
eqR _ _ = False

eqDT :: DT -> DT -> Bool
eqDT (DT str1 rt1) (DT str2 rt2) = str1 == str2 && eqRTup rt1 rt2

instance Eq DT where
   (==) = eqDT

eqRTup :: MTup R t1 -> MTup R t2 -> Bool
eqRTup MNil MNil = True
eqRTup (r1 :+: rt1) (r2 :+: rt2) = eqR r1 r2 && eqRTup rt1 rt2

-- | The type-safe cast operation, explicit arguments
castR :: R a -> R b -> a -> Maybe b
castR (ra::R a) (rb::R b) = 
    if eqR ra rb then \(x::a) -> Just (unsafeCoerce# x::b) else \x -> Nothing

-- | The type-safe cast operation, implicit arguments
cast :: forall a b. (Rep a, Rep b) => a -> Maybe b
cast x = castR (rep :: R a) (rep :: R b) x

-- | Leibniz equality between types, explicit representations
gcastR :: forall a b c. R a -> R b -> c a -> Maybe (c b)
gcastR ra rb = if eqR ra rb
        then \(x :: c a) -> Just (unsafeCoerce# x :: c b)
        else \x -> Nothing

-- | Leibniz equality between types, implicit representations
gcast :: forall a b c. (Rep a, Rep b) => c a -> Maybe (c b)
gcast = gcastR (rep :: R a) (rep :: R b)      

---------- (Heterogeneous) Ordering -------------------------

-- | Heterogeneous Ordering    
compareR :: R a -> R b -> Ordering 
compareR Int Int = EQ
compareR Int _   = LT
compareR _   Int = GT
compareR Char Char = EQ
compareR Char _  = LT
compareR _ Char  = GT
compareR Integer Integer = EQ
compareR Integer _  = LT
compareR _ Integer  = GT
compareR Float Float = EQ
compareR Float _  = LT
compareR _ Float  = GT
compareR Rational Rational = EQ
compareR Rational _  = LT
compareR _ Rational  = GT
compareR IOError IOError = EQ
compareR IOError _  = LT
compareR _ IOError  = GT
compareR (IO r1) (IO r2) = compareR r1 r2
compareR (IO _) _  = LT
compareR _ (IO _)  = GT
compareR (Arrow r1 r2) (Arrow r3 r4) =
   case compareR r1 r3 of 
      EQ -> compareR r2 r4
      ord -> ord
compareR (Arrow _ _) _  = LT
compareR _ (Arrow _ _)  = GT
compareR (Data dt1 _) (Data dt2 _) = 
   compare dt1 dt2
compareR (Data _ _) _ = LT
compareR _ (Data _ _) = GT
compareR (Abstract dt1) (Abstract dt2) = 
   compare dt1 dt2
compareR (Abstract _) _ = LT
compareR _ (Abstract _) = GT

instance Ord DT where
  compare (DT str1 reps1) (DT str2 reps2) = 
    case compare str1 str2 of 
       EQ -> compareMTup reps1 reps2
       other -> other

compareMTup :: MTup R l -> MTup R l' -> Ordering
compareMTup MNil MNil = EQ
compareMTup MNil _    = LT
compareMTup _    MNil = GT
compareMTup (a :+: as) (b :+: bs) = 
  case compareR a b of 
     EQ -> compareMTup as bs
     other -> other  



--------- Basic instances and library operations for heterogeneous lists ---------------

-- | A datastructure to store the results of findCon
data Val ctx a = forall l.  Val (Emb l a) (MTup ctx l) l

-- | Given a list of constructor representations for a datatype, 
-- determine which constructor formed the datatype.
findCon :: [Con ctx a] -> a -> Val ctx a
findCon (Con rcd rec : rest) x = case (from rcd x) of 
       Just ys -> Val rcd rec ys
       Nothing -> findCon rest x

-- | A fold right operation for heterogeneous lists, that folds a function 
-- expecting a type type representation across each element of the list.
foldr_l :: (forall a. Rep a => ctx a -> a -> b -> b) -> b 
            -> (MTup ctx l) -> l -> b
foldr_l f b MNil Nil = b
foldr_l f b (ca :+: cl) (a :*: l) = f ca a (foldr_l f b cl l ) 

-- | A fold left for heterogeneous lists
foldl_l :: (forall a. Rep a => ctx a -> b -> a -> b) -> b 
            -> (MTup ctx l) ->  l -> b
foldl_l f b MNil Nil = b
foldl_l f b (ca :+: cl) (a :*: l) = foldl_l f (f ca b a) cl l 

-- | A map for heterogeneous lists
map_l :: (forall a. Rep a => ctx a -> a -> a) 
           -> (MTup ctx l) ->  l ->  l
map_l f MNil Nil = Nil
map_l f (ca :+: cl) (a :*: l) = (f ca a) :*: (map_l f cl l)

-- | Transform a heterogeneous list in to a standard list
mapQ_l :: (forall a. Rep a => ctx a -> a -> r) -> MTup ctx l -> l -> [r]
mapQ_l q MNil Nil = []
mapQ_l q (r :+: rs) (a :*: l) = q r a : mapQ_l q rs l

-- | mapM for heterogeneous lists
mapM_l :: (Monad m) => (forall a. Rep a => ctx a -> a -> m a) -> MTup ctx l -> l -> m l
mapM_l f MNil Nil = return Nil
mapM_l f (ca :+: cl) (a :*: l) = do 
  x1 <- f ca a
  x2 <- mapM_l f cl l
  return (x1 :*: x2)

-- | Generate a heterogeneous list from metadata
fromTup :: (forall a. Rep a => ctx a -> a) -> MTup ctx l -> l
fromTup f MNil = Nil
fromTup f (b :+: l) = (f b) :*: (fromTup f l)

-- | Generate a heterogeneous list from metadata, in a monad
fromTupM :: (Monad m) => (forall a. Rep a => ctx a -> m a) -> MTup ctx l -> m l
fromTupM f MNil = return Nil
fromTupM f (b :+: l) = do hd <- f b
                          tl <- fromTupM f l
                          return (hd :*: tl)

-- | Generate a normal lists from metadata
toList :: (forall a. Rep a => ctx a -> b) -> MTup ctx l -> [b]
toList f MNil = []
toList f (b :+: l) = f b : toList f l

---------------------  SYB style operations --------------------------

-- | A SYB style traversal
type Traversal = forall a. Rep a => a -> a

-- | Map a traversal across the kids of a data structure 
gmapT :: forall a. Rep a => Traversal -> a -> a
gmapT t = 
  case (rep :: R a) of 
   (Data dt cons) -> \x -> 
     case (findCon cons x) of 
      Val emb reps ys -> to emb (map_l (const t) reps ys)
   _ -> id


-- | SYB style query type
type Query r = forall a. Rep a => a -> r 

gmapQ :: forall a r. Rep a => Query r -> a -> [r]
gmapQ q =
  case (rep :: R a) of 
    (Data dt cons) -> \x -> case (findCon cons x) of 
		Val emb reps ys -> mapQ_l (const q) reps ys
    _ -> const []


-- | SYB style monadic map type
type MapM m = forall a. Rep a => a -> m a

gmapM   :: forall a m. (Rep a, Monad m) => MapM m -> a -> m a
gmapM m = case (rep :: R a) of
   (Data dt cons) -> \x -> case (findCon cons x) of 
     Val emb reps ys -> do l <- mapM_l (const m) reps ys
                           return (to emb l)
   _ -> return 


-------------- Generalized  SYB ops ---------------------------

type Traversal1 ctx = forall a. Rep a => ctx a -> a -> a
gmapT1 :: forall a ctx. (Rep1 ctx a) => Traversal1 ctx -> a -> a 
gmapT1 t = 
  case (rep1 :: R1 ctx a) of 
   (Data1 dt cons) -> \x -> 
     case (findCon cons x) of 
      Val emb recs kids -> to emb (map_l t recs kids)
   _ -> id

type Query1 ctx r = forall a. Rep a => ctx a -> a -> r
gmapQ1 :: forall a ctx r. (Rep1 ctx a) => Query1 ctx r -> a -> [r]
gmapQ1 q  =
  case (rep1 :: R1 ctx a) of 
    (Data1 dt cons) -> \x -> case (findCon cons x) of 
		Val emb recs kids -> mapQ_l q recs kids
    _ -> const []

type MapM1 ctx m = forall a. Rep a => ctx a -> a -> m a
gmapM1  :: forall a ctx m. (Rep1 ctx a, Monad m) => MapM1 ctx m -> a -> m a
gmapM1 m = case (rep1 :: R1 ctx a) of
   (Data1 dt cons) -> \x -> case (findCon cons x) of 
     Val emb rec ys -> do l <- mapM_l m rec ys
                          return (to emb l)
   _ -> return 

-------------- Spine from SYB Reloaded ---------------------------

data Typed a = a ::: R a 
infixr 7 :::

data Spine a where
	 Constr :: a -> Spine a
	 (:<>)  :: Spine (a -> b) -> Typed a -> Spine b

toSpineR :: R a -> a -> Spine a
toSpineR (Data _ cons) a = 
	 case (findCon cons a) of 
	    Val emb reps kids -> toSpineRl reps kids (to emb)
toSpineR _ a = Constr a

toSpineRl :: MTup R l -> l -> (l -> a) -> Spine a 
toSpineRl MNil Nil into = Constr (into Nil)
toSpineRl (ra :+: rs) (a :*: l) into = 
	 (toSpineRl rs l into') :<> (a ::: ra)
		  where into' tl1 x1 = into (x1 :*: tl1)

toSpine :: Rep a => a -> Spine a 
toSpine = toSpineR rep

fromSpine :: Spine a -> a
fromSpine (Constr x) = x
fromSpine (x :<> (y:::_)) = fromSpine x y

