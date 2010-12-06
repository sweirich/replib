{-# LANGUAGE TemplateHaskell, ScopedTypeVariables,
    FlexibleInstances, FlexibleContexts,
    UndecidableInstances, MultiParamTypeClasses,
    TypeFamilies, EmptyDataDecls, TypeOperators, GADTs, MagicHash #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | A definition of length-indexed vectors plus their representations
module Data.RepLib.Vec (
       Z,rZ,rZ1,S,rS,rS1,
       SNat(..),toSNat,
       Vec(..),rVec,rVec1
       )
where

import Data.RepLib
import GHC.Base (unsafeCoerce#)

-- | Natural numbers
data Z 
data S n

$(derive [''Z, ''S])

-- | Singleton GADT for natural numbers
data SNat a where
  SZ :: SNat Z
  SS :: Rep n => SNat n -> SNat (S n)

-- | Convert a representation of a natural number into a singleton
-- WARNING: Only call this on *numbers*
-- It demonstrates a deficiency of reps for void/abstract datatypes
toSNat :: forall n. R n -> (SNat n)
toSNat r = 
  case gcast (SZ :: SNat n) of 
    Just sz -> sz
    Nothing -> case gcast (SS (toSNat rm)) of 
                 
toSNat r@(Data (DT "Data.RepLib.Vec.Z" MNil) []) = 
    case gcastR r rZ SZ of 
      Just sz -> sz
      Nothing -> error "BUG"
toSNat r@(Data (DT "Data.RepLib.Vec.S" (rm :+: MNil)) []) = 
    case gcastR r (rS (toSNat rm)) of
       Just i -> i
       Nothing -> error "impossible"
--       (unsafeCoerce# (SS (toSNat rm)) :: SNat n)
toSNat _ = error "BUG: toSNat can only be called with the representation of a natural number"


-- | a tuple of n values of type a
type family Tup a n :: *
type instance Tup a Z = Nil
type instance Tup a (S m) = a :*: (Tup a m)

-- | a vector of n values of type a
data Vec a n where
 VNil  :: Vec a Z
 VCons :: Rep n => a -> Vec a n -> Vec a (S n)

gTo :: forall a n . Rep n => SNat n -> (Tup a n) -> (Vec a n)
gTo s = case s of 
  SZ -> \Nil -> VNil
  SS sm -> \(a :*: l ) -> VCons a (gTo sm l)
gFrom :: forall a n. Rep n => SNat n -> (Vec a n) -> Maybe (Tup a n)
gFrom SZ = \ VNil -> Just Nil
gFrom (SS sm) = \ (VCons a tl) -> do 
     tl' <- gFrom sm tl  
     return (a :*: tl')

gMTup :: forall a n. (Rep a, Rep n) => R a -> SNat n -> MTup R (Tup a n)
gMTup ra SZ = MNil
gMTup ra (SS sm) = ra :+: gMTup ra sm

vecEmb :: forall a n . Rep n => SNat n -> Emb (Tup a n) (Vec a n)
vecEmb sn =   (Emb { to = gTo sn, 
                    from = gFrom sn, 
                    labels = Nothing, 
                    name = "", 
                    fixity = Nonfix })

-- | Rep of the vector type
rVec :: forall a n. (Rep a, Rep n) => R (Vec a n)
rVec =
  Data (DT "Data.RepLib.Vec.Vec" ((rep :: R a) :+: (rep :: R n) :+: MNil))
       [ Con (vecEmb sn)
             (gMTup (rep :: R a) sn) ]  where
     sn :: SNat n 
     sn = toSNat rep

gMTup1 :: forall a n ctx. (Rep a, Rep n, Sat (ctx a)) => R a -> SNat n -> MTup ctx (Tup a n)
gMTup1 ra SZ = MNil
gMTup1 ra (SS sm) = dict :+: gMTup1 ra sm

rVec1 :: forall a n ctx. (Rep a, Rep n, Sat (ctx a)) => R1 ctx (Vec a n)
rVec1 =
  Data1 (DT "Data.RepLib.Vec.Vec" ((rep :: R a) :+: (rep :: R n) :+: MNil))
       [ Con (vecEmb sn)
             (gMTup1 (rep :: R a) sn) ]  where
     sn :: SNat n 
     sn = toSNat rep


instance (Rep a, Rep n) => Rep (Vec a n) where
     rep  = rVec
instance (Rep a, Rep n, Sat (ctx a)) => Rep1 ctx (Vec a n) where
     rep1 = rVec1
