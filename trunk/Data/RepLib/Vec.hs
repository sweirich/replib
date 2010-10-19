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

data Z
data S n

$(derive [''Z, ''S])

data SNat a where
  SZ :: SNat Z
  SS :: Rep n => SNat n -> SNat (S n)

toSNat :: forall n. R n -> (SNat n)
toSNat (Data (DT "Z" MNil) []) = 
       (unsafeCoerce# SZ :: SNat n)
toSNat (Data (DT "S" (rm :+: MNil)) []) = 
       (unsafeCoerce# (SS (toSNat rm)) :: SNat n)

type family Tup a n :: *
type instance Tup a Z = Nil
type instance Tup a (S m) = a :*: (Tup a m)

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
rVec :: forall a n. (Rep a, Rep n) => R (Vec a n)
rVec =
  Data (DT "Vec" ((rep :: R a) :+: (rep :: R n) :+: MNil))
       [ Con (vecEmb sn)
             (gMTup (rep :: R a) sn) ]  where
     sn :: SNat n 
     sn = toSNat rep

gMTup1 :: forall a n ctx. (Rep a, Rep n, Sat (ctx a)) => R a -> SNat n -> MTup ctx (Tup a n)
gMTup1 ra SZ = MNil
gMTup1 ra (SS sm) = dict :+: gMTup1 ra sm

rVec1 :: forall a n ctx. (Rep a, Rep n, Sat (ctx a)) => R1 ctx (Vec a n)
rVec1 =
  Data1 (DT "Vec" ((rep :: R a) :+: (rep :: R n) :+: MNil))
       [ Con (vecEmb sn)
             (gMTup1 (rep :: R a) sn) ]  where
     sn :: SNat n 
     sn = toSNat rep


instance (Rep a, Rep n) => Rep (Vec a n) where
     rep  = rVec
instance (Rep a, Rep n, Sat (ctx a)) => Rep1 ctx (Vec a n) where
     rep1 = rVec1
