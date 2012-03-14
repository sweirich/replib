{-# LANGUAGE 
             UndecidableInstances
           , GADTs
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , FlexibleInstances
           , TypeSynonymInstances
           , TypeOperators
 #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  RepLib.R1
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
--
-----------------------------------------------------------------------------

module Generics.RepLib.R1 where

import Generics.RepLib.R
import Data.Type.Equality

---------- Basic infrastructure

data R1 ctx a where
    Int1      :: R1 ctx Int
    Char1     :: R1 ctx Char
    Integer1  :: R1 ctx Integer
    Float1    :: R1 ctx Float
    Double1   :: R1 ctx Double
    Rational1 :: R1 ctx Rational
    IOError1  :: R1 ctx IOError
    IO1       :: (Rep a) => ctx a -> R1 ctx (IO a)
    Arrow1    :: (Rep a, Rep b) => ctx a -> ctx b -> R1 ctx (a -> b)
    Data1     :: DT -> [Con ctx a] -> R1 ctx a
    Abstract1 :: DT -> R1 ctx a
    Equal1    :: (Rep a, Rep b) => ctx a -> ctx b -> R1 ctx (a :=: b)
class Sat a where dict :: a

class Rep a => Rep1 ctx a where rep1 :: R1 ctx a

instance Show (R1 c a) where
    show Int1           = "Int1"
    show Char1          = "Char1"
    show Integer1       = "Integer1"
    show Float1         = "Float1"
    show Double1        = "Double1"
    show Rational1      = "Rational1"
    show IOError1       = "IOError1"
    show (IO1 cb)       = "(IO1 " ++ show (getRepC cb) ++ ")"
    show (Arrow1 cb cc) = "(Arrow1 " ++ show (getRepC cb) ++ " " ++ show (getRepC cc) ++ ")"
    show (Data1 dt _)   = "(Data1 " ++ show dt ++ ")"
    show (Abstract1 dt) = "(Abstract1 " ++ show dt ++ ")"
    show (Equal1 ca cb) = "(Equal1 " ++ show (getRepC ca) ++ " " ++ show (getRepC cb) ++ ")"

-- | Access a representation, given a proxy
getRepC :: Rep b => c b -> R b
getRepC _ = rep

-- | Transform a parameterized rep to a vanilla rep
toR :: R1 c a -> R a
toR Int1            = Int
toR Char1           = Char
toR Integer1        = Integer
toR Float1          = Float
toR Double1         = Double
toR Rational1       = Rational
toR IOError1        = IOError
toR (Arrow1 t1 t2)  = Arrow (getRepC t1) (getRepC t2)
toR (IO1 t1)        = IO (getRepC t1)
toR (Data1 dt cons) = (Data dt (map toCon cons))
  where toCon (Con emb rec) = Con emb (toRs rec)
        toRs           :: MTup c a -> MTup R a
        toRs MNil      = MNil
        toRs (c :+: l) = (getRepC c :+: toRs l)
toR (Abstract1 dt) = Abstract dt
toR (Equal1 ca cb) = Equal (getRepC ca) (getRepC cb)

---------------  Representations of Prelude types

instance Rep1 ctx Int      where rep1 = Int1
instance Rep1 ctx Char     where rep1 = Char1
instance Rep1 ctx Integer  where rep1 = Integer1
instance Rep1 ctx Float    where rep1 = Float1
instance Rep1 ctx Double   where rep1 = Double1
instance Rep1 ctx IOError  where rep1 = IOError1
instance Rep1 ctx Rational where rep1 = Rational1
instance (Rep a, Sat (ctx a)) =>
         Rep1 ctx (IO a)   where rep1 = IO1 dict
instance (Rep a, Rep b, Sat (ctx a), Sat (ctx b)) =>
         Rep1 ctx (a -> b) where rep1 = Arrow1 dict dict

instance (Rep a, Rep b, Sat (ctx a), Sat (ctx b)) =>
         Rep1 ctx (a :=: b) where rep1 = Equal1 dict dict

-- Data structures

-- unit
instance Rep1 ctx ()   where
 rep1 = Data1 (DT "()" MNil)
        [Con rUnitEmb MNil]

-- pairs
rTup2_1 :: forall a b ctx. (Rep a, Rep b) => ctx a -> ctx b -> R1 ctx (a,b)
rTup2_1 ca cb =
  case (rep :: R (a,b)) of
     Data rdt _ -> Data1 rdt
       [Con rPairEmb (ca :+: cb :+: MNil)]

instance (Rep a, Sat (ctx a), Rep b, Sat (ctx b)) => Rep1 ctx (a,b) where
  rep1 = rTup2_1 dict dict


-- Lists
rList1 :: forall a ctx.
  Rep a => ctx a -> ctx [a] -> R1 ctx [a]
rList1 ca cl = Data1 (DT "[]" ((rep :: R a) :+: MNil))
                  [ rCons1, rNil1 ] where
   rNil1  :: Con ctx [a]
   rNil1  = Con rNilEmb MNil

   rCons1 :: Con ctx [a]
   rCons1 = Con rConsEmb (ca :+: cl :+: MNil)

instance (Rep a, Sat (ctx a), Sat (ctx [a])) => Rep1 ctx [a] where
  rep1 = rList1 dict dict

