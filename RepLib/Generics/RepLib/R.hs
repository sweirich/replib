{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    RankNTypes, TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, CPP, ImpredicativeTypes
 #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib.R
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Basic data structure and class for representation types
--
-----------------------------------------------------------------------------

module Generics.RepLib.R where

import Unsafe.Coerce

import Data.Type.Equality

-- | A value of type @R a@ is a representation of a type @a@.
data R a where
   Int      :: R Int
   Char     :: R Char
   Integer  :: R Integer
   Float    :: R Float
   Double   :: R Double
   Rational :: R Rational
   IOError  :: R IOError
   IO       :: (Rep a) => R a -> R (IO a)
   Arrow    :: (Rep a, Rep b) => R a -> R b -> R (a -> b)
   Data     :: DT -> [Con R a] -> R a
   Abstract :: DT -> R a
#if MIN_VERSION_base(4,7,0)
   Equal    :: (Rep a, Rep b) => R a -> R b -> R (a :~: b)
#else
   Equal    :: (Rep a, Rep b) => R a -> R b -> R (a :=: b)
#endif

-- | Representation of a data constructor includes an
-- embedding between the datatype and a list of other types
-- as well as the representation of that list of other types.
data Con r a where
  Con  :: Emb l a -> MTup r l -> Con r a

-- | An embedding between a list of types @l@ and
-- a datatype @a@, based on a particular data constructor.
-- The to function is a wrapper for the constructor, the
-- from function pattern matches on the constructor.
data Emb l a  = Emb { to     :: l -> a,
                      from   :: a -> Maybe l,
                      labels :: Maybe [String],
                      name   :: String,
                      fixity :: Fixity
                     }
                
-- | Fixity and precedence for data constructors
data Fixity =  Nonfix
                | Infix      { prec      :: Int }
                | Infixl     { prec      :: Int }
                | Infixr     { prec      :: Int }

-- | Information about a datatype, including its
-- fully qualified name and representation of
-- its type arguments.
data DT       = forall l. DT String (MTup R l)


-- | An empty list of types
data Nil = Nil
-- | Cons for a list of types
data a :*: l = a :*: l

infixr 7 :*:

-- | A heterogeneous list
data MTup r l where
    MNil   :: MTup r Nil
    (:+:)  :: (Rep a) => r a -> MTup r l -> MTup r (a :*: l)

infixr 7 :+:

-- | A class of representable types
class Rep a where rep :: R a

newtype IRep a r where IRep :: (Rep a => r) -> IRep a r

-- | Use a concrete @'R' a@ for a @'Rep' a@ dictionary
withRep :: forall a r. R a -> (Rep a => r) -> r
withRep = unsafeCoerce ((\a f -> f a) :: R a -> (R a -> r) -> r)

---withRep :: forall a r. R a -> (Rep a => r) -> r
---withRep rep c = withRep' rep (IRep c)

-- I think there's some contraint machinery that could hide the unsafeness here

------ Showing representations  (rewrite this with showsPrec?)

instance Show (R a) where
  show Int     = "Int"
  show Char    = "Char"
  show Integer = "Integer"
  show Float   = "Float"
  show Double  = "Double"
  show Rational= "Rational"
  show (IO t)  = "(IO " ++ show t ++ ")"
  show IOError = "IOError"
  show (Arrow r1 r2) =
     "(" ++ (show r1) ++ " -> " ++ (show r2) ++ ")"
  show (Data dt _) =
     "(Data" ++ show dt ++ ")"
  show (Abstract dt) =
     "(Abstract" ++ show dt ++ ")"
  show (Equal r1 r2) =
     "(Equal" ++ show r1 ++ " " ++ show r2 ++ ")"

instance Show DT where
  show (DT str reps) = str ++ show reps

instance Show (MTup R l) where
  show MNil         = ""
  show (r :+: MNil) = show r
  show (r :+: rs)   = " " ++ show r ++ show rs

instance Eq (R a) where
  _ == _ = True

instance Ord (R a) where
  compare _ _ = EQ  -- R a is a singleton

--- Representations for (some) Haskell Prelude types

instance Rep Int where rep = Int
instance Rep Char where rep = Char
instance Rep Integer where rep = Integer
instance Rep Float where rep = Float
instance Rep Double where rep = Double
instance Rep Rational where rep = Rational
instance Rep IOError where rep = IOError
instance Rep a => Rep (IO a) where rep = IO rep
instance (Rep a, Rep b) => Rep (a -> b) where rep = Arrow rep rep
#if MIN_VERSION_base(4,7,0)
instance (Rep a, Rep b) => Rep (a :~: b) where rep = Equal rep rep
#else
instance (Rep a, Rep b) => Rep (a :=: b) where rep = Equal rep rep
#endif

-- Unit

-- | Embedding for () constructor
rUnitEmb :: Emb Nil ()
rUnitEmb = Emb { to = \Nil -> (),
                 from = \() -> Just Nil,
                 labels = Nothing,
                 name = "()",
                 fixity = Nonfix }

-- | Representation of Unit type
rUnit :: R ()
rUnit = Data (DT "()" MNil)
        [Con rUnitEmb MNil]

instance Rep () where rep = rUnit

-- Tuples

instance (Rep a, Rep b) => Rep (a,b) where
   rep = rTup2

-- | Representation of tuple type
rTup2 :: forall a b. (Rep a, Rep b) => R (a,b)
rTup2 = let args =  ((rep :: R a) :+: (rep :: R b) :+: MNil) in
            Data (DT "(,)" args) [ Con rPairEmb args ]

-- | Embedding for pair constructor
rPairEmb :: Emb (a :*: b :*: Nil) (a,b)
rPairEmb =
  Emb { to = \( t1 :*: t2 :*: Nil) -> (t1,t2),
        from = \(a,b) -> Just (a :*: b :*: Nil),
        labels = Nothing,
        name = "(,)",
        fixity = Nonfix -- ???
      }

-- Lists
-- | Representation for list type
rList :: forall a. Rep a => R [a]
rList = Data (DT "[]" ((rep :: R a) :+: MNil))
             [ Con rNilEmb MNil, Con rConsEmb ((rep :: R a) :+: rList :+: MNil) ]

-- | Embedding of [] constructor
rNilEmb :: Emb Nil [a]
rNilEmb = Emb {   to   = \Nil -> [],
                  from  = \x -> case x of
                           (_:_) -> Nothing
                           []    -> Just Nil,
                  labels = Nothing,
                  name = "[]",
                  fixity = Nonfix
                 }

-- | Embedding of (:) constructor
rConsEmb :: Emb (a :*: [a] :*: Nil) [a]
rConsEmb =
   Emb {
            to   = (\ (hd :*: tl :*: Nil) -> (hd : tl)),
            from  = \x -> case x of
                    (hd : tl) -> Just (hd :*: tl :*: Nil)
                    []        -> Nothing,
            labels = Nothing,
            name = ":",
            fixity = Nonfix -- ???
          }

instance Rep a => Rep [a] where
   rep = rList

