{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables
 #-} 
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib.R
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Basic data structure and class for representation types
--
-----------------------------------------------------------------------------

module Data.RepLib.R where

import Data.List

-- | A value of type @R a@ is a representation of a type @a@. 
data R a where
   Int     :: R Int
   Char    :: R Char 
   Integer :: R Integer
   Float   :: R Float
   Double  :: R Double
   Rational:: R Rational
   IOError :: R IOError
   IO      :: (Rep a) => R a -> R (IO a)
   Arrow   :: (Rep a, Rep b) => R a -> R b -> R (a -> b)
   Data    :: DT -> [Con R a] -> R a 

-- | Representation of a data constructor includes an
-- embedding between the datatype and a list of other types
-- as well as the representation of that list of other types.
data Con r a  = forall l. Con (Emb l a) (MTup r l)

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

-- | A Class of representatble types
class Rep a where rep :: R a

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

instance Show DT where
  show (DT str reps) = str ++ show reps 
  
instance Show (MTup R l) where
  show MNil         = ""
  show (r :+: MNil) = show r 
  show (r :+: rs)   = " " ++ show r ++ show rs

instance Eq (R a) where
	 r1 == r2 = True


--- Representations for (some) Haskell Prelude types

instance Rep Int where rep = Int
instance Rep Char where rep = Char
instance Rep Double where rep = Double
instance Rep Rational where rep = Rational
instance Rep Float where rep = Float
instance Rep Integer where rep = Integer
instance Rep a => Rep (IO a) where rep = IO rep
instance Rep IOError where rep = IOError
instance (Rep a, Rep b) => Rep (a -> b) where rep = Arrow rep rep
      
-- Unit

rUnitEmb :: Emb Nil ()
rUnitEmb = Emb { to = \Nil -> (), 
                 from = \() -> Just Nil, 
			        labels = Nothing, 
                 name = "()", 
                 fixity = Nonfix }

rUnit :: R ()
rUnit = Data (DT "()" MNil) 
        [Con rUnitEmb MNil]
 
instance Rep () where rep = rUnit

-- Tuples 

instance (Rep a, Rep b) => Rep (a,b) where
   rep = rTup2

rTup2 :: forall a b. (Rep a, Rep b) => R (a,b)
rTup2 = let args =  ((rep :: R a) :+: (rep :: R b) :+: MNil) in
			Data (DT "," args) [ Con rPairEmb args ]

rPairEmb :: Emb (a :*: b :*: Nil) (a,b)
rPairEmb = 
  Emb { to = \( t1 :*: t2 :*: Nil) -> (t1,t2),
        from = \(a,b) -> Just (a :*: b :*: Nil),
        labels = Nothing, 
        name = "(,)",
        fixity = Nonfix -- ???
      }

-- Lists
rList :: forall a. Rep a => R [a]
rList = Data (DT "[]" ((rep :: R a) :+: MNil))
             [ Con rNilEmb MNil, Con rConsEmb ((rep :: R a) :+: rList :+: MNil) ]

rNilEmb :: Emb Nil [a]
rNilEmb = Emb {   to   = \Nil -> [],
                  from  = \x -> case x of 
                           (x:xs) -> Nothing
                           []     ->  Just Nil,
                  labels = Nothing, 
                  name = "[]",
		  fixity = Nonfix
                 }

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

