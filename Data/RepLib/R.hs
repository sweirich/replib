{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables
 #-} 
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib.R
-- Copyright   :  (c) The University of Pennsylvania, 2006
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
--
-----------------------------------------------------------------------------

module Data.RepLib.R where

import Data.List


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


data DT       = forall l. DT String (MTup R l)
data Con r a  = forall l. Con (Emb l a) (MTup r l)


data Nil = Nil 
data a :*: l = a :*: l
infixr 7 :*:

data MTup r l where
    MNil   :: MTup ctx Nil
    (:+:)  :: (Rep a) => r a -> MTup r l -> MTup r (a :*: l)

infixr 7 :+:

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


--- Representations for Haskell Prelude types

instance Rep Int where rep = Int
instance Rep Char where rep = Char
instance Rep Double where rep = Double
instance Rep Rational where rep = Rational
instance Rep Float where rep = Float
instance Rep Integer where rep = Integer
instance Rep a => Rep (IO a) where rep = IO rep
instance Rep IOError where rep = IOError
instance (Rep a, Rep b) => Rep (a -> b) where rep = Arrow rep rep

-- Booleans
{-
rTrueEmb :: Emb Nil Bool
rTrueEmb =  Emb { to = \Nil -> True,
                  from = \x -> if x then Just Nil else Nothing,
                  labels = Nothing,
                  name = "True",
						fixity = Nonfix
                 }

rFalseEmb :: Emb Nil Bool
rFalseEmb =  Emb { to = \Nil -> False,
                   from = \x -> if x then Nothing else Just Nil,
                   labels = Nothing,
                   name = "False",
						 fixity = Nonfix
                  }

rBool :: R Bool
rBool = Data (DT "Bool" MNil) [Con rTrueEmb, Con rFalseEmb]

instance Rep Bool where rep = rBool
 -}
      
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

{-
-- Maybe representation

rJust :: Rep a => Con (Maybe a)
rJust = Con (rJustEmb)

rJustEmb :: Emb (a :*: Nil) (Maybe a)
rJustEmb = Emb 
  { to   = (\(x :*: Nil) -> Just x),
    from  = \x -> case x of 
            (Just y) -> Just (y :*: Nil)
            Nothing  -> Nothing,
    labels = Nothing, 
    name = "Just"
   }

rNothing :: Con (Maybe a)
rNothing = Con rNothingEmb

rNothingEmb :: Emb Nil (Maybe a)
rNothingEmb = Emb 
  { to   = \Nil -> Nothing,
    from  = \x -> case x of 
             Nothing -> Just Nil
             _       -> Nothing,
    labels = Nothing,
    name = "Nothing"
  }

rMaybe :: forall a. Rep a => R (Maybe a)
rMaybe = Data (DT "Maybe" ((rep :: R a) :+: MNil))
              [rJust, rNothing]

instance Rep a => Rep (Maybe a) where
   rep = rMaybe
-}
-- Ordering
-- Either

