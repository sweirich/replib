-- OPTIONS -fglasgow-exts -fallow-undecidable-instances
{-# LANGUAGE TemplateHaskell, UndecidableInstances, GADTs #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-----------------------------------------------------------------------------
--
-- Module      :  RepLib.PreludeLib
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
-----------------------------------------------------------------------------


-- | The module PreludeLib contains generic operations to derive members of the standard
-- prelude classess: Eq, Bounded, Compare, Show  (TODO: add Enum and Read)
--
-- Although these classes may already be automatically derived via the
-- "deriving" mechanism, this module is included for two reasons:
--
--  * Deriving only works when datatypes are defined. This library
-- allows instances of these classes to be generated anywhere. For
-- example, suppose some other module contains the definition of the
-- datatype T and exposes all of its constructors, but, frustratingly,
-- does not derive an instance of the Show class.
--
--   You could define a Show instance of 'T' in your own module with the
--   following code:
--
--   > import RepLib
--   >
--   > (repr1 ''T)  -- make the Rep1 instance of T available
--   >
--   > instance Show T where
--   >   showsPrec = showsPrecR1 rep1   -- showsPrecR1 is defined in this module
													 --
--  * This library also serves as a model for generic functions that are
-- slight modifications to these prelude operations. For example, if you
-- wanted to define reverse lexicographic ordering or an XML pretty
-- printer for datatypes, you might start here. This library is also a
-- good place to start learning how to define your own generic
-- operations, because the behavior of these operations should match the
-- deriving mechanism specified by Haskell 98.
--
module Generics.RepLib.PreludeLib (
  EqD,
  eqR1,
  OrdD,
  compareR1,
  BoundedD,
  minBoundR1,
  maxBoundR1,
  ShowD,
  showsPrecR1
)where

import Generics.RepLib.R
import Generics.RepLib.R1
import Generics.RepLib.RepAux

--- Polymorphic equality -------------------------

data EqD a = EqD { eqD :: a -> a -> Bool }
instance Eq a => Sat (EqD a) where
    dict = EqD (==)

-- | Polymorphic equality, given an R1 representation
eqR1 :: R1 EqD a -> a -> a -> Bool
eqR1 Int1           = (==)
eqR1 Char1          = (==)
eqR1 Integer1       = (==)
eqR1 Float1         = (==)
eqR1 Double1        = (==)
eqR1 (Data1 _ cons) = \x y ->
   let loop (Con rcd rec : rest) =
         case (from rcd x, from rcd y) of
          (Just p1, Just p2) -> eqRL1 rec p1 p2
          (Nothing, Nothing) -> loop rest
          (_,_) -> False
   in loop cons
eqR1 r1  = error ("eqR1 undefined for " ++ show r1)

eqRL1 :: MTup EqD l -> l -> l -> Bool
eqRL1 MNil Nil Nil = True
eqRL1 (r :+: rl) (p1 :*: t1) (p2 :*: t2) =
  eqD r p1 p2 && eqRL1 rl t1 t2


------------ Ord -------------------------------

-- compare :: a -> a -> Ordering is a minimal instance
-- of the Ord class

data OrdD a = OrdD { compareD :: a -> a -> Ordering }

instance Ord a => Sat (OrdD a) where
    dict = OrdD { compareD = compare }

lexord         :: Ordering -> Ordering -> Ordering
lexord LT _    =  LT
lexord EQ ord  =  ord
lexord GT _    =  GT

-- | Minimal completion of the Ord class
compareR1 :: R1 OrdD a -> a -> a -> Ordering
compareR1 Int1  = compare
compareR1 Char1 = compare
compareR1 (Data1 _ cons) = \ x y ->
             let loop (Con emb rec : rest) =
                     case (from emb x, from emb y) of
                        (Just t1, Just t2) -> compareTup rec t1 t2
                        (Just _ , Nothing) -> LT
                        (Nothing, Just _ ) -> GT
                        (Nothing, Nothing) -> loop rest
             in loop cons
compareR1 r1 = error ("compareR1 not supported for " ++ show r1)

compareTup :: MTup OrdD l -> l -> l -> Ordering
compareTup MNil Nil Nil = EQ
compareTup (x :+: xs) (y :*: ys) (z :*: zs) =
    lexord (compareD x y z) (compareTup xs ys zs)

------------ Bounded ------------------------------

data BoundedD a = BoundedD { minBoundD :: a, maxBoundD :: a }

instance Bounded a => Sat (BoundedD a) where
    dict = BoundedD { minBoundD = minBound, maxBoundD = maxBound }

-- | To generate the Bounded class
minBoundR1 :: R1 BoundedD a -> a
minBoundR1 Int1  = minBound
minBoundR1 Char1 = minBound
minBoundR1 (Data1 _ (Con emb rec:_)) = to emb (fromTup minBoundD rec)
minBoundR1 r1     = error ("minBoundR1 not supported for " ++ show r1)

-- | To generate the Bounded class
maxBoundR1 :: R1 BoundedD a -> a
maxBoundR1 Int1  = maxBound
maxBoundR1 Char1 = maxBound
maxBoundR1 (Data1 _ cons) =
   case last cons of (Con emb rec) -> to emb (fromTup maxBoundD rec)
maxBoundR1 r1     = error ("maxBoundR1 not supported for " ++ show r1)

-------------------- Show -------------------------------------
-- Inspired by the Generic Haskell implementation
-- Current version doesn't correctly handle fixity

data ShowD a = ShowD { showsPrecD :: Int -> a -> ShowS }

instance Show a => Sat (ShowD a) where
	 dict = ShowD { showsPrecD = showsPrec }

getFixity :: Emb a b -> Int
getFixity c = case fixity c of
				    Nonfix   -> 0
				    Infix  i -> i
				    Infixl i -> i
				    Infixr i -> i

-- | Minimal completion of the show class
showsPrecR1 :: R1 ShowD a ->
               Int  -> -- precendence level
               a    -> -- value to be shown
               ShowS
showsPrecR1 (Data1 (DT _ _) cons) = \p v ->
	case (findCon cons v) of
      Val c rec kids ->
          case (labels c) of
            Just labs -> par $ showString (name c) .
                               showString "{" .
	 		       showRecord rec kids labs .
			       showString "}"
            Nothing   -> par $ showString (name c) .
                               maybespace .
                               showKids rec kids
          where par        = showParen (p > p' && conArity > 0)
                p'         = getFixity c
                maybespace = if conArity == (0::Int) then id else (' ':)
                conArity   = foldr_l (\_ _ i -> 1 + i) 0 rec kids

                showKid :: ShowD a -> a -> ShowS
                showKid r x = showsPrecD r (p'+1) x

                showRecord ::  MTup ShowD l -> l -> [String] -> ShowS
                showRecord (r :+: MNil) (a :*: Nil) (l : _) = showString l . ('=':) . showKid r a
                showRecord (r :+: rs) (a :*: aa) (l : ls) =
                    showString l . ('=':) . showKid r a . showString (", ") . showRecord rs aa ls
                showRecord _ _ _ = error ("Incorrect representation: " ++
				          "wrong number of labels in record type")

                showKids :: MTup ShowD l -> l -> ShowS
                showKids MNil Nil = id
                showKids (r :+: MNil) (x :*: Nil) = showsPrecD r (p'+1) x
                showKids (r :+: cl)   (x :*: l)   = showsPrecD r (p'+1) x . (' ':) . (showKids cl l)

showsPrecR1 Int1      = showsPrec
showsPrecR1 Char1     = showsPrec
showsPrecR1 Integer1  = showsPrec
showsPrecR1 Float1    = showsPrec
showsPrecR1 Double1   = showsPrec
showsPrecR1 r1        = error ("showsPrecR1 not supported for " ++ show r1)


