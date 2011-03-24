{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables,
    MultiParamTypeClasses, FlexibleContexts, FlexibleInstances,
    TypeSynonymInstances, GADTs
  #-}


-----------------------------------------------------------------------------
-- |
-- Module      :  RepLib.Lib
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A library of type-indexed functions
--
-----------------------------------------------------------------------------
module Generics.RepLib.Lib (
  -- * Available for all representable types
  subtrees, deepSeq, rnf,

  -- * Specializable type-indexed functions
  GSum(..),
  Zero(..),
  Generate(..),
  Enumerate(..),
  Shrink(..),
  Lreduce(..),
  Rreduce(..),

  -- * Generic operations based on Fold
  Fold(..),
  crush, gproduct, gand, gor, flatten, count, comp, gconcat, gall, gany, gelem,

  -- * Auxiliary types and generators for derivable classes
  GSumD(..), ZeroD(..), GenerateD(..), EnumerateD(..), ShrinkD(..), LreduceD(..), RreduceD(..),
  rnfR, deepSeqR, gsumR1, zeroR1, generateR1, enumerateR1, lreduceR1, rreduceR1

) where

import Generics.RepLib.R
import Generics.RepLib.R1
import Generics.RepLib.RepAux
import Generics.RepLib.PreludeReps()

------------------- Subtrees --------------------------
-- there is no point in using R1 for subtrees
-- From Mark P. Jones, Functional programming with
-- overloading and higher-order polymorphism
-- Also the same function as "children" from SYB III

-- | Produce all children of a datastructure with the same type.
-- Note that subtrees is available for all representable types. For those that
-- are not recursive datatypes, subtrees will always return the
-- empty list. But, these trivial instances are convenient to have
-- for the Shrink operation below.

subtrees :: forall a. Rep a => a -> [a]
subtrees x = [y | Just y <- gmapQ (cast :: Query (Maybe a)) x]

-------------------- DeepSeq -----------------------


-- | Recursively force the evaluation of the first
-- argument. For example,
-- @
--  deepSeq ( x , y ) z where
--    x = ...
--    y = ...
-- @
-- will evaluate both @x@ and @y@ then return @z@
deepSeq :: Rep a => a -> b -> b
deepSeq = deepSeqR rep

-- | Force the evaluation of *datatypes* to their normal
-- forms. Other types are left alone and not forced.
rnf :: Rep a => a -> a
rnf = rnfR rep


rnfR :: R a -> a -> a
rnfR (Data dt cons) x =
    case (findCon cons x) of
      Val emb reps args -> to emb (map_l rnfR reps args)
rnfR _ x = x

deepSeqR :: R a -> a -> b -> b
deepSeqR (Data dt cons) = \x ->
    case (findCon cons x) of
      Val _ reps args -> foldl_l (\ra bb a -> (deepSeqR ra a) . bb) id reps args
deepSeqR _ = seq

deepSeq_l :: MTup R l -> l -> b -> b
deepSeq_l MNil Nil = id
deepSeq_l (rb :+: rs) (b :*: bs) = deepSeqR rb b . deepSeq_l rs bs

------------------- Generic Sum ----------------------
-- | Add together all of the @Int@s in a datastructure
-- For example:
-- gsum ( 1 , True, ("a", Maybe 3, []) , Nothing)
-- 4
--
class Rep1 GSumD a => GSum a where
   gsum :: a -> Int
   gsum = gsumR1 rep1

data GSumD a = GSumD { gsumD :: a -> Int }

gsumR1 :: R1 GSumD a -> a -> Int
gsumR1 Int1              x  = x
gsumR1 (Arrow1 r1 r2)    f  = error "urk"
gsumR1 (Data1 dt cons)   x  =
  case (findCon cons x) of
      Val emb rec kids ->
        foldl_l (\ca a b -> (gsumD ca b) + a) 0 rec kids
gsumR1 _                 x  = 0

instance GSum a => Sat (GSumD a) where
   dict = GSumD gsum

instance GSum Float
instance GSum Int
instance GSum Bool
instance GSum ()
instance GSum Integer
instance GSum Char
instance GSum Double
instance (GSum a, GSum b) => GSum (a,b)
instance (GSum a) => GSum [a]

-------------------- Zero ------------------------------
-- | Create a zero element of a type
-- @
-- ( zero  :: ((Int, Maybe Int), Float))
-- ((0, Nothing), 0.0)
-- @
class (Rep1 ZeroD a) => Zero a where
    zero :: a
    zero = zeroR1 rep1

data ZeroD a = ZD { zeroD :: a }

instance Zero a => Sat (ZeroD a) where
    dict = ZD zero

zeroR1 :: R1 ZeroD a -> a
zeroR1 Int1 = 0
zeroR1 Char1 = minBound
zeroR1 (Arrow1 z1 z2) = \x -> zeroD z2
zeroR1 Integer1 = 0
zeroR1 Float1 = 0.0
zeroR1 Double1 = 0.0
zeroR1 (Data1 dt (Con emb rec : rest)) = to emb (fromTup zeroD rec)
zeroR1 IOError1 = userError "Default Error"
zeroR1 r1 = error ("No zero element of type: " ++ show r1)

instance Zero Int
instance Zero Char
instance (Zero a, Zero b) => Zero (a -> b)
instance Zero Integer
instance Zero Float
instance Zero Double
instance Zero IOError

instance Zero ()
instance Zero Bool
instance (Zero a, Zero b) => Zero (a,b)
instance Zero a => Zero [a]

---------- Generate ------------------------------

data GenerateD a = GenerateD { generateD :: Int -> [a] }

-- | Generate elements of a type up to a certain depth
--
class Rep1 GenerateD a => Generate a where
  generate :: Int -> [a]
  generate = generateR1 rep1

instance Generate a => Sat (GenerateD a) where
  dict = GenerateD generate

genEnum :: (Enum a) => Int -> [a]
genEnum d = enumFromTo (toEnum 0) (toEnum d)

generateR1 :: R1 GenerateD a -> Int -> [a]
generateR1 Int1  d = genEnum d
generateR1 Char1 d = genEnum d
generateR1 Integer1 d = genEnum d
generateR1 Float1 d = genEnum d
generateR1 Double1 d = genEnum d
generateR1 (Data1 dt cons) 0 = []
generateR1 (Data1 dt cons) d =
  [ to emb l | (Con emb rec) <- cons,
               l <- fromTupM (\x -> generateD x (d-1)) rec]
generateR1 r1 x = error ("No way to generate type: " ++ show r1)

instance Generate Int
instance Generate Char
instance Generate Integer
instance Generate Float
instance Generate Double

instance Generate ()
instance (Generate a, Generate b) => Generate (a,b)
instance Generate a => Generate [a]

------------ Enumerate -------------------------------
-- note that this is not the same as the Enum class in the standard prelude

data EnumerateD a = EnumerateD { enumerateD :: [a] }

instance Enumerate a => Sat (EnumerateD a) where
    dict = EnumerateD { enumerateD = enumerate }

-- | enumerate the elements of a type, in DFS order.
class Rep1 EnumerateD a => Enumerate a where
    enumerate :: [a]
    enumerate = enumerateR1 rep1

enumerateR1 :: R1 EnumerateD a -> [a]
enumerateR1 Int1 =  [minBound .. (maxBound::Int)]
enumerateR1 Char1 = [minBound .. (maxBound::Char)]
enumerateR1 (Data1 dt cons) = enumerateCons cons
enumerateR1 r1 = error ("No way to enumerate type: " ++ show r1)

enumerateCons :: [Con EnumerateD a] -> [a]
enumerateCons (Con emb rec:rest) = (map (to emb) (fromTupM enumerateD rec)) ++ (enumerateCons rest)
enumerateCons [] = []

----------------- Shrink (from SYB III) -------------------------------

data ShrinkD a = ShrinkD { shrinkD :: a -> [a] }

instance Shrink a => Sat (ShrinkD a) where
    dict = ShrinkD { shrinkD    = shrink }

-- | Given an element, return smaller elements of the same type
-- for example, to automatically find small counterexamples when testing
class (Rep1 ShrinkD a) => Shrink a where
    shrink :: a -> [a]
    shrink a = subtrees a ++ shrinkStep a
               where shrinkStep t = let M _ ts = gmapM1 m a
                                    in ts
                     m :: forall a. ShrinkD a -> a -> M a
                     m dict x = M x ((shrinkD dict) x)

data M a = M a [a]

instance Monad M where
 return x = M x []
 (M x xs) >>= k = M r (rs1 ++ rs2)
   where
     M r rs1 = k x
     rs2 = [r | x <- xs, let M r _ = k x]

instance Shrink Int
instance Shrink a => Shrink [a]
instance Shrink Char
instance Shrink ()
instance (Shrink a, Shrink b) => Shrink (a,b)

------------ Reduce -------------------------------

data RreduceD b a = RreduceD { rreduceD :: a -> b -> b }
data LreduceD b a = LreduceD { lreduceD :: b -> a -> b }

-- | A general version of fold right, use for Fold class below
class Rep1 (RreduceD b) a => Rreduce b a where
    rreduce :: a -> b -> b
    rreduce = rreduceR1 rep1

-- | A general version of fold left, use for Fold class below
class Rep1 (LreduceD b) a => Lreduce b a where
    lreduce :: b -> a -> b
    lreduce = lreduceR1 rep1

-- For example
-- @ instance Fold [] where
--	 foldRight op = rreduceR1 (rList1 (RreduceD { rreduceD = op })
--					  (RreduceD { rreduceD = foldRight op }))
--	 foldLeft op = lreduceR1 (rList1 (LreduceD  { lreduceD = op })
--					 (LreduceD { lreduceD = foldLeft op }))
-- @

instance Rreduce b a => Sat (RreduceD b a) where
    dict = RreduceD { rreduceD = rreduce }
instance Lreduce b a => Sat (LreduceD b a) where
    dict = LreduceD { lreduceD = lreduce }

lreduceR1 :: R1 (LreduceD b) a -> b -> a -> b
lreduceR1 (Data1 dt cons) b a = case (findCon cons a) of
  Val emb rec args -> foldl_l lreduceD b rec args
lreduceR1 _               b a = b

rreduceR1 :: R1 (RreduceD b) a -> a -> b -> b
rreduceR1 (Data1 dt cons) a b = case (findCon cons a) of
  Val emb rec args -> foldr_l rreduceD b rec args
rreduceR1 _               a b = b

-- Instances for standard types
instance Lreduce b Int
instance Lreduce b ()
instance Lreduce b Char
instance Lreduce b Bool
instance (Lreduce c a, Lreduce c b) => Lreduce c (a,b)
instance Lreduce c a => Lreduce c[a]

instance Rreduce b Int
instance Rreduce b ()
instance Rreduce b Char
instance Rreduce b Bool
instance (Rreduce c a, Rreduce c b) => Rreduce c (a,b)
instance Rreduce c a => Rreduce c[a]

-------------------- Fold -------------------------------
-- | All of the functions below are defined using instances
-- of the following class
class Fold f where
	 foldRight :: Rep a => (a -> b -> b) -> f a -> b -> b
	 foldLeft  :: Rep a => (b -> a -> b) -> b -> f a -> b

-- | Fold a bindary operation left over a datastructure
crush      :: (Rep a, Fold t) => (a -> a -> a) -> a -> t a -> a
crush op   = foldLeft op

-- | Multiply all elements together
gproduct   :: (Rep a, Num a, Fold t) => t a -> a
gproduct t = foldLeft (*) 1 t

-- | Ensure all booleans are true
gand       :: (Fold t) => t Bool -> Bool
gand t     = foldLeft (&&) True t

-- | Ensure at least one boolean is true
gor        :: (Fold t) => t Bool -> Bool
gor  t     = foldLeft (||) False t

-- | Convert to list
flatten    :: (Rep a, Fold t) => t a -> [a]
flatten t  = foldRight (:) t []

-- | Count number of @a@s that appear in the argument
count      :: (Rep a, Fold t) => t a -> Int
count t    = foldRight (const (+1)) t 0

-- | Compose all functions in the datastructure together
comp       :: (Rep a, Fold t) => t (a -> a) -> a -> a
comp t     = foldLeft (.) id t

-- | Concatenate all lists in the datastructure together
gconcat    :: (Rep a, Fold t) => t [a] -> [a]
gconcat t  = foldLeft (++) []  t

-- | Ensure property holds of all data
gall       :: (Rep a, Fold t) => (a -> Bool) -> t a -> Bool
gall p t   = foldLeft (\a b -> a && p b) True t


-- | Ensure property holds of some element
gany       :: (Rep a, Fold t) => (a -> Bool) -> t a -> Bool
gany p t   = foldLeft (\a b -> a || p b) False t

-- | Is an element stored in a datastructure
gelem      :: (Rep a, Eq a, Fold t) => a -> t a -> Bool
gelem x t  = foldRight (\a b -> a == x || b) t False


instance Fold [] where
	 foldRight op = rreduceR1 (rList1 (RreduceD { rreduceD = op })
					  (RreduceD { rreduceD = foldRight op }))
	 foldLeft op = lreduceR1 (rList1 (LreduceD  { lreduceD = op })
					 (LreduceD { lreduceD = foldLeft op }))

