{-# LANGUAGE GADTs
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , UndecidableInstances
           , OverlappingInstances
           , Rank2Types
           , TypeOperators
           , TypeFamilies
  #-}

module GADT where

import Reify

import Data.Maybe (catMaybes)
import Unsafe.Coerce
import Data.Type.Equality

import Generics.RepLib

data Foo a where
  Bar  :: Int -> Foo Int
  Bar2 :: Foo b -> Foo [b]
  Bar3 :: Foo c -> Foo d -> Foo (c,d)

instance Show (Foo a) => Show (Foo [a]) where
  show (Bar2 f) = "Bar2 (" ++ show f ++ ")"

instance Show (Foo Int) where
  show (Bar n) = "Bar " ++ show n

instance (Show (Foo c), Show (Foo d)) => Show (Foo (c,d)) where
  show (Bar3 f1 f2) = "(" ++ show f1 ++ ", " ++ show f2 ++ ")"

data Blub = Blob Int

$(doReify ''Foo)

-- $(derive [''Foo])

rFoo :: forall a. Rep a => R (Foo a)
rFoo
  = Data
      (DT "Foo" ((:+:) (rep :: R a) MNil))
      (catMaybes
      [ case eqT (rep :: R a) Int of
           Just Refl -> Just rMkBar
           _         -> Nothing

      , case destr1 (rep :: R a) (rep :: R [()]) of
           Result1 (Refl :: a :=: [b]) -> Just rMkBar2
           _                           -> Nothing

      , case destr2 (rep :: R a) (rep :: R ((),())) of
           Result2 (Refl :: a :=: (c,d)) -> Just rMkBar3
           _                             -> Nothing
      ])

-- rMkBar :: (Con R (Foo Int))
rMkBar = Con mkBarEmb (Int :+: MNil)

-- mkBarEmb :: Emb (Int :*: Nil) (Foo Int)
mkBarEmb = Emb
        { name = "Bar"
        , to   = \(x :*: Nil) -> Bar x
        , from = \y -> case y of { Bar x -> Just ((:*:) x Nil) }
        , labels = Nothing, fixity = Nonfix
        }

rMkBar2 :: forall b. Rep b => Con R (Foo [b])
rMkBar2 = Con mkBar2Emb ((rep :: R (Foo b)) :+: MNil)

mkBar2Emb :: Emb (Foo b :*: Nil) (Foo [b])
mkBar2Emb = Emb
        { name = "Bar2"
        , to   = \(x :*: Nil) -> Bar2 x
        , from = \y -> case y of { Bar2 x -> Just ((:*:) x Nil) }
        , labels = Nothing, fixity = Nonfix
        }

rMkBar3 :: forall c d. (Rep c, Rep d) => Con R (Foo (c,d))
rMkBar3 = Con mkBar3Emb ((rep :: R (Foo c)) :+: (rep :: R (Foo d)) :+: MNil)

mkBar3Emb :: Emb (Foo c :*: Foo d :*: Nil) (Foo (c,d))
mkBar3Emb = Emb
        { name = "Bar3"
        , to   = \(x :*: y :*: Nil) -> Bar3 x y
        , from = \z -> case z of { Bar3 x y -> Just (x :*: y :*: Nil) }
        , labels = Nothing, fixity = Nonfix
        }

data Res1 c a where
  Result1   :: Rep b => a :=: (c b) -> Res1 c a
  NoResult1 :: Res1 c a

-- data InList a where
--   InList :: Rep b => R b -> a :=: [b] -> InList a

destr1 :: R a -> R (c d) -> Res1 c a
destr1 (Data (DT s1 ((rb :: R b) :+: MNil)) _)
       (Data (DT s2 _) _)
  | s1 == s2  = Result1 (unsafeCoerce Refl :: a :=: (c b))
  | otherwise = NoResult1
destr1 _ _ = NoResult1

data Res2 c2 a where
  Result2   :: (Rep d, Rep e) => a :=: (c2 d e) -> Res2 c2 a
  NoResult2 :: Res2 c2 a

destr2 :: R a -> R (c2 d e) -> Res2 c2 a
destr2 (Data (DT s1 ((rd :: R d) :+: (re :: R e) :+: MNil)) _)
       (Data (DT s2 _) _)
  | s1 == s2  = Result2 (unsafeCoerce Refl :: a :=: (c2 d e))
  | otherwise = NoResult2
destr2 _ _ = NoResult2

-- prjList :: R a -> Maybe (InList a)
-- prjList ra@(Data (DT "[]" (rb :+: MNil)) _) = Just $ InList rb (unsafeCoerce Refl)
-- prjList _ = Nothing

instance Rep a => Rep (Foo a) where
    rep = rFoo

{-
-- Argh, but what about normal (non-GADT) constructors?  Can't have
-- overlapping data instances!  (Note: this would still be true even
-- if we could have closed data families, because of how these are
-- translated into equality axioms...)

-- Maybe we could create a new GADT, w/ isomorphism to original, where
-- all the constructor return types are distinguished?  Gets uglier
-- and uglier...
data family FooArgs :: (* -> *) -> * -> *
data instance FooArgs ctx Int = FooArg1 (ctx Int)
data instance FooArgs ctx [b] = FooArg2 (ctx (Foo b))

instance Sat (ctx Int) => Sat (FooArgs ctx Int) where
  dict = FooArg1 dict

instance Sat (ctx (Foo b)) => Sat (FooArgs ctx [b]) where
  dict = FooArg2 dict
-}

rFoo1 ::
  forall ctx a. Rep a =>
  ctx Int ->
  (forall b. a :=: [b] -> ctx (Foo b)) ->
  (forall c d. a :=: (c,d) -> (ctx (Foo c), ctx (Foo d))) ->
  R1 ctx (Foo a)
rFoo1 ci cb ccd
  = Data1 (DT "Foo" ((:+:) (rep :: R a) MNil))
      (catMaybes
      [ case eqT (rep :: R a) Int of
           Just Refl -> Just $ rMk1Bar ci
           _         -> Nothing

      , case destr1 (rep :: R a) (rep :: R [()]) of
           Result1 Refl -> Just $ rMk1Bar2 (cb Refl)
           _            -> Nothing

      , case destr2 (rep :: R a) (rep :: R ((),())) of
           Result2 Refl -> Just $ rMk1Bar3 (ccd Refl)
           _            -> Nothing
      ])

rMk1Bar :: ctx Int -> Con ctx (Foo Int)
rMk1Bar c = Con mkBarEmb (c :+: MNil)

rMk1Bar2 :: Rep b => ctx (Foo b) -> Con ctx (Foo [b])
rMk1Bar2 c = Con mkBar2Emb (c :+: MNil)

rMk1Bar3 :: (Rep c, Rep d) => (ctx (Foo c), ctx (Foo d)) -> Con ctx (Foo (c,d))
rMk1Bar3 (cc, cd) = Con mkBar3Emb (cc :+: cd :+: MNil)

class BSat ctx a where
    bdict :: forall b. a :=: [b] -> ctx (Foo b)

instance Sat (ctx (Foo b)) => BSat ctx [b] where
    bdict = \ Refl -> dict

instance BSat ctx a where
  bdict = \ Refl -> error "BSat instance for a is impossible"

{-
instance (Sat (ctx (Foo b)), a ~ [b]) => BSat ctx a where
  bdict = \ Refl -> dict
-}

class CDSat ctx a where
  cddict :: forall c d. a :=: (c,d) -> (ctx (Foo c), ctx (Foo d))

instance (Sat (ctx (Foo c)), Sat (ctx (Foo d))) => CDSat ctx (c,d) where
  cddict = \ Refl -> (dict, dict)

instance CDSat ctx a where
  cddict = \ Refl -> error "CDSat instance for a is impossible"

instance (Rep a,
          Sat (ctx Int),
          BSat ctx a,
          CDSat ctx a
         ) =>
         Rep1 ctx (Foo a) where
   rep1 = rFoo1 dict bdict cddict

instance GSum a => GSum (Foo a)

size :: R a -> a -> Int
size Int _ = 1
size (Equal _ _) _ = 0
size (Data _ cons) a = case (findCon cons a) of
  Val emb rec args -> 1 + sizeL rec args

sizeL :: MTup R l -> l -> Int
sizeL MNil _ = 0
sizeL (r :+: tup) (a :*: l') = size r a + sizeL tup l'


eroiufreg :: R a -> a -> Int
eroiufreg Int x = x
eroiufreg (Equal _ _) _ = 0
eroiufreg (Data _ cons) a = case (findCon cons a) of
  Val emb rec args -> sumL rec args

sumL :: MTup R l -> l -> Int
sumL MNil _ = 0
sumL (r :+: tup) (a :*: l') = eroiufreg r a + sumL tup l'



{-
data Foo a where
  Bar :: Int -> Foo Int
  Baz :: Char -> Foo a


rFoo :: forall a[a14X]. Rep a[a14X] => R (Foo a[a14X])
rFoo
  = Data
      (DT "Foo" ((:+:) (rep :: R a[a14X]) MNil))
      [Con
         (Emb
            {name = "Bar", to = \ (x[a15C] :*: Nil) -> Bar x[a15C],
             from = \ y[a15E]
                      -> case y[a15E] of {
                           Bar x[a15D] -> Just ((:*:) x[a15D] Nil)
                           _ -> Nothing },
             labels = Nothing, fixity = Nonfix})
         (Int :+: MNil),
       Con
         (Emb
            {name = "Baz", to = \ (x[a15F] :*: Nil) -> Baz x[a15F],
             from = \ y[a15H]
                      -> case y[a15H] of {
                           Baz x[a15G] -> Just ((:*:) x[a15G] Nil)
                           _ -> Nothing },
             labels = Nothing, fixity = Nonfix})
         (Char :+: MNil)]
instance Rep a[a14X] => Rep (Foo a[a14X]) where
    { rep = rFoo }
rFoo1 ::
  forall ctx[a15t] a[a14X]. Rep a[a14X] =>
  ctx[a15t] Int -> ctx[a15t] Char -> R1 ctx[a15t] (Foo a[a14X])
rFoo1
  = \ (p[a15u] :: ctx[a15t] Int) (p[a15v] :: ctx[a15t] Char)
      -> Data1
           (DT "Foo" ((:+:) (rep :: R a[a14X]) MNil))
           [Con
              (Emb
                 {name = "Bar", to = \ (x[a15w] :*: Nil) -> Bar x[a15w],
                  from = \ y[a15y]
                           -> case y[a15y] of {
                                Bar x[a15x] -> Just ((:*:) x[a15x] Nil)
                                _ -> Nothing },
                  labels = Nothing, fixity = Nonfix})
              (p[a15u] :+: MNil),
            Con
              (Emb
                 {name = "Baz", to = \ (x[a15z] :*: Nil) -> Baz x[a15z],
                  from = \ y[a15B]
                           -> case y[a15B] of {
                                Baz x[a15A] -> Just ((:*:) x[a15A] Nil)
                                _ -> Nothing },
                  labels = Nothing, fixity = Nonfix})
              (p[a15v] :+: MNil)]
instance (Rep a[a14X],
          Sat (ctx[a15t] Int),
          Sat (ctx[a15t] Char)) =>
         Rep1 ctx[a15t] (Foo a[a14X]) where
    { rep1 = rFoo1 dict dict }

-}

{-
data Term c where
  Pair :: a -> b -> Term (a,b)

rPair :: Con R (Term c)

newtype PairType c a b = PT (Equal c (a, b) :+: a :+: b :+: Nil)

rPairEmb :: Emb (Ex2 (PairType c)) (Term c)


rPairEmb = Emb { to = toPair
               , from = fromPair
               , labels = Nothing
               , name = "Pair"
               , fixity = Nonfix }

toPair :: Ex2 (PairType c) -> Term c
toPair (Ex2 (PT (Refl :*: a :*: b :*: Nil))) = Pair a b

fromPair :: Term c -> Ex2 (PairType c)
fromPair (Pair a b) = Just (Ex2 (PT (Refl :*: a :*: b :*: Nil)))

rPairTup :: MTup R (Ex2 (PairType c))
rPairTup = MEx2 (

$(doReify ''Term)
-}