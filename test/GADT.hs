{-# LANGUAGE GADTs
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module GADT where

import Data.Maybe (catMaybes)
import Unsafe.Coerce

import Generics.RepLib

data Foo a where
  Bar  :: Int -> Foo Int
  Bar2 :: Foo b -> Foo [b]

data Blub = Blob Int

-- $(doReify ''Foo)

-- $(derive [''Foo])

rFoo :: forall a. Rep a => R (Foo a)
rFoo
  = Data
      (DT "Foo" ((:+:) (rep :: R a) MNil))
      (catMaybes
      [ rMkBar  (rep :: R a)
      , rMkBar2 (rep :: R a)
      ])

rMkBar :: R a -> Maybe (Con R (Foo a))
rMkBar ra = case prjInt ra of
  Just Refl -> Just $
    GADT (rFoo :: R (Foo Int)) Refl
      (Emb
        { name = "Bar"
        , to   = \(x :*: Nil) -> Bar x
        , from = \y -> case y of { Bar x -> Just ((:*:) x Nil) }
        , labels = Nothing, fixity = Nonfix
        })
      (Int :+: MNil)
  _ -> Nothing

rMkBar2 :: R a -> Maybe (Con R (Foo a))
rMkBar2 ra = case prjList ra of
  Just (InList (rb :: R b) Refl) -> Just $
    GADT (rFoo :: R (Foo [b])) Refl
      (Emb
        { name = "Bar2"
        , to   = \(x :*: Nil) -> Bar2 x
        , from = \y -> case y of { Bar2 x -> Just ((:*:) x Nil) }
        , labels = Nothing, fixity = Nonfix
        })
      ((rFoo :: R (Foo b)) :+: MNil)

  _ -> Nothing

data InList a where
  InList :: Rep b => R b -> Equal a [b] -> InList a

prjList :: R a -> Maybe (InList a)
prjList ra@(Data (DT "[]" (rb :+: MNil)) _) = Just $ InList rb (unsafeCoerce Refl)
prjList _                                   = Nothing

prjInt :: R a -> Maybe (Equal a Int)
prjInt Int = Just Refl
prjInt _   = Nothing

instance Rep a => Rep (Foo a) where
    { rep = rFoo }
rFoo1 ::
  forall ctx a. Rep a =>
  ctx (Equal a Int) -> ctx Int -> R1 ctx (Foo a)
rFoo1
  = \ (e :: ctx (Equal a Int)) (p :: ctx Int)
      -> Data1
           (DT "Foo" ((:+:) (rep :: R a) MNil))
           [Con
              (Emb
                 {name = "Bar", to = \ (Refl :*: x :*: Nil) -> Bar x,
                  from = \ y
                           -> case y of { Bar x -> Just ((:*:) Refl ((:*:) x Nil)) },
                  labels = Nothing, fixity = Nonfix})
              (e :+: p :+: MNil)]
instance (Rep a, Sat (ctx (Equal a Int)), Sat (ctx Int)) =>
         Rep1 ctx (Foo a) where
    { rep1 = rFoo1 dict dict }

{-
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