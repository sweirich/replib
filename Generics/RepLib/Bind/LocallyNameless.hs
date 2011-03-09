{-# LANGUAGE FlexibleInstances,
             UndecidableInstances,
             FlexibleContexts,
             MultiParamTypeClasses,
             TemplateHaskell,
             TypeOperators,
             ScopedTypeVariables,
             TypeSynonymInstances,
             RankNTypes,
             GADTs,
             EmptyDataDecls,
             StandaloneDeriving,
             GeneralizedNewtypeDeriving, 
             TypeFamilies
  #-}
{- LANGUAGE  KitchenSink -}

----------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib.Bind.LocallyNameless
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  non-portable (-XKitchenSink)
--
-- A generic implementation of name binding functions using a locally
-- nameless representation.  Datatypes with binding can be defined
-- using the 'Name' and 'Bind' types.  Expressive patterns for binding
-- come from the 'Annot' and 'Rebind' types.
--
-- Important classes are:
--
--   * 'Alpha' -- the class of types and patterns that include binders,
--
--   * 'Subst' -- for subtitution functions.
--
-- Name generation is controlled via monads which implement the
-- 'Fresh' and 'LFresh' classes.
----------------------------------------------------------------------

module Generics.RepLib.Bind.LocallyNameless
  ( -- * Basic types
    Name, AnyName(..), Bind, Annot(..), Rebind, Rec,

    -- ** Utilities
    integer2Name, string2Name, s2n, makeName,
    name2Integer, name2String, anyName2Integer, anyName2String,
    name1,name2,name3,name4,name5,name6,name7,name8,name9,name10,
    translate,

    -- * The 'Alpha' class
    Alpha(..),
    swaps, swapsAnnots, swapsBinders,
    match, matchAnnots, matchBinders,
    fv, fvAny, patfv, binders,
    aeq, aeqBinders,
    acompare,

    -- * Binding operations
    bind, unsafeUnbind,

    -- * The 'Fresh' class
    Fresh(..), freshen,
    unbind, unbind2, unbind3,

    FreshM, runFreshM,
    FreshMT, runFreshMT,

    -- * The 'LFresh' class
    LFresh(..),
    lfreshen,
    lunbind, lunbind2, lunbind3,

    LFreshM, runLFreshM, getAvoids,
    LFreshMT, runLFreshMT,

    -- * Rebinding operations
    rebind, unrebind,

    -- * Rec operations
    rec, unrec,

    -- * Substitution
    Subst(..),SubstName(..),

   -- * Advanced
   AlphaCtx, matchR1,

   -- * Pay no attention to the man behind the curtain
   -- $paynoattention
   rName, rBind, rRebind, rAnnot
) where

import Generics.RepLib hiding (GT)
import Generics.RepLib.Bind.PermM
import Generics.RepLib.Bind.Name
import Generics.RepLib.Bind.Fresh

import qualified Data.List as List
import qualified Data.Char as Char
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import qualified Text.Read as R
import Prelude hiding (or)
import Data.Function (on)
import Data.Monoid
import qualified Data.Foldable as F
import Control.Monad (liftM2)
import Control.Monad.Reader (Reader,ask,local,runReader,MonadReader)
import Control.Applicative (Applicative)
import System.IO.Unsafe (unsafePerformIO)

------------------------------------------------------------
-- Overview
--
-- We have two classes of types: 
--    Terms (which contain binders) and 
--    Patterns (which contain variables)
-- 
-- Terms include 
--    Names 
--    Bind a b when a is a Pattern and b is a Term
--    Standard type constructors (Unit, (,), Maybe, [], etc)
-- 
-- Patterns include
--    Names
--    Annot a when a is a Term
--    Rebind a b when a and b are both Patterns
--    Standard type constructors (Unit, (,), Maybe, [], etc)
-- 
-- Terms support a number of operations, including alpha-equivalence,
-- free variables, swapping, etc.  Because Patterns occur in terms, so
-- they too support the same operations, but only for the annotations 
-- inside them.
-- Therefore, both Terms and Patterns are instances of the "Alpha" type class
-- which lists these operations.  However, some types (such as [Name])
-- are both Terms and Patterns, and the behavior of the operations 
-- is different when we use [Name] as a term and [Name] as a pattern.
-- Therefore, we index each of the operations with a mode that tells us 
-- what version we should be defining.
--
-- [SCW: could we use multiparameter type classes? Alpha m t]
-- 
-- Patterns also support a few extra operations that Terms do not 
-- for dealing with the binding variables. 
--     These are used to find the index of names inside patterns.
------------------------------------------------------------

------------------------------------------------------------
-- Basic types
------------------------------------------------------------

$(derive_abstract [''R])
-- The above only works with GHC 7.

-- | The type of a binding.  We can 'Bind' an @a@ object in a @b@
--   object if we can create \"fresh\" @a@ objects, and @a@ objects
--   can occur unbound in @b@ objects. Often @a@ is 'Name' but that
--   need not be the case.
--
--   Like 'Name', 'Bind' is also abstract. You can create bindings
--   using 'bind' and take them apart with 'unbind' and friends.
data Bind a b = B a b

-- | An annotation is a \"hole\" in a pattern where variables can be
--   used, but not bound. For example, patterns may include type
--   annotations, and those annotations can reference variables
--   without binding them.  Annotations do nothing special when they
--   appear elsewhere in terms.
newtype Annot a = Annot a deriving Eq

-- | 'Rebind' supports \"telescopes\" --- that is, patterns where
--   bound variables appear in multiple subterms.
data Rebind a b = R a b

-- | 'Rec' supports recursive patterns --- that is, patterns where
-- any variables anywhere in the pattern are bound in the pattern
-- itself.  Useful for lectrec (and Agda's dot notation).
newtype Rec a = Rec (Rebind [AnyName] a)

$(derive [''Bind, ''Name, ''Annot, ''Rebind, ''Rec])

--------------------------------------------------
-- Pointed functors
--------------------------------------------------

-- Pointed
class Pointed f where
  singleton :: a -> f a

instance Pointed [] where
  singleton = (:[])

instance Pointed S.Set where
  singleton = S.singleton

fromList :: (Pointed f, Monoid (f a)) => [a] -> f a
fromList = mconcat . map singleton

------------------------------------------------------------
-- The Alpha class
------------------------------------------------------------

-- | The 'Alpha' type class is for types which may contain names.  The
--   'Rep1' constraint means that we can only make instances of this
--   class for types that have generic representations (which can be
--   automatically derived by RepLib.)
--
--   Note that the methods of 'Alpha' should never be called directly!
--   Instead, use other methods provided by this module which are
--   defined in terms of 'Alpha' methods. (The only reason they are
--   exported is to make them available to automatically-generated
--   code.)
--
--   Most of the time, the default definitions of these methods will
--   suffice, so you can make an instance for your data type by simply
--   declaring
--
--   > instance Alpha MyType
--
class (Show a, Rep1 AlphaD a) => Alpha a where

  -- | See 'swaps'.
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  swaps' = swapsR1 rep1

  -- | See 'fv'.
  fv' :: (Pointed f, Monoid (f AnyName)) => AlphaCtx -> a -> f AnyName
  fv' = fvR1 rep1

  -- | See 'lfreshen'.
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  lfreshen' = lfreshenR1 rep1

  -- | See 'freshen'.
  freshen' :: Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  freshen' = freshenR1 rep1

  -- | See 'aeq'.
  aeq' :: AlphaCtx -> a -> a -> Bool
  aeq' = aeqR1 rep1

  -- | See 'match'.
  match'   :: AlphaCtx -> a -> a -> Maybe (Perm AnyName)
  match'   = matchR1 rep1

  -- | Replace free names by bound names.
  close :: Alpha b => AlphaCtx -> b -> a -> a
  close = closeR1 rep1

  -- | Replace bound names by free names.
  open :: Alpha b => AlphaCtx -> b -> a -> a
  open = openR1 rep1

  -- | See 'acompare'.
  acompare' :: AlphaCtx -> a -> a -> Ordering
  acompare' = acompareR1 rep1


  ---------------- PATTERN OPERATIONS ----------------------------

  -- | @'nthpatrec' b n@ looks up the @n@th name in the pattern @b@
  -- (zero-indexed), returning the number of names encountered if not
  -- found.
  nthpatrec :: a -> Integer -> (Integer, Maybe AnyName)
  nthpatrec = nthpatR1 rep1

  -- | Find the (first) index of the name in the pattern if it exists;
  --   if not found ('Bool' = 'False'), return the number of names
  --   encountered instead.
  findpatrec :: a -> AnyName -> (Integer, Bool)
  findpatrec = findpatR1 rep1

-- | Many of the operations in the 'Alpha' class take an 'AlphaCtx':
-- stored information about the iteration as it progresses. This type
-- is abstract, as classes that override these operations should just pass
-- the context on.
data AlphaCtx = AC { mode :: Mode , level :: Integer }

initial :: AlphaCtx
initial = AC Term 0

incr :: AlphaCtx -> AlphaCtx
incr c = c { level = level c + 1 }

pat  :: AlphaCtx -> AlphaCtx
pat c  = c { mode = Pat }

term  :: AlphaCtx -> AlphaCtx
term c  = c { mode = Term }

-- | A mode is basically a flag that tells us whether we should be
--   looking at the names in the term, or if we are in a pattern and
--   should /only/ be looking at the names in the annotations. The
--   standard mode is to use 'Term'; many functions do this by default.
data Mode = Term | Pat deriving (Show, Eq, Read)

-- | Class constraint hackery to allow us to override the default
--   definitions for certain classes.  'AlphaD' is essentially a
--   reified dictionary for the 'Alpha' class.
data AlphaD a = AlphaD {
  swapsD    :: AlphaCtx -> Perm AnyName -> a -> a,
  fvD       :: (Monoid (f AnyName), Pointed f) => AlphaCtx -> a -> f AnyName,
  freshenD  :: forall m. Fresh m => AlphaCtx -> a -> m (a, Perm AnyName),
  lfreshenD :: forall b m. LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b,
  aeqD      :: AlphaCtx -> a -> a -> Bool,
  matchD    :: AlphaCtx -> a -> a -> Maybe (Perm AnyName),
  closeD    :: Alpha b => AlphaCtx -> b -> a -> a,
  openD     :: Alpha b => AlphaCtx -> b -> a -> a,
  findpatD  :: a -> AnyName -> (Integer, Bool),
  nthpatD   :: a -> Integer -> (Integer, Maybe AnyName),
  acompareD :: AlphaCtx -> a -> a -> Ordering
  }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD swaps' fv' freshen' lfreshen' aeq' match'
           close open findpatrec nthpatrec acompare'

----------------------------------------------------------------------
-- Generic definitions for 'Alpha' methods.  (Note that all functions
-- that take representations end in 'R1'.)
----------------------------------------------------------------------

closeR1 :: Alpha b => R1 AlphaD a -> AlphaCtx -> b -> a -> a
closeR1 (Data1 _ cons) = \i a d ->
   case (findCon cons d) of
      Val c rec kids ->
        to c (map_l (\z -> closeD z i a) rec kids)
closeR1 _               = \_ _ d -> d


openR1 :: Alpha b => R1 AlphaD a -> AlphaCtx -> b -> a -> a
openR1 (Data1 _ cons) = \i a d ->
   case (findCon cons d) of
      Val c rec kids ->
        to c (map_l (\z -> openD z i a) rec kids)
openR1 _               = \_ _ d -> d


swapsR1 :: R1 AlphaD a -> AlphaCtx -> Perm AnyName -> a -> a
swapsR1 (Data1 _ cons)  = \ p x d ->
  case (findCon cons d) of
    Val c rec kids -> to c (map_l (\z -> swapsD z p x) rec kids)
swapsR1 _               = \ _ _ d -> d


fvR1 :: (Pointed f, Monoid (f AnyName)) => R1 (AlphaD) a -> AlphaCtx -> a -> f AnyName
fvR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> fv1 rec p kids
fvR1 _ = \ _ _ -> mempty

fv1 :: (Pointed f, Monoid (f AnyName)) => MTup (AlphaD) l -> AlphaCtx -> l -> f AnyName
fv1 MNil _ Nil = mempty
fv1 (r :+: rs) p (p1 :*: t1) =
   fvD r p p1 `mappend` fv1 rs p t1


matchR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> a -> Maybe (Perm AnyName)
matchR1 (Data1 _ cons) = loop cons where
   loop (Con emb reps : rest) p x y =
     case (from emb x, from emb y) of
      (Just p1, Just p2) -> match1 reps p p1 p2
      (Nothing, Nothing) -> loop rest p x y
      (_,_)              -> Nothing
   loop [] _ _ _ = error "Impossible"
matchR1 Int1 = \ _ x y -> if x == y then Just empty else Nothing
matchR1 Integer1 = \ _ x y -> if x == y then Just empty else Nothing
matchR1 Char1 = \ _ x y -> if x == y then Just empty else Nothing
matchR1 _ = \ _ _ _ -> Nothing

match1 :: MTup (AlphaD) l -> AlphaCtx -> l -> l -> Maybe (Perm AnyName)
match1 MNil _ Nil Nil = Just empty
match1 (r :+: rs) c (p1 :*: t1) (p2 :*: t2) = do
  l1 <- matchD r c p1 p2
  l2 <- match1 rs c t1 t2
  (l1 `join` l2)

aeqR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> a -> Bool
aeqR1 (Data1 _ cons) = loop cons where
   loop (Con emb reps : rest) p x y =
     case (from emb x, from emb y) of
      (Just p1, Just p2) -> aeq1 reps p p1 p2
      (Nothing, Nothing) -> loop rest p x y
      (_,_)              -> False
   loop [] _ _ _ = error "Impossible"
aeqR1 Int1     = \ _ x y ->  x == y 
aeqR1 Integer1 = \ _ x y -> x == y 
aeqR1 Char1    = \ _ x y -> x == y
aeqR1 _        = \ _ _ _ -> False

aeq1 :: MTup (AlphaD) l -> AlphaCtx -> l -> l -> Bool
aeq1 MNil _ Nil Nil = True
aeq1 (r :+: rs) c (p1 :*: t1) (p2 :*: t2) = do
  aeqD r c p1 p2 && aeq1 rs c t1 t2

freshenR1 :: Fresh m => R1 (AlphaD) a -> AlphaCtx -> a -> m (a,Perm AnyName)
freshenR1 (Data1 _ cons) = \ p d ->
   case findCon cons d of
     Val c rec kids -> do
       (l, p') <- freshenL rec p kids
       return (to c l, p')
freshenR1 _ = \ _ n -> return (n, empty)

freshenL :: Fresh m => MTup (AlphaD) l -> AlphaCtx -> l -> m (l, Perm AnyName)
freshenL MNil _ Nil = return (Nil, empty)
freshenL (r :+: rs) p (t :*: ts) = do
  (xs, p2) <- freshenL rs p ts
  (x, p1) <- freshenD r p (swapsD r p p2 t)
  return ( x :*: xs, p1 <> p2)

lfreshenR1 :: LFresh m => R1 AlphaD a -> AlphaCtx -> a ->
              (a -> Perm AnyName -> m b) -> m b
lfreshenR1 (Data1 _ cons) = \p d f ->
   case findCon cons d of
     Val c rec kids -> lfreshenL rec p kids (\ l p' -> f (to c l) p')
lfreshenR1 _ = \ _ n f -> f n empty

lfreshenL :: LFresh m => MTup (AlphaD) l -> AlphaCtx -> l ->
              (l -> Perm AnyName -> m b) -> m b
lfreshenL MNil _ Nil f = f Nil empty
lfreshenL (r :+: rs) p (t :*: ts) f =
  lfreshenL rs p ts ( \ y p2 ->
  lfreshenD r p (swapsD r p p2 t) ( \ x p1 ->
     f (x :*: y) (p1 <> p2)))


-- returns either (# of names in b, false) or (index, true)
findpatR1 :: R1 AlphaD b -> b -> AnyName -> (Integer, Bool)
findpatR1 (Data1 dt cons) = \ d n ->
   case findCon cons d of
     Val c rec kids -> findpatL rec kids n
findpatR1 _ = \ x n -> (0, False)

findpatL :: MTup AlphaD l -> l -> AnyName -> (Integer, Bool)
findpatL MNil Nil n = (0, False)
findpatL (r :+: rs) (t :*: ts) n =
  case findpatD r t n of
    s@(i, True) -> s
    (i, False) -> case findpatL rs ts n of
                    (j, b) -> (i+j, b)

nthpatR1 :: R1 AlphaD b -> b -> Integer -> (Integer, Maybe AnyName)
nthpatR1 (Data1 dt cons) = \ d n ->
   case findCon cons d of
     Val c rec kids -> nthpatL rec kids n
nthpatR1 _ = \ x n -> (n, Nothing)

nthpatL :: MTup AlphaD l -> l -> Integer -> (Integer, Maybe AnyName)
nthpatL MNil Nil i = (i, Nothing)
nthpatL (r :+: rs) (t :*: ts) i =
  case nthpatD r t i of
    s@(_, Just n) -> s
    (j, Nothing) -> nthpatL rs ts j

-- Exactly like the generic Ord instance defined in Generics.RepLib.PreludeLib,
-- except that the comparison operation takes an AlphaCtx

acompareR1 :: R1 AlphaD a -> AlphaCtx -> a -> a -> Ordering
acompareR1 Int1  c = \x y -> compare x y
acompareR1 Char1 c = \x y -> compare x y
acompareR1 (Data1 str cons) c = \x y ->
             let loop (Con emb rec : rest) =
                     case (from emb x, from emb y) of
                        (Just t1, Just t2) -> compareTupM rec c t1 t2
                        (Just t1, Nothing) -> LT
                        (Nothing, Just t2) -> GT
                        (Nothing, Nothing) -> loop rest
             in loop cons
acompareR1 r1 c = error ("compareR1 not supported for " ++ show r1)

lexord         :: Ordering -> Ordering -> Ordering
lexord LT ord  =  LT
lexord EQ ord  =  ord
lexord GT ord  =  GT

compareTupM :: MTup AlphaD l -> AlphaCtx -> l -> l -> Ordering
compareTupM MNil c Nil Nil = EQ
compareTupM (x :+: xs) c (y :*: ys) (z :*: zs) =
   lexord (acompareD x c y z) (compareTupM xs c ys zs)


------------------------------------------------------------
-- Specific Alpha instances for the four important type 
-- constructors:
--      Names, Bind, Annot, Rebind and Rec 
-----------------------------------------------------------

-- in the name instance, if the mode is Term then the operation
-- observes the name. In Pat mode the name is pretty much ignored.
instance Rep a => Alpha (Name a) where
  fv' c n@(Nm _ _)  | mode c == Term = singleton (AnyName n)
  fv' _ _                            = mempty

  swaps' c p x | mode c == Term =
                     case apply p (AnyName x) of
                       AnyName y ->
                         case gcastR (getR y) (getR x) y of
                           Just y' -> y'
                           Nothing -> error "Internal error in swaps': sort mismatch"
  swaps' c p x | mode c == Pat  = x

  aeq' _ x y   | x == y         = True
  aeq' c n1 n2 | mode c == Term = False
  aeq' c _ _   | mode c == Pat  = True

  match' _ x  y   | x == y         = Just empty
  match' c n1 n2  | mode c == Term = Just $ single (AnyName n1) (AnyName n2)
  match' c _ _    | mode c == Pat  = Just empty

  freshen' c nm | mode c == Term = do x <- fresh nm
                                      return (x, single (AnyName nm) (AnyName x))
  freshen' c nm | mode c == Pat  = return (nm, empty)

  lfreshen' c nm f = case mode c of
     Term -> do x <- lfresh nm
                avoid [AnyName x] $ f x (single (AnyName nm) (AnyName x))
     Pat  -> f nm empty

  open c a (Bn r j x) | mode c == Term && level c == j =
    case nthpat a x of
      AnyName nm -> case gcastR (getR nm) r nm of
        Just nm' -> nm'
        Nothing  -> error "Internal error in open: sort mismatch"
  open _ _ n = n

  close c a nm@(Nm r n) | mode c == Term =
      case findpat a (AnyName nm) of
        Just x  -> Bn r (level c) x
        Nothing -> nm
  close _ _ n = n

  findpatrec nm1 (AnyName nm2) =
    case gcastR (getR nm1) (getR nm2) nm1 of
      Just nm1' -> if nm1' == nm2 then (0, True) else (1, False)
      Nothing -> (1, False)

  nthpatrec nm 0 = (0, Just (AnyName nm))
  nthpatrec nm i = (i - 1, Nothing)

  acompare' c (Nm r1 n1) (Nm r2 n2) | mode c == Term = lexord (compare r1 r2) (compare n1 n2)
  acompare' c (Bn r1 m1 n1) (Bn r2 m2 n2) | mode c == Term = lexord (compare r1 r2) (lexord (compare m1 m2) (compare n1 n2))
  acompare' c (Nm _ _) (Bn _ _ _) | mode c == Term = LT
  acompare' c (Bn _ _ _) (Nm _ _) | mode c == Term = GT
  acompare' c _ _ | mode c == Pat = EQ

instance Alpha AnyName  where
  fv' c n@(AnyName (Nm _ _))  | mode c == Term = singleton n
  fv' _ _                                      = mempty

  swaps' c p x = case mode c of
                   Term -> apply p x
                   Pat  -> x

  aeq' _ x y | x == y         = True
  aeq' c _ _ | mode c == Term = False
  aeq' c _ _ | mode c == Pat  = True

  match' _ x y | x == y          = Just empty
  match' c (AnyName n1) (AnyName n2)
    | mode c == Term =
      case gcastR (getR n1) (getR n2) n1 of
        Just n1' -> Just $ single (AnyName n1) (AnyName n2)
        Nothing  -> Nothing
  match' c _ _           | mode c == Pat   = Just empty


  acompare' _ x y | x == y          = EQ
  acompare' c (AnyName n1) (AnyName n2)
    | mode c == Term =
      case compareR (getR n1) (getR n2) of
       EQ ->  case gcastR (getR n1) (getR n2) n1 of
          Just n1' -> acompare' c n1' n2
          Nothing  -> error "impossible"
       otherwise -> otherwise
  acompare' c _ _           | mode c == Pat   = EQ



  freshen' c (AnyName nm) = case mode c of
     Term -> do x <- fresh nm
                return (AnyName x, single (AnyName nm) (AnyName x))
     Pat  -> return (AnyName nm, empty)

  --lfreshen' :: LFresh m => Pat a -> (a -> Perm Name -> m b) -> m b
  lfreshen' c (AnyName nm) f = case mode c of
     Term -> do x <- lfresh nm
                avoid [AnyName x] $ f (AnyName x) (single (AnyName nm) (AnyName x))
     Pat  -> f (AnyName nm) empty

  open c a (AnyName (Bn _ j x)) | level c == j = nthpat a x
  open _ _ n = n

  close c a nm@(AnyName (Nm r n)) =
    case findpat a nm of
      Just x  -> AnyName (Bn r (level c) x)
      Nothing -> nm

  close _ _ n = n

  findpatrec nm1 nm2 | nm1 == nm2 = ( 0 , True )
  findpatrec _ _ = (1, False)

  nthpatrec nm 0 = (0, Just nm)
  nthpatrec nm i = (i - 1, Nothing)

instance (Alpha a, Alpha b) => Alpha (Bind a b) where
    swaps' c pm (B x y) =
        (B (swaps' (pat c) pm x)
           (swaps' (incr c) pm y))

    fv' c (B x y) = fv' (pat c) x `mappend` fv' (incr c) y

    freshen' c (B x y) = do
      (x', pm1) <- freshen' (pat c) x
      (y', pm2) <- freshen' (incr c) (swaps' (incr c) pm1 y)
      return (B x' y', pm1 <> pm2)

    lfreshen' c (B x y) f =
--      avoid (S.elems $ fv' c x) $ -- I don't think we need this
        lfreshen' (pat c) x (\ x' pm1 ->
        lfreshen' (incr c) (swaps' (incr c) pm1 y) (\ y' pm2 ->
        f (B x' y') (pm1 <> pm2)))

    aeq' c (B x1 y1) (B x2 y2) = do
      aeq' (pat c) x1 x2  && aeq' (incr c) y1 y2

    match' c (B x1 y1) (B x2 y2) = do
      px <- match' (pat c) x1 x2
      py <- match' (incr c) y1 y2
      -- need to make sure that all permutations of
      -- bound variables at this
      -- level are the identity
      (px `join` py)

    open  c a (B x y)    = B (open (pat c) a x)  (open  (incr c) a y)
    close c a (B x y)    = B (close (pat c) a x) (close (incr c) a y)

    --  Comparing two binding terms.
    acompare' c (B a1 a2) (B b1 b2) = 
      lexord (acompare' (pat c) a1 b1) (acompare' (incr c) a2 b2)

instance (Alpha a, Alpha b) => Alpha (Rebind a b) where

  swaps' p pm (R x y) = R (swaps' p pm x) (swaps' (incr p) pm y)

  fv' p (R x y) =  fv' p x `mappend` fv' (incr p) y

  lfreshen' p (R x y) g =
    lfreshen' p x $ \ x' pm1 ->
      lfreshen' (incr p) (swaps' (incr p) pm1 y) $ \ y' pm2 ->
        g (R x' y') (pm1 <> pm2)

  freshen' p (R x y) = do
      (x', pm1) <- freshen' p x
      (y', pm2) <- freshen' (incr p) (swaps' (incr p) pm1 y)
      return (R x' y', pm1 <> pm2)

  aeq' p (R x1 y1) (R x2 y2 ) = do 
      aeq' p x1 x2 && aeq' p y1 y2

  match' p (R x1 y1) (R x2 y2) = do
     px <- match' p x1 x2
     py <- match' (incr p)  y1 y2
     (px `join` py)

  acompare' c (R a1 a2) (R b1 b2) = 
      lexord (acompare' c a1 b1) (acompare' (incr c) a2 b2)


  open c a (R x y)  = R (open c a x) (open (incr c) a y)
  close c a (R x y) = R (close c a x) (close (incr c) a y)

  findpatrec (R x y) nm =
     case findpatrec x nm of
         (i, True) -> (i, True)
         (i, False) -> case findpatrec y nm of
                         (j, True) -> (i + j, True)
                         (j, False) -> (i+j, False)

  nthpatrec (R x y) i =
      case nthpatrec x i of
        (j , Just n) -> (j, Just n)
        (j , Nothing) -> nthpatrec y j

-- note: for Annots, when the mode is "term" then we are 
-- implementing the "binding" version of the function
-- and we generally should treat the annots as constants
instance Alpha a => Alpha (Annot a) where
   swaps' c pm (Annot t) | mode c == Pat  = Annot (swaps' (term c) pm t)
   swaps' c pm (Annot t) | mode c == Term = Annot t 

   fv' c (Annot t) | mode c == Pat  = fv' (term c) t
   fv' c _         | mode c == Term = mempty

   freshen' c (Annot t) | mode c == Pat = do
       (t', p) <- freshen' (term c) t
       return (Annot t', p)
   freshen' c a | mode c == Term = return (a, empty)

   lfreshen' c a f
     | mode c == Term = f a empty
     | mode c == Pat  = error "lfreshen' called on Annot in Pat mode!?"

   aeq' c (Annot x) (Annot y) | mode c == Pat = aeq' (term c) x y
   aeq' c (Annot x) (Annot y) | mode c == Term = aeq' (term c) x y -- yes, exactly the same

   acompare' c (Annot x) (Annot y) = acompare' (term c) x y

   match' c (Annot x) (Annot y) | mode c == Pat  = match' (term c) x y
   match' c (Annot x) (Annot y) | mode c == Term = 
                                    if x `aeq` y
                                    then Just empty
                                    else Nothing

   close c b (Annot x) | mode c == Pat  = Annot (close (term c) b x)
                       | mode c == Term = error "close on Annot"

   open c b (Annot x) | mode c == Pat  = Annot (open (term c) b x)
                      | mode c == Term = error "open on Annot"


   findpatrec _ _ = (0, False)
   nthpatrec nm i = (i, Nothing)


instance Alpha a => Alpha (Rec a) where
   -- default definitions suffice

-- Instances for other types use the default definitions.
instance Alpha Bool
instance Alpha Float
instance Alpha ()
instance Alpha a => Alpha [a]
instance Alpha Int
instance Alpha Integer
instance Alpha Double
instance Alpha Char
instance Alpha a => Alpha (Maybe a)
instance (Alpha a,Alpha b) => Alpha (Either a b)
instance (Alpha a,Alpha b) => Alpha (a,b)
instance (Alpha a,Alpha b,Alpha c) => Alpha (a,b,c)
instance (Alpha a, Alpha b,Alpha c, Alpha d) => Alpha (a,b,c,d)
instance (Alpha a, Alpha b,Alpha c, Alpha d, Alpha e) =>
   Alpha (a,b,c,d,e)

instance (Rep a) => Alpha (R a)

----------------------------------------------------------
-- Binding operations & instances
----------------------------------------------------------
-- | A smart constructor for binders, also sometimes known as
-- \"close\".
bind ::(Alpha b, Alpha c) => b -> c -> Bind b c
bind b c = B b (close initial b c)

-- | A destructor for binders that does /not/ guarantee fresh
--   names for the binders.
unsafeUnbind :: (Alpha a, Alpha b) => Bind a b -> (a,b)
unsafeUnbind (B a b) = (a, open initial a b)

instance (Alpha a, Alpha b, Read a, Read b) => Read (Bind a b) where
         readPrec = R.parens $ (R.prec app_prec $ do
                                  R.Ident "<" <- R.lexP
                                  m1 <- R.step R.readPrec
                                  R.Ident ">" <- R.lexP
                                  m2 <- R.step R.readPrec
                                  return (bind m1 m2))
           where app_prec = 10

         readListPrec = R.readListPrecDefault

instance (Show a, Show b) => Show (Bind a b) where
  showsPrec p (B a b) = showParen (p>0)
      (showString "<" . showsPrec p a . showString "> " . showsPrec 0 b)

----------------------------------------------------------
-- Rebinding operations
----------------------------------------------------------

-- | Constructor for binding in patterns.
rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind a b = R a (close (pat initial) a b)

-- | Compare for alpha-equality.
instance (Alpha a, Alpha b, Eq b) => Eq (Rebind a b) where
   b1 == b2 = b1 `aeqBinders` b2

instance (Show a, Show b) => Show (Rebind a b) where
  showsPrec p (R a b) = showParen (p>0)
      (showString "<<" . showsPrec p a . showString ">> " . showsPrec 0 b)

-- | Destructor for `Rebind`.  It does not need a monadic context for
--   generating fresh names, since `Rebind` can only occur in the
--   pattern of a `Bind`; hence a previous call to `open` must have
--   already freshened the names at this point.
unrebind :: (Alpha a, Alpha b) => Rebind a b -> (a, b)
unrebind (R a b) = (a, open (pat initial) a b)

----------------------------------------------------------
-- Rec operations
----------------------------------------------------------

rec :: (Alpha a) => a -> Rec a 
rec a = Rec (rebind xs a) where
              xs = fv' initial a 

unrec :: (Alpha a) => Rec a -> a 
unrec (Rec rbnd) = snd (unrebind a)

instance Show a => Show (Rec a) where
  showsPrec p (Rec a) = showString "[" . showsPrec 0 a . showString "]"

----------------------------------------------------------
-- Annot
----------------------------------------------------------

instance Show a => Show (Annot a) where
  showsPrec p (Annot a) = showString "{" . showsPrec 0 a . showString "}"

----------------------------------------------------------
-- Wrappers for operations in the Alpha class
----------------------------------------------------------
-- | Determine alpha-equivalence of terms
aeq :: Alpha a => a -> a -> Bool
aeq t1 t2 = aeq' initial t1 t2

-- | Determine (alpha-)equivalence of patterns
-- Do they bind the same variables and have alpha-equal annotations?
aeqBinders :: Alpha a => a -> a -> Bool
aeqBinders t1 t2 = aeq' initial t1 t2

-- | Calculate the free variables (of any sort) contained in a term.
fvAny :: (Alpha a, Pointed f, Monoid (f AnyName)) => a -> f (AnyName)
fvAny = fv' initial

-- | Calculate the free variables of a particular sort contained in a term.
fv :: forall a b f.
      (Rep b, Alpha a,
       Pointed f, F.Foldable f, Monoid (f AnyName), Monoid (f (Name b)))
      => a -> f (Name b)
fv = fromList . catMaybes . map toSortedName . F.toList . (fv' initial :: a -> f AnyName)

-- | List all the binding variables (of a particular sort) in a pattern.
binders :: (Rep a, Alpha b) => b -> [Name a]
binders = fv

-- | Set of variables of a particular sort that occur freely in
--   annotations (not bindings).
patfv :: (Rep a, Alpha b) => b -> Set (Name a)
patfv = S.map fromJust . S.filter isJust . S.map toSortedName . fv' (pat initial)


-- | Apply a permutation to a term.
swaps :: Alpha a => Perm AnyName -> a -> a
swaps = swaps' initial

-- | Apply a permutation to the binding variables in a pattern.
-- Annotations are left alone by the permutation.
swapsBinders :: Alpha a => Perm AnyName -> a -> a
swapsBinders = swaps' initial

-- | Apply a permutation to the annotations in a pattern. Binding
-- names are left alone by the permutation.
swapsAnnots :: Alpha a => Perm AnyName -> a -> a
swapsAnnots = swaps' (pat initial)


-- | \"Locally\" freshen a term.  TODO: explain this type signature a bit better.
lfreshen :: (Alpha a, LFresh m) => a -> (a -> Perm AnyName -> m b) -> m b
lfreshen = lfreshen' initial

-- | Freshen a term by replacing all old /binding/ 'Name's with new
-- fresh 'Name's, returning a new term and a @'Perm' 'Name'@
-- specifying how 'Name's were replaced.
freshen :: (Fresh m, Alpha a) => a -> m (a, Perm AnyName)
freshen = freshen' initial

-- | Compare two data structures and produce a permutation of their
-- 'Name's that will make them alpha-equivalent to each other ('Name's
-- that appear in annotations must match exactly).  Return 'Nothing'
-- if no such renaming is possible.  Note that two terms are
-- alpha-equivalent if the empty permutation is returned.
match   :: Alpha a => a -> a -> Maybe (Perm AnyName)
match   = match' initial

-- | Compare two patterns, ignoring the names of binders, and produce
-- a permutation of their annotations to make them alpha-equivalent
-- to eachother. Return 'Nothing' if no such renaming is possible.
matchAnnots :: Alpha a => a -> a -> Maybe (Perm AnyName)
matchAnnots = match' (pat initial)

-- | Compare two patterns for equality and produce a permutation of
-- their binding 'Names' to make them alpha-equivalent to each other
-- ('Name's that appear in annotations must match exactly). Return
-- 'Nothing' if no such renaming is possible.
matchBinders ::  Alpha a => a -> a -> Maybe (Perm AnyName)
matchBinders = match' initial


-- | @'nthpat' b n@ looks up up the @n@th name in the pattern @b@
-- (zero-indexed).  PRECONDITION: the number of names in the pattern
-- must be at least @n@.
nthpat :: Alpha a => a -> Integer -> AnyName
nthpat x i = case nthpatrec x i of
                 (j, Nothing) -> error
                   ("BUG: pattern index " ++ show i ++ " out of bounds by " ++ show j ++ "in" ++ show x)
                 (_, Just n)  -> n

-- | Find the (first) index of the name in the pattern, if it exists.
findpat :: Alpha a => a -> AnyName -> Maybe Integer
findpat x n = case findpatrec x n of
                   (i, True) -> Just i
                   (_, False) -> Nothing

-- | An alpha-respecting total order on terms involving binders.
acompare :: Alpha a => a -> a -> Ordering
acompare x y = acompare' initial x y

------------------------------------------------------------
-- Opening binders
------------------------------------------------------------

-- | Unbind (also known as \"open\") is the destructor for
-- bindings. It ensures that the names in the binding are fresh.
unbind  :: (Fresh m, Alpha b, Alpha c) => Bind b c -> m (b,c)
unbind (B b c) = do
      (b', _) <- freshen b
      return (b', open initial b' c)

-- | Unbind two terms with the same fresh names, provided the
--   binders have the same number of binding variables.
unbind2  :: (Fresh m, Alpha b1, Alpha b2, Alpha c, Alpha d) =>
            Bind b1 c -> Bind b2 d -> m (Maybe (b1,c,b2,d))
unbind2 (B b1 c) (B b2 d) = do
      case match (fvAny b1 :: [AnyName]) (fvAny b2) of
         Just p -> do
           (b1', p') <- freshen b1
           return $ Just (b1', open initial b1' c,
                          swaps (p' <> p) b2, open initial b1' d)
         Nothing -> return Nothing

-- | Unbind three terms with the same fresh names, provided the
--   binders have the same number of binding variables.
unbind3  :: (Fresh m, Alpha b1, Alpha b2, Alpha b3, Alpha c, Alpha d, Alpha e) =>
            Bind b1 c -> Bind b2 d -> Bind b3 e ->  m (Maybe (b1,c,b2,d,b3,e))
unbind3 (B b1 c) (B b2 d) (B b3 e) = do
      case ( match (fvAny b1 :: [AnyName]) (fvAny b2)
           , match (fvAny b1 :: [AnyName]) (fvAny b3) ) of
         (Just p12, Just p13) -> do
           (b1', p') <- freshen b1
           return $ Just (b1', open initial b1' c,
                          swaps (p' <> p12) b2, open initial b1' d,
                          swaps (p' <> p13) b3, open initial b1' e)
         _ -> return Nothing

-- | Destruct a binding in an 'LFresh' monad.
lunbind :: (LFresh m, Alpha a, Alpha b) => Bind a b -> ((a, b) -> m c) -> m c
lunbind (B a b) g =
  lfreshen a (\x _ -> g (x, open initial x b))


-- | Unbind two terms with the same fresh names, provided the
--   binders have the same number of binding variables.
lunbind2  :: (LFresh m, Alpha b1, Alpha b2, Alpha c, Alpha d) =>
            Bind b1 c -> Bind b2 d -> (Maybe (b1,c,b2,d) -> m e) -> m e
lunbind2 (B b1 c) (B b2 d) g =
  case match (fvAny b1 :: [AnyName]) (fvAny b2) of
    Just p1 ->
      lfreshen b1 (\b1' p2 -> g $ Just (b1', open initial b1' c,
                                        swaps (p2 <> p1) b2, open initial b1' d))
    Nothing -> g Nothing

-- | Unbind three terms with the same fresh names, provided the
--   binders have the same number of binding variables.
lunbind3  :: (LFresh m, Alpha b1, Alpha b2, Alpha b3, Alpha c, Alpha d, Alpha e) =>
            Bind b1 c -> Bind b2 d -> Bind b3 e ->  (Maybe (b1,c,b2,d,b3,e) -> m f) -> m f
lunbind3 (B b1 c) (B b2 d) (B b3 e) g =
  case ( match (fvAny b1 :: [AnyName]) (fvAny b2)
       , match (fvAny b1 :: [AnyName]) (fvAny b3) ) of
         (Just p12, Just p13) ->
           lfreshen b1 (\b1' p' -> g $ Just (b1', open initial b1' c,
                                             swaps (p' <> p12) b2, open initial b1' d,
                                             swaps (p' <> p13) b3, open initial b1' e))
         _ -> g Nothing

------------------------------------------------------------
-- Substitution
------------------------------------------------------------

data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b


-- | The 'Subst' class governs capture-avoiding substitution.  To
--   derive this class, you only need to indicate where the variables
--   are in the data type, by overriding the method 'isvar'.
class (Rep1 (SubstD b) a) => Subst b a where

  -- | If the argument is a variable, return its name wrapped in the
  --   'SubstName' constructor.  Return 'Nothing' for
  --   non-variable arguments.

  -- why not isvar:: (a ~ b) => a -> Maybe (Name b) ??
  isvar :: a -> Maybe (SubstName a b)
  isvar x = Nothing

  -- | @'subst' nm sub tm@ substitutes @sub@ for @nm@ in @tm@.
  subst :: Name b -> b -> a -> a
  subst n u x =
     case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) -> if  m == n then u else x
        Nothing -> substR1 rep1 n u x

  -- | Perform several simultaneous substitutions.
  substs :: [Name b] -> [b] -> a -> a
  substs ns us x =
      case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) ->
          if length ns /= length us
            then error "BUG: Number of vars and terms must match in multisubstitution"
            else case m `List.elemIndex` ns of
               Just i  -> (us !! i)
               Nothing -> x
        Nothing -> substsR1 rep1 ns us x

-- | Reified class dictionary for 'Subst'.
data SubstD b a = SubstD {
  isvarD  :: a -> Maybe (SubstName a b),
  substD  ::  Name b -> b -> a -> a ,
  substsD :: [Name b] -> [b] -> a -> a
}

instance Subst b a => Sat (SubstD b a) where
  dict = SubstD isvar subst substs

substDefault :: Rep1 (SubstD b) a => Name b -> b -> a -> a
substDefault = substR1 rep1

substR1 :: R1 (SubstD b) a -> Name b -> b -> a -> a
substR1 (Data1 dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substD w x y) rec kids
      in (to c z)
substR1 r               = \ x y c -> c

substsR1 :: R1 (SubstD b) a -> [Name b] -> [b] -> a -> a
substsR1 (Data1 dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substsD w x y) rec kids
      in (to c z)
substsR1 r               = \ x y c -> c

instance Subst b Int
instance Subst b Bool
instance Subst b ()
instance Subst b Char
instance Subst b Integer
instance Subst b Float
instance Subst b Double

instance Subst b AnyName
instance Rep a => Subst b (R a)
instance Rep a => Subst b (Name a)

instance (Subst c a, Subst c b) => Subst c (a,b)
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d)
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e)
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f)
instance (Subst c a) => Subst c [a]
instance (Subst c a) => Subst c (Maybe a)
instance (Subst c a, Subst c b) => Subst c (Either a b)

instance (Subst c b, Subst c a, Alpha a,Alpha b) =>
    Subst c (Bind a b)
instance (Subst c b, Subst c a, Alpha a, Alpha b) =>
    Subst c (Rebind a b)

instance (Subst c a) => Subst c (Annot a)
instance (Subst c a) => Subst c (Rec a)

-------------------- TESTING CODE --------------------------------
data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp) deriving (Show)

$(derive [''Exp])

instance Alpha Exp
instance Subst Exp Exp where
   isvar (V n) = Just (SubstName n)
   isvar _     = Nothing

nameA, nameB, nameC :: Name Exp
nameA = integer2Name 1
nameB = integer2Name 2
nameC = integer2Name 3

assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
   tests_aeq
   tests_fv
   tests_big
   tests_nth
   tests_acompare

perm = single nameA nameB

naeq x y = not (aeq x y)

tests_aeq = do
   assert "a1" $ (bind nameA nameA) `naeq` (bind nameA nameB)
   assert "a2" $ (bind nameA nameA) `aeq` (bind nameA nameA)
   assert "a3" $ (bind nameA nameA) `aeq` (bind nameB nameB)
   assert "a4" $ (bind nameA nameB) `naeq` (bind nameB nameA)
   assert "a5" $ (bind (nameA, Annot nameB) nameA) `naeq`
                 (bind (nameA, Annot nameC) nameA)
   assert "a6" $ (bind (nameA, Annot nameB) nameA) `aeq`
                 (bind (nameA, Annot nameB) nameA)
   assert "a7" $ (bind (nameA, Annot nameB) nameA) `aeq`
                 (bind (nameB, Annot nameB) nameB)
   assert "a8" $ rebind nameA nameB `naeq` rebind nameB nameB
   assert "a9" $ rebind nameA nameA `naeq` rebind nameB nameB
   assert "a9" $ (bind (rebind nameA (Annot nameA)) nameA) `aeq`
                 (bind (rebind nameB (Annot nameB)) nameB)
   assert "a10" $ bind (rebind (nameA, Annot nameA) ()) nameA `aeq`
                  bind (rebind (nameB, Annot nameA) ()) nameB
   assert "a11" $ bind (rebind (nameA, Annot nameA) ()) nameA `naeq`
                  bind (rebind (nameB, Annot nameB) ()) nameB
   assert "a12" $ bind (Annot nameA) () `naeq` bind (Annot nameB) ()
   assert "a13" $ bind (Annot nameA) () `aeq` bind (Annot nameA) ()
   assert "a14" $ bind (rebind (Annot nameA) ()) () `naeq`
                  bind (rebind (Annot nameB) ()) ()
   assert "a15" $ (rebind (nameA, Annot nameA) ()) `naeq`
                  (rebind (name4, Annot nameC) ())
   assert "a16" $ bind (nameA, nameB) nameA `naeq` bind (nameB, nameA) nameA
   assert "a17" $ bind (nameA, nameB) nameA `naeq` bind (nameA, nameB) nameB
   assert "a18" $ (nameA, nameA) `naeq` (nameA, nameB)
   assert "a19" $ match (nameA, nameA) (nameB, nameC) == Nothing

emptyNE :: Set (Name Exp)
emptyNE = S.empty

tests_fv = do
   assert "f1" $ fv (bind nameA nameA) == emptyNE
   assert "f2" $ fv' (pat initial) (bind nameA nameA) == S.empty
   assert "f4" $ fv (bind nameA nameB) == S.singleton nameB
   assert "f5" $ fv (bind (nameA, Annot nameB) nameA) == S.singleton nameB
   assert "f7" $ fv (bind (nameB, Annot nameB) nameB) == S.singleton nameB
   assert "f8" $ fv (rebind nameA nameB) == S.fromList [nameA, nameB]
   assert "f9" $ fv' (pat initial) (rebind nameA nameA) == S.empty
   assert "f3" $ fv (bind (rebind nameA (Annot nameA)) nameA) == emptyNE
   assert "f10" $ fv (rebind (nameA, Annot nameA) ()) == S.singleton nameA
   assert "f11" $ fv' (pat initial) (rebind (nameA, Annot nameA) ()) == S.singleton (AnyName nameA)
   assert "f12" $ fv (bind (Annot nameA) ()) == S.singleton nameA
   assert "f14" $ fv (rebind (Annot nameA) ()) == emptyNE

mkbig :: [Name Exp] -> Exp -> Exp
mkbig (n : names) body =
    L (bind n (mkbig names (A (V n) body)))
mkbig [] body = body

big1 = mkbig (map integer2Name (take 100 [1 ..])) (V name11)
big2 = mkbig (map integer2Name (take 101 [1 ..])) (V name11)


tests_nth = do
  assert "n1" $ nthpat ([nameA],nameB) 0 == AnyName nameA
  assert "n2" $ nthpat ([nameA],nameB) 1 == AnyName nameB
  assert "n3" $ nthpat (nameA, nameB) 0 == AnyName nameA
  assert "p1" $ findpat ([nameA],nameB) (AnyName nameA) == Just 0
  assert "p2" $ findpat ([nameA],nameB) (AnyName nameB) == Just 1
  assert "p3" $ findpat ([nameA],nameB) (AnyName nameC) == Nothing

tests_big = do
   assert "b1" $ big1 `naeq` big2
   assert "b2" $ fv big1 == emptyNE
   assert "b3" $ big1 `aeq` subst name11 (V name11) big1

tests_acompare = do
   -- Names compare in the obvious way.
   assert "ac1" $ acompare nameA nameB == LT
   assert "ac2" $ acompare nameB nameB == EQ
   assert "ac3" $ acompare nameB nameA == GT
   -- structured date compares lexicographically
   assert "ac4" $ acompare (A (V nameA) (V nameA)) (A (V nameA) (V nameA)) == EQ
   assert "ac5" $ acompare (A (V nameA) (V nameA)) (A (V nameA) (V nameB)) == LT
   assert "ac6" $ acompare (A (V nameA) (V nameB)) (A (V nameA) (V nameA)) == GT
   assert "ac7" $ acompare (A (V nameA) (V nameA)) (A (V nameB) (V nameA)) == LT
   assert "ac8" $ acompare (A (V nameB) (V nameA)) (A (V nameA) (V nameA)) == GT
   assert "ac9" $ acompare (A (V nameB) (V nameA)) (A (V nameA) (V nameB)) == GT
   -- comparison goes under binders, alpha-respectingly.
   assert "ac10" $ acompare (bind nameA (A (V nameA) (V nameA))) (bind nameA (A (V nameA) (V nameA))) == EQ
   assert "ac11" $ acompare (bind nameA (A (V nameA) (V nameA))) (bind nameA (A (V nameA) (V nameB))) == GT
   assert "ac12" $ acompare (bind nameC (A (V nameC) (V nameA))) (bind nameA (A (V nameA) (V nameB))) == LT
   -- non-matching binders handled alpha-respectingly.
   assert "ac13" $ acompare (bind [nameA] nameA) (bind [nameA,nameB] nameA)
                 ==  acompare (bind [nameC] nameC) (bind [nameA,nameB] nameA)
   assert "ac14" $ acompare (bind [nameA,nameB] nameA) (bind [nameA] nameA)
                 ==  acompare (bind [nameC,nameB] nameC) (bind [nameA] nameA)
   -- non-binding stuff in patterns gets compared
   assert "ac15" $ acompare (Annot nameA) (Annot nameB) == LT
   assert "ac16" $ acompare (bind (nameC, Annot nameA) (A (V nameC) (V nameC)))
                            (bind (nameC, Annot nameB) (A (V nameC) (V nameC))) == LT
   assert "ac17" $ acompare (bind (nameC, Annot nameA) (A (V nameB) (V nameB)))
                          (bind (nameC, Annot nameB) (A (V nameA) (V nameA))) == LT
   -- TODO: do we need anything special for rebind? For AnyName?

-- properties
-- if match t1 t2 = Some p then swaps p t1 = t2

-- $paynoattention
-- These type representation objects are exported so they can be
-- referenced by auto-generated code.  Please pretend they do not
-- exist.