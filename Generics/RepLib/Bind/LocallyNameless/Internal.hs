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
-- Module      :  Generics.RepLib.Bind.LocallyNameless.Internal
-- License     :  BSD-like (see LICENSE)
--
----------------------------------------------------------------------

module Generics.RepLib.Bind.LocallyNameless.Internal where

import Generics.RepLib hiding (GT)
import Generics.RepLib.Bind.PermM
import Generics.RepLib.Bind.LocallyNameless.Name
import Generics.RepLib.Bind.LocallyNameless.Fresh

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

(<>) :: Monoid m => m -> m -> m
(<>) = mappend

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
data Bind p t = B p t

-- | 'Rebind' supports \"telescopes\" --- that is, patterns where
--   bound variables appear in multiple subterms.
data Rebind p1 p2 = R p1 p2

-- | 'Rec' supports recursive patterns --- that is, patterns where
-- any variables anywhere in the pattern are bound in the pattern
-- itself.  Useful for lectrec (and Agda's dot notation).
data Rec p = Rec p

-- | An annotation is a \"hole\" in a pattern where variables can be
--   used, but not bound. For example, patterns may include type
--   annotations, and those annotations can reference variables
--   without binding them.  Annotations do nothing special when they
--   appear elsewhere in terms.
newtype Annot t = Annot t deriving Eq

-- | An outer can shift an annotation \"hole\" to refer to higher context.
newtype Outer p = Outer p deriving Eq


$(derive [''Bind, ''Name, ''Annot, ''Rebind, ''Rec, ''Outer])

--------------------------------------------------
-- Collections
--------------------------------------------------

-- | Collections are foldable types that support empty, singleton, and
--   union operations.  The result of a free variable calculation may be
--   any collection.  Instances are provided for lists and sets.
class F.Foldable f => Collection f where
  emptyC    :: f a
  singleton :: a -> f a
  union     :: Ord a => f a -> f a -> f a

unions :: (Ord a, Collection f) => [f a] -> f a
unions = foldr union emptyC

fromList :: (Ord a, Collection f) => [a] -> f a
fromList = unions . map singleton

instance Collection [] where
  emptyC    = []
  singleton = (:[])
  union     = (++)

instance Collection S.Set where
  emptyC    = S.empty
  singleton = S.singleton
  union     = S.union

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
  fv' :: Collection f => AlphaCtx -> a -> f AnyName
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

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid
  --   pattern.  The default instance returns @True@ if at all
  --   possible.
  isPat :: a -> Bool
  isPat = isPatR1 rep1

  -- | @isTerm x@ dynamically checks whether @x@ can be used as a
  --   valid term. The default instance returns @True@ if at all
  --   possible.
  isTerm :: a -> Bool
  isTerm = isTermR1 rep1

  -- | @isAnnot@ is needed internally for the implementation of
  --   @isPat@.  @isAnnot@ is true for terms wrapped in @Annot@ and zero
  --   or more occurrences of @Outer@.  The default implementation
  --   simply returns @False@.
  isAnnot :: a -> Bool
  isAnnot _ = False
  ---------------- PATTERN OPERATIONS ----------------------------

  -- | @'nthpatrec' p n@ looks up the @n@th name in the pattern @p@
  -- (zero-indexed), returning the number of names encountered if not
  -- found.
  nthpatrec :: a -> NthCont
  nthpatrec = nthpatR1 rep1

  -- | Find the (first) index of the name in the pattern if one
  --   exists; otherwise, return the number of names encountered
  --   instead.
  findpatrec :: a -> AnyName -> FindResult
  findpatrec = findpatR1 rep1

------------------------------------------------------------
--  Pattern operation internals
------------------------------------------------------------

-- | The result of a 'findpatrec' operation.
data FindResult = Index Integer      -- ^ The (first) index of the name we
                                     --   sought
                | NamesSeen Integer  -- ^ We haven't found the name
                                     --   (yet), but have seen this many
                                     --   others while looking for it
  deriving (Eq, Ord, Show)

-- | @FindResult@ forms a monoid which combines information from
--   several 'findpatrec' operations.  @mappend@ takes the leftmost
--   'Index', and combines the number of names seen to the left of it
--   so we can correctly compute its global index.
instance Monoid FindResult where
  mempty = NamesSeen 0
  NamesSeen i `mappend` NamesSeen j = NamesSeen (i + j)
  NamesSeen i `mappend` Index j     = Index (i + j)
  Index j     `mappend` _           = Index j

-- | The result of an 'nthpatrec' operation.
data NthResult = Found AnyName    -- ^ The name found at the given
                                  --   index.
               | CurIndex Integer -- ^ We haven't yet reached the
                                  --   required index; this is the
                                  --   index into the remainder of the
                                  --   pattern (which decreases as we
                                  --   traverse the pattern).

-- | A continuation which takes the remaining index and searches for
--   that location in a pattern, yielding a name or a remaining index
--   if the end of the pattern was reached too soon.
newtype NthCont = NthCont { runNthCont :: Integer -> NthResult }

-- | @NthCont@ forms a monoid: function composition which
--   short-circuits once a result is found.
instance Monoid NthCont where
  mempty = NthCont $ \i -> CurIndex i
  (NthCont f) `mappend` (NthCont g)
    = NthCont $ \i -> case f i of
                        Found n     -> Found n
                        CurIndex i' -> g i'

-- | If we see a name, check whether the index is 0: if it is, we've
--   found the name we're looking for, otherwise continue with a
--   decremented index.
nthName :: AnyName -> NthCont
nthName nm = NthCont $ \i -> if i == 0
                               then Found nm
                               else CurIndex (i-1)

------------------------------------------------------------
--  AlphaCtx
------------------------------------------------------------

-- An AlphaCtx records the current mode (Term/Pat) and current level,
-- and gets passed along during operations which need to keep track of
-- the mode and/or level.

-- | Many of the operations in the 'Alpha' class take an 'AlphaCtx':
-- stored information about the iteration as it progresses. This type
-- is abstract, as classes that override these operations should just pass
-- the context on.
data AlphaCtx = AC { mode :: Mode , level :: Integer }

initial :: AlphaCtx
initial = AC Term 0

incr :: AlphaCtx -> AlphaCtx
incr c = c { level = level c + 1 }

decr :: AlphaCtx -> AlphaCtx
decr c = if level c == 0 then error "Too many outers"
         else c { level = level c - 1 }


pat  :: AlphaCtx -> AlphaCtx
pat c  = c { mode = Pat }

term  :: AlphaCtx -> AlphaCtx
term c  = c { mode = Term }

-- | A mode is basically a flag that tells us whether we should be
--   looking at the names in the term, or if we are in a pattern and
--   should /only/ be looking at the names in the annotations. The
--   standard mode is to use 'Term'; many functions do this by default.
data Mode = Term | Pat deriving (Show, Eq, Read)

-- | Open a term using the given pattern.
openT :: (Alpha p, Alpha t) => p -> t -> t
openT = open initial

-- | @openP p1 p2@ opens the pattern @p2@ using the pattern @p1@.
openP :: (Alpha p1, Alpha p2) => p1 -> p2 -> p2
openP = open (pat initial)

-- | Close a term using the given pattern.
closeT :: (Alpha p, Alpha t) => p -> t -> t
closeT = close initial

-- | @closeP p1 p2@ closes the pattern @p2@ using the pattern @p1@.
closeP :: (Alpha p1, Alpha p2) => p1 -> p2 -> p2
closeP = close (pat initial)

-- | Class constraint hackery to allow us to override the default
--   definitions for certain classes.  'AlphaD' is essentially a
--   reified dictionary for the 'Alpha' class.
data AlphaD a = AlphaD {
  isPatD    :: a -> Bool,
  isTermD   :: a -> Bool,
  isAnnotD  :: a -> Bool,
  swapsD    :: AlphaCtx -> Perm AnyName -> a -> a,
  fvD       :: Collection f => AlphaCtx -> a -> f AnyName,
  freshenD  :: forall m. Fresh m => AlphaCtx -> a -> m (a, Perm AnyName),
  lfreshenD :: forall b m. LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b,
  aeqD      :: AlphaCtx -> a -> a -> Bool,
  matchD    :: AlphaCtx -> a -> a -> Maybe (Perm AnyName),
  closeD    :: Alpha b => AlphaCtx -> b -> a -> a,
  openD     :: Alpha b => AlphaCtx -> b -> a -> a,
  findpatD  :: a -> AnyName -> FindResult,
  nthpatD   :: a -> NthCont,
  acompareD :: AlphaCtx -> a -> a -> Ordering
  }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD isPat isTerm isAnnot swaps' fv' freshen' lfreshen' aeq' match'
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


fvR1 :: Collection f => R1 (AlphaD) a -> AlphaCtx -> a -> f AnyName
fvR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> fv1 rec p kids
fvR1 _ = \ _ _ -> emptyC

fv1 :: Collection f => MTup (AlphaD) l -> AlphaCtx -> l -> f AnyName
fv1 MNil _ Nil = emptyC
fv1 (r :+: rs) p (p1 :*: t1) =
   fvD r p p1 `union` fv1 rs p t1


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


findpatR1 :: R1 AlphaD b -> b -> AnyName -> FindResult
findpatR1 (Data1 dt cons) = \ d n ->
   case findCon cons d of
     Val c rec kids -> findpatL rec kids n
findpatR1 _ = \ x n -> mempty

findpatL :: MTup AlphaD l -> l -> AnyName -> FindResult
findpatL MNil Nil n              = mempty
findpatL (r :+: rs) (t :*: ts) n = findpatD r t n <> findpatL rs ts n

nthpatR1 :: R1 AlphaD b -> b -> NthCont
nthpatR1 (Data1 dt cons) = \ d ->
   case findCon cons d of
     Val c rec kids -> nthpatL rec kids
nthpatR1 _ = \ x -> mempty

nthpatL :: MTup AlphaD l -> l -> NthCont
nthpatL MNil Nil              = mempty
nthpatL (r :+: rs) (t :*: ts) = nthpatD r t <> nthpatL rs ts

isPatR1 :: R1 AlphaD b -> b -> Bool
isPatR1 (Data1 dt cons) = \ d ->
   case findCon cons d of
     Val c rec kids -> foldl_l (\ c b a -> isPatD c a && b) True rec kids
isPatR1 _ = \ d -> True

isTermR1 :: R1 AlphaD b -> b -> Bool
isTermR1 (Data1 dt cons) = \ d ->
   case findCon cons d of
     Val c rec kids -> foldl_l (\ c b a -> isTermD c a && b) True rec kids
isTermR1 _ = \ d -> True

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
-- Specific Alpha instances for the binding combinators:
--      Name, Bind, Annot, Rebind, Rec, Outer
-----------------------------------------------------------

-- In the Name instance, if the mode is Term then the operation
-- observes the name. In Pat mode the name is a binder, so the name is
-- usually ignored.
instance Rep a => Alpha (Name a) where

  -- Both bound and free names are valid terms.
  isTerm _ = True

  -- Only free names are valid as patterns, which serve as binders.
  isPat (Nm {}) = True
  isPat _       = False

  fv' c n@(Nm _ _)  | mode c == Term = singleton (AnyName n)
  fv' _ _                            = emptyC

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

  freshen' c nm | mode c == Pat  = do x <- fresh nm
                                      return (x, single (AnyName nm) (AnyName x))
  freshen' c nm | mode c == Term = error "freshen' on Name in Term mode"

  lfreshen' c nm f = case mode c of
     Pat  -> do x <- lfresh nm
                avoid [AnyName x] $ f x (single (AnyName nm) (AnyName x))
     Term -> error "lfreshen' on Name in Term mode"

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
      Just nm1' -> if nm1' == nm2 then Index 0 else NamesSeen 1
      Nothing   -> NamesSeen 1

  nthpatrec = nthName . AnyName

  acompare' c (Nm r1 n1)    (Nm r2 n2)
    | mode c == Term = lexord (compare r1 r2) (compare n1 n2)

  acompare' c (Bn r1 m1 n1) (Bn r2 m2 n2)
    | mode c == Term = lexord (compare r1 r2) (lexord (compare m1 m2) (compare n1 n2))

  acompare' c (Nm _ _)   (Bn _ _ _) | mode c == Term = LT
  acompare' c (Bn _ _ _) (Nm _ _)   | mode c == Term = GT
  acompare' c _          _          | mode c == Pat = EQ

instance Alpha AnyName  where

  isTerm _ = True

  isPat (AnyName (Nm {})) = True
  isPat _                 = False

  fv' c n@(AnyName (Nm _ _))  | mode c == Term = singleton n
  fv' _ _                                      = emptyC

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
     Pat  -> do x <- fresh nm
                return (AnyName x, single (AnyName nm) (AnyName x))
     Term -> error "freshen' on AnyName in Term mode"

  lfreshen' c (AnyName nm) f = case mode c of
     Pat  -> do x <- lfresh nm
                avoid [AnyName x] $ f (AnyName x) (single (AnyName nm) (AnyName x))
     Term -> error "lfreshen' on AnyName in Term mode"

  open c a (AnyName (Bn _ j x)) | level c == j = nthpat a x
  open _ _ n = n

  close c a nm@(AnyName (Nm r n)) =
    case findpat a nm of
      Just x  -> AnyName (Bn r (level c) x)
      Nothing -> nm

  close _ _ n = n

  findpatrec nm1 nm2 | nm1 == nm2 = Index 0
  findpatrec _ _ = NamesSeen 1

  nthpatrec = nthName

instance (Alpha p, Alpha t) => Alpha (Bind p t) where
    isPat _ = False
    isTerm (B p t) = isPat p && isTerm t

    swaps' c pm (B p t) =
        (B (swaps' (pat c) pm p)
           (swaps' (incr c) pm t))

    fv' c (B p t) = fv' (pat c) p `union` fv' (incr c) t

    freshen' c (B p t) = do
      (p', pm1) <- freshen' (pat c) p
      (t', pm2) <- freshen' (incr c) (swaps' (incr c) pm1 t)
      return (B p' t', pm1 <> pm2)

    lfreshen' c (B p t) f =
      lfreshen' (pat c) p (\ p' pm1 ->
      lfreshen' (incr c) (swaps' (incr c) pm1 t) (\ t' pm2 ->
      f (B p' t') (pm1 <> pm2)))

    aeq' c (B p1 t1) (B p2 t2) = do
      aeq' (pat c) p1 p2  && aeq' (incr c) t1 t2

    match' c (B p1 t1) (B p2 t2) = do
      pp <- match' (pat c) p1 p2
      pt <- match' (incr c) t1 t2
      -- need to make sure that all permutations of
      -- bound variables at this
      -- level are the identity
      (pp `join` pt)

    open  c a (B p t)    = B (open (pat c) a p)  (open  (incr c) a t)
    close c a (B p t)    = B (close (pat c) a p) (close (incr c) a t)

    --  Comparing two binding terms.
    acompare' c (B p1 t1) (B p2 t2) =
      lexord (acompare' (pat c) p1 p2) (acompare' (incr c) t1 t2)

    findpatrec _ b = error $ "Binding " ++ show b ++ " used as a pattern"
    nthpatrec    b = error $ "Binding " ++ show b ++ " used as a pattern"

instance (Alpha p, Alpha q) => Alpha (Rebind p q) where
  isTerm _ = False
  isPat (R p q) = isPat p && isPat q

  swaps' c pm (R p q) = R (swaps' c pm p) (swaps' (incr c) pm q)

  fv' c (R p q) =  fv' c p `union` fv' (incr c) q

  lfreshen' c (R p q) g
    | mode c == Term = error "lfreshen' on Rebind in Term mode"
    | otherwise =
        lfreshen' c p $ \ p' pm1 ->
        lfreshen' (incr c) (swaps' (incr c) pm1 q) $ \ q' pm2 ->
        g (R p' q') (pm1 <> pm2)

  freshen' c (R p q)
    | mode c == Term = error "freshen' on Rebind in Term mode"
    | otherwise = do
        (p', pm1) <- freshen' c p
        (q', pm2) <- freshen' (incr c) (swaps' (incr c) pm1 q)
        return (R p' q', pm1 <> pm2)

  aeq' c (R p1 q1) (R p2 q2 ) = do
      aeq' c p1 p2 && aeq' c q1 q2

  match' c (R p1 q1) (R p2 q2) = do
     pp <- match' c p1 p2
     pq <- match' (incr c)  q1 q2
     (pp `join` pq)

  acompare' c (R a1 a2) (R b1 b2) =
      lexord (acompare' c a1 b1) (acompare' (incr c) a2 b2)


  open c a (R p q)  = R (open c a p) (open (incr c) a q)
  close c a (R p q) = R (close c a p) (close (incr c) a q)

  findpatrec (R p q) nm = findpatrec p nm <> findpatrec q nm

  nthpatrec (R p q) = nthpatrec p <> nthpatrec q


instance Alpha p => Alpha (Rec p) where
   {-  default defs of these work if we don't care about incrs

   fv' c (Rec a) = fv' c a
   aeq' c (Rec a) (Rec b) = aeq' c a b
   acompare' c (Rec a) (Rec b) = acompare' c a b
   swaps' p pm (Rec a) = Rec (swaps' p pm a)
   findpatrec (Rec a) nm = findpatrec a nm
   nthpatrec (Rec a)  i  = nthpatrec a i

   -}
   isPat (Rec p) = isPat p
   isTerm _ = False

   open  c a (Rec p) = Rec (open  (incr c) a p)
   close c a (Rec p) = Rec (close (incr c) a p)


-- note: for Annots, when the mode is "term" then we are
-- implementing the "binding" version of the function
-- and we generally should treat the annots as constants
instance Alpha t => Alpha (Annot t) where
   isPat (Annot t)   = isTerm t
   isTerm t          = False
   isAnnot (Annot t) = isPat t

   swaps' c pm (Annot t) | mode c == Pat  = Annot (swaps' (term c) pm t)
   swaps' c pm (Annot t) | mode c == Term = Annot t

   fv' c (Annot t) | mode c == Pat  = fv' (term c) t
   fv' c _         | mode c == Term = emptyC

   freshen' c p | mode c == Term = error "freshen' called on a term"
                | otherwise      = return (p, empty)

   lfreshen' c p f         | mode c == Term = error "lfreshen' called on a term"
                           | otherwise      = f p empty

   aeq' c (Annot x) (Annot y) = aeq' (term c) x y

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

   findpatrec _ _ = mempty
   nthpatrec _    = mempty


instance Alpha a => Alpha (Outer a) where

  -- The contents of Outer may only be an Annot or another Outer.
  isPat (Outer a)   = isAnnot a
  isTerm a          = False
  isAnnot (Outer a) = isAnnot a

  close c b (Outer x) = Outer (close (decr c) b x)
  open  c b (Outer x) = Outer (open  (decr c) b x)


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
bind :: (Alpha c, Alpha b) => b -> c -> Bind b c
bind b c = B b (closeT b c)

-- | A destructor for binders that does /not/ guarantee fresh
--   names for the binders.
unsafeUnbind :: (Alpha a, Alpha b) => Bind a b -> (a,b)
unsafeUnbind (B a b) = (a, openT a b)

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
rebind a b = R a (closeP a b)

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
unrebind (R a b) = (a, openP a b)

----------------------------------------------------------
-- Rec operations
----------------------------------------------------------

rec :: (Alpha a) => a -> Rec a
rec a = Rec (closeP a a) where

unrec :: (Alpha a) => Rec a -> a
unrec (Rec a) = openP a a

instance Show a => Show (Rec a) where
  showsPrec p (Rec a) = showString "[" . showsPrec 0 a . showString "]"

----------------------------------------------------------
-- Annot
----------------------------------------------------------

instance Show a => Show (Annot a) where
  showsPrec p (Annot a) = showString "{" . showsPrec 0 a . showString "}"

instance Show a => Show (Outer a) where
  showsPrec p (Outer a) = showString "{" . showsPrec 0 a . showString "}"

----------------------------------------------------------
-- Wrappers for operations in the Alpha class
----------------------------------------------------------

-- | Determine alpha-equivalence of terms.
aeq :: Alpha t => t -> t -> Bool
aeq t1 t2 = aeq' initial t1 t2

-- | Determine (alpha-)equivalence of patterns.  Do they bind the same
--   variables and have alpha-equal annotations?
aeqBinders :: Alpha p => p -> p -> Bool
aeqBinders p1 p2 = aeq' initial p1 p2

-- | An alpha-respecting total order on terms involving binders.
acompare :: Alpha t => t -> t -> Ordering
acompare x y = acompare' initial x y


-- | Calculate the free variables (of any sort) contained in a term.
fvAny :: (Alpha t, Collection f) => t -> f AnyName
fvAny = fv' initial

-- | Calculate the free variables of a particular sort contained in a
--   term.
fv :: forall a t f. (Rep a, Alpha t, Collection f) => t -> f (Name a)
fv = fromList
   . catMaybes
   . map toSortedName
   . F.toList
   . (fvAny :: t -> f AnyName)

-- | Calculate the variables (of any sort) that occur freely within
--   pattern annotations (but are not bound by the pattern).
patfvAny :: (Alpha p, Collection f) => p -> f AnyName
patfvAny = fv' (pat initial)

-- | Calculate the variables of a particular sort that occur freely in
--   pattern annotations (but are not bound by the pattern).
patfv :: forall a p f. (Rep a, Alpha p, Collection f) => p -> f (Name a)
patfv = fromList
      . catMaybes
      . map toSortedName
      . F.toList
      . (patfvAny :: p -> f AnyName)

-- | Calculate the binding variables (of any sort) in a pattern.
bindersAny :: (Alpha p, Collection f) => p -> f AnyName
bindersAny = fvAny

-- | Calculate the binding variables (of a particular sort) in a
--   pattern.
binders :: (Rep a, Alpha p, Collection f) => p -> f (Name a)
binders = fv


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


-- | \"Locally\" freshen a pattern replacing all binding names with
--  new names that have not already been used. The second argument is
-- a continuation, which takes the renamed term and a permutation that
-- specifies how the pattern has been renamed.
lfreshen :: (Alpha p, LFresh m) => p -> (p -> Perm AnyName -> m b) -> m b
lfreshen = lfreshen' (pat initial)

-- | Freshen a pattern by replacing all old /binding/ 'Name's with new
-- fresh 'Name's, returning a new pattern and a @'Perm' 'Name'@
-- specifying how 'Name's were replaced.
freshen :: (Alpha p, Fresh m) => p -> m (p, Perm AnyName)
freshen = freshen' (pat initial)

-- | Compare two terms and produce a permutation of their 'Name's that
-- will make them alpha-equivalent to each other.  Return 'Nothing' if
-- no such renaming is possible.  Note that two terms are
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
-- (Free 'Name's that appear in annotations must match exactly). Return
-- 'Nothing' if no such renaming is possible.
matchBinders ::  Alpha a => a -> a -> Maybe (Perm AnyName)
matchBinders = match' initial


-- | @'nthpat' b n@ looks up up the @n@th name in the pattern @b@
-- (zero-indexed).  PRECONDITION: the number of names in the pattern
-- must be at least @n@.
nthpat :: Alpha a => a -> Integer -> AnyName
nthpat x i = case runNthCont (nthpatrec x) i of
                 CurIndex j -> error
                   ("BUG: pattern index " ++ show i ++
                    " out of bounds by " ++ show j ++ "in" ++ show x)
                 Found nm   -> nm

-- | Find the (first) index of the name in the pattern, if it exists.
findpat :: Alpha a => a -> AnyName -> Maybe Integer
findpat x n = case findpatrec x n of
                   Index i     -> Just i
                   NamesSeen _ -> Nothing

------------------------------------------------------------
-- Opening binders
------------------------------------------------------------

-- | Unbind (also known as \"open\") is the destructor for
-- bindings. It ensures that the names in the binding are fresh.
unbind  :: (Fresh m, Alpha p, Alpha t) => Bind p t -> m (p,t)
unbind (B p t) = do
      (p', _) <- freshen p
      return (p', openT p' t)

-- | Unbind two terms with the same fresh names, provided the
--   binders have the same number of binding variables.
unbind2  :: (Fresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2) =>
            Bind p1 t1 -> Bind p2 t2 -> m (Maybe (p1,t1,p2,t2))
unbind2 (B p1 t1) (B p2 t2) = do
      case match (fvAny p1 :: [AnyName]) (fvAny p2) of
         Just p -> do
           (p1', p') <- freshen p1
           return $ Just (p1', openT p1' t1,
                          swaps (p' <> p) p2, openT p1' t2)
         Nothing -> return Nothing

-- | Unbind three terms with the same fresh names, provided the
--   binders have the same number of binding variables.
unbind3  :: (Fresh m, Alpha p1, Alpha p2, Alpha p3, Alpha t1, Alpha t2, Alpha t3) =>
            Bind p1 t1 -> Bind p2 t2 -> Bind p3 t3 ->  m (Maybe (p1,t1,p2,t2,p3,t3))
unbind3 (B p1 t1) (B p2 t2) (B p3 t3) = do
      case ( match (fvAny p1 :: [AnyName]) (fvAny p2)
           , match (fvAny p1 :: [AnyName]) (fvAny p3) ) of
         (Just p12, Just p13) -> do
           (p1', p') <- freshen p1
           return $ Just (p1', openT p1' t1,
                          swaps (p' <> p12) p2, openT p1' t2,
                          swaps (p' <> p13) p3, openT p1' t3)
         _ -> return Nothing

-- | Destruct a binding in an 'LFresh' monad.
lunbind :: (LFresh m, Alpha p, Alpha t) => Bind p t -> ((p, t) -> m c) -> m c
lunbind (B p t) g =
  lfreshen p (\x _ -> g (x, openT x t))


-- | Unbind two terms with the same fresh names, provided the
--   binders have the same number of binding variables.
lunbind2  :: (LFresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2) =>
            Bind p1 t1 -> Bind p2 t2 -> (Maybe (p1,t1,p2,t2) -> m r) -> m r
lunbind2 (B p1 t1) (B p2 t2) g =
  case match (fvAny p1 :: [AnyName]) (fvAny p2) of
    Just pm1 ->
      lfreshen p1 (\p1' pm2 -> g $ Just (p1', openT p1' t1,
                                         swaps (pm2 <> pm1) p2, openT p1' t2))
    Nothing -> g Nothing

-- | Unbind three terms with the same fresh names, provided the
--   binders have the same number of binding variables.
lunbind3 :: (LFresh m, Alpha p1, Alpha p2, Alpha p3, Alpha t1, Alpha t2, Alpha t3) =>
            Bind p1 t1 -> Bind p2 t2 -> Bind p3 t3 ->
            (Maybe (p1,t1,p2,t2,p3,t3) -> m r) ->
            m r
lunbind3 (B p1 t1) (B p2 t2) (B p3 t3) g =
  case ( match (fvAny p1 :: [AnyName]) (fvAny p2)
       , match (fvAny p1 :: [AnyName]) (fvAny p3) ) of
         (Just pm12, Just pm13) ->
           lfreshen p1 (\p1' pm' -> g $ Just (p1', openT p1' t1,
                                              swaps (pm' <> pm12) p2, openT p1' t2,
                                              swaps (pm' <> pm13) p3, openT p1' t3))
         _ -> g Nothing

------------------------------------------------------------
-- Substitution
------------------------------------------------------------

-- | See 'isvar'.
data SubstName a b where
  SubstName :: (a ~ b) => Name a -> SubstName a b

-- | The 'Subst' class governs capture-avoiding substitution.  To
--   derive this class, you only need to indicate where the variables
--   are in the data type, by overriding the method 'isvar'.
class (Rep1 (SubstD b) a) => Subst b a where

  -- | If the argument is a variable, return its name wrapped in the
  --   'SubstName' constructor.  Return 'Nothing' for non-variable
  --   arguments.  The default implementation always returns
  --   'Nothing'.
  isvar :: a -> Maybe (SubstName a b)
  isvar x = Nothing

  -- | @'subst' nm sub tm@ substitutes @sub@ for @nm@ in @tm@.
  subst :: Name b -> b -> a -> a
  subst n u x | isFree n =
     case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) -> if  m == n then u else x
        Nothing -> substR1 rep1 n u x
  subst m u x = error $ "Cannot substitute for bound variable " ++ show m

  -- | Perform several simultaneous substitutions.
  substs :: [(Name b, b)] -> a -> a
  substs ss x
    | all (isFree . fst) ss =
      case (isvar x :: Maybe (SubstName a b)) of
        Just (SubstName m) ->
          case List.find ((==m) . fst) ss of
            Just (_, u) -> u
            Nothing     -> x
        Nothing -> substsR1 rep1 ss x
    | otherwise =
      error $ "Cannot substitute for bound variable in: " ++ show (map fst ss)

-- | Reified class dictionary for 'Subst'.
data SubstD b a = SubstD {
  isvarD  :: a -> Maybe (SubstName a b),
  substD  ::  Name b -> b -> a -> a ,
  substsD :: [(Name b, b)] -> a -> a
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

substsR1 :: R1 (SubstD b) a -> [(Name b, b)] -> a -> a
substsR1 (Data1 dt cons) = \ s d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substsD w s) rec kids
      in (to c z)
substsR1 r               = \ s c -> c

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
instance (Alpha a, Subst c a) => Subst c (Rec a)

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