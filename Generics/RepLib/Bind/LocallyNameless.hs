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
             StandaloneDeriving
  #-}
{- LANGUAGE  KitchenSink -}

{- TODO:

X - Permutation type
X - Better type for freshen
Story about polarity
X - Easier instances for Patterns/Alphas
  - coalesced Pattern and Alpha type classes together
  - as there does not seem to be a good reason to distinguish them.
Extensive testing
X - Nominal version

-}

{- Tricky things about the design.

Equality for binders is defined in terms of aeq, *not* equality for
the subcomponents. If you want to use a specialized form of equality
for a particular type, (to ignore source locations for example) you
need to edit match to take that into accont. Merely creating a special
instance of Eq won't work!

Single/multiple substitutions are *not* defined in terms of
each other.

 -}

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
    Name, AnyName(..), Bind, Annot(..), Rebind,

    -- ** Utilities
    integer2Name, string2Name, makeName,
    name2Integer, name2String, anyName2Integer, anyName2String,
    name1,name2,name3,name4,name5,name6,name7,name8,name9,name10,

    -- * The 'Alpha' class
    Alpha(..),
    swaps, match,
    binders, patfv, fv,
    aeq,

    -- * Binding operations
    bind, unsafeUnBind,

    -- * The 'Fresh' class
    Fresh(..), freshen,
    unbind, unbind2, unbind3,

    -- * The 'LFresh' class
    HasNext(..), LFresh(..),
    lfreshen,
    lunbind, lunbind2, lunbind3,

    -- * Rebinding operations
    rebind, reopen,

    -- * Substitution
    Subst(..),

    -- * For abstract types
    abs_swaps,abs_fv,abs_freshen,abs_match,
    abs_nthpatrec,abs_findpatrec,abs_close,abs_open,

   -- * Advanced
   AlphaCtx, matchR1,

   -- * Pay no attention to the man behind the curtain
   -- $paynoattention
   rName, rBind, rRebind, rAnnot
) where

import Generics.RepLib
import Generics.RepLib.Bind.PermM

import qualified Data.List as List
import qualified Data.Char as Char
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as S
import qualified Text.Read as R
import Prelude hiding (or)
import Data.Monoid
import Control.Monad.Reader (Reader,ask,local,runReader)
import System.IO.Unsafe (unsafePerformIO)


------------------------------------------------------------
-- Basic types
------------------------------------------------------------

$(derive_abstract [''R])
-- The above only works with GHC 7.

instance Ord (R a) where
  compare r1 r2 = EQ  -- R a is a singleton

-- | 'Name's are things that get bound.  This type is intentionally
--   abstract; to create a 'Name' you can use 'string2Name' or
--   'integer2Name'. The type parameter is a tag, or /sort/, which tells
--   us what sorts of things this name may stand for. The sort must
--   be an instance of the 'Rep' type class.
data Name a
  = Nm (R a) (String, Integer)   -- free names
  | Bn (R a) Integer Integer     -- bound names / binding level + pattern index
   deriving (Eq, Ord)

-- | A name with a hidden (existentially quantified) sort.
data AnyName = forall a. Rep a => AnyName (Name a)



-- | The type of a binding.  We can 'Bind' an @a@ object in a @b@
--   object if we can create \"fresh\" @a@ objects, and @a@ objects
--   can occur unbound in @b@ objects. Often @a@ is 'Name' but that
--   need not be the case.
--
--   Like 'Name', 'Bind' is also abstract. You can create bindings
--   using 'bind' and take them apart with 'unbind' and friends.
data Bind a b = B a b

-- Set bindings.  TODO: implement.
data SBind a b = SB a b

-- | An annotation is a \"hole\" in a pattern where variables can be
--   used, but not bound. For example, patterns may include type
--   annotations, and those annotations can reference variables
--   without binding them.  Annotations do nothing special when they
--   appear elsewhere in terms.
newtype Annot a = Annot a deriving (Show, Read, Eq)

-- | 'Rebind' supports \"telescopes\" --- that is, patterns where
--   bound variables appear in multiple subterms.
data Rebind a b = R a b

$(derive [''Bind, ''Name, ''Annot, ''Rebind])

-- AnyName has an existential in it, so we cannot create a complete
-- representation for it, unfortunately.

$(derive_abstract [''AnyName])

instance Show AnyName where
  show (AnyName n1) = show n1

instance Eq AnyName where
   (AnyName n1) == (AnyName n2) =
      case gcastR (getR n1) (getR n2) n1 of
           Just n1' -> n1' == n2
           Nothing  -> False

instance Ord AnyName where
   compare (AnyName n1) (AnyName n2) =
       case compareR (getR n1) (getR n2) of
         EQ  -> case gcastR (getR n1) (getR n2) n1 of
           Just n1' -> compare n1' n2
           Nothing  -> error "Panic: equal types are not equal in Ord AnyName instance!"
         ord -> ord

------------------------------------------------------------
-- Utilities
------------------------------------------------------------

-- some convenient names for testing
name1, name2, name3, name4, name5, name6, name7, name8, name9, name10, name11
  :: Rep a => Name a
name1 = integer2Name 1
name2 = integer2Name 2
name3 = integer2Name 3
name4 = integer2Name 4
name5 = integer2Name 5
name6 = integer2Name 6
name7 = integer2Name 7
name8 = integer2Name 8
name9 = integer2Name 9
name10 = integer2Name 10
name11 = integer2Name 11

--instance Read Name where
--  read s = error "FIXME"

instance Show (Name a) where
  show (Nm _ ("",n)) = "_" ++ (show n)
  show (Nm _ (x,0))  = x
  show (Nm _ (x,n))  = x ++ (show n)
  show (Bn _ x y)    =  show x ++ "@" ++ show y

-- | Get the integer index of a 'Name'.
name2Integer :: Name a -> Integer
name2Integer (Nm _ (_,x)) = x
name2Integer (Bn _ _ _)   = error "Internal Error: cannot call name2Integer for bound names"

-- | Get the string part of a 'Name'.
name2String :: Name a -> String
name2String (Nm _ (s,_)) = s
name2String (Bn _ _ _)   = error "Internal Error: cannot call name2Integer for bound names"

-- | Get the integer index of an 'AnyName'.
anyName2Integer :: AnyName -> Integer
anyName2Integer (AnyName nm) = name2Integer nm

-- | Get the string part of an 'AnyName'.
anyName2String :: AnyName -> String
anyName2String (AnyName nm) = name2String nm

toSortedName :: Rep a => AnyName -> Maybe (Name a)
toSortedName (AnyName n) = gcastR (getR n) rep n

-- | Create a 'Name' from an 'Integer'.
integer2Name :: Rep a => Integer -> Name a
integer2Name n = makeName "" n

-- | Create a 'Name' from a 'String'.
string2Name :: Rep a => String -> Name a
string2Name s = makeName s 0

-- | Create a 'Name' from a @String@ and an @Integer@ index.
makeName :: Rep a => String -> Integer -> Name a
makeName s i = Nm rep (s,i)

-- | Determine the sort of a 'Name'.
getR :: Name a -> R a
getR (Nm r _)   = r
getR (Bn r _ _) = r

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

  -- BAY: A bunch of these 'see foo' notes refer to things which are
  -- not exported, should they be?

  -- | See 'swaps'.
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  swaps' = swapsR1 rep1

  -- | See 'fv'.
  fv' :: AlphaCtx -> a -> Set AnyName
  fv' = fvR1 rep1

  -- | See 'lfreshen'.
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  lfreshen' = lfreshenR1 rep1

  -- | See 'freshen'.
  freshen' :: Fresh m => AlphaCtx -> a -> m (a, Perm AnyName)
  freshen' = freshenR1 rep1

  -- | See 'match'.
  match'   :: AlphaCtx -> a -> a -> Maybe (Perm AnyName)
  match'   = matchR1 rep1

  -- | Replace free names by bound names.
  close :: Alpha b => AlphaCtx -> b -> a -> a
  close = closeR1 rep1

  -- | Replace bound names by free names.
  open :: Alpha b => AlphaCtx -> b -> a -> a
  open = openR1 rep1

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
--   standard mode is to use 'Term'; the function 'fv', 'swaps',
--   'lfreshen', 'freshen' and 'match' do this by default.
data Mode = Term | Pat deriving (Show, Eq, Read)

-- | Class constraint hackery to allow us to override the default
--   definitions for certain classes.  'AlphaD' is essentially a
--   reified dictionary for the 'Alpha' class.
data AlphaD a = AlphaD {
  swapsD    :: AlphaCtx -> Perm AnyName -> a -> a,
  fvD       :: AlphaCtx -> a -> Set AnyName,
  freshenD  :: forall m. Fresh m => AlphaCtx -> a -> m (a, Perm AnyName),
  lfreshenD :: forall b m. LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b,
  matchD    :: AlphaCtx -> a -> a -> Maybe (Perm AnyName),

  closeD    :: Alpha b => AlphaCtx -> b -> a -> a,
  openD     :: Alpha b => AlphaCtx -> b -> a -> a,
  findpatD  :: a -> AnyName -> (Integer, Bool),
  nthpatD   :: a -> Integer -> (Integer, Maybe AnyName)
  }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD swaps' fv' freshen' lfreshen' match'
           close open findpatrec nthpatrec

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


fvR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> Set AnyName
fvR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> fv1 rec p kids
fvR1 _ = \ _ _ -> S.empty

fv1 :: MTup (AlphaD) l -> AlphaCtx -> l -> Set AnyName
fv1 MNil _ Nil = S.empty
fv1 (r :+: rs) p (p1 :*: t1) =
   fvD r p p1 `S.union` fv1 rs p t1

-- Generic definition of freshen and match

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
  l2 <- match1 rs c t1 t2
  (l1 `join` l2)

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

------------------------------------------------------------
-- Specific Alpha instances
-----------------------------------------------------------

instance Rep a => Alpha (Name a) where
  fv' c n@(Nm _ _)  | mode c == Term = S.singleton (AnyName n)
  fv' c (Bn _ _ _)  | mode c == Term = S.empty
  fv' c n           | mode c == Pat  = S.empty

  swaps' c p x = case mode c of
                   Term ->
                     case apply p (AnyName x) of
                       AnyName y ->
                         case gcastR (getR y) (getR x) y of
                           Just y' -> y'
                           Nothing -> error "Internal error in swaps': sort mismatch"
                   Pat  -> x

  match' _ x  y   | x == y         = Just empty
  match' c n1 n2  | mode c == Term = Just $ single (AnyName n1) (AnyName n2)
  match' c _ _    | mode c == Pat  = Just empty

  freshen' c nm = case mode c of
     Term -> do x <- fresh nm
                return (x, single (AnyName nm) (AnyName x))
     Pat  -> return (nm, empty)

  --lfreshen' :: LFresh m => Pat a -> (a -> Perm Name -> m b) -> m b
  lfreshen' c nm f = case mode c of
     Term -> do x <- lfresh nm
                avoid [AnyName x] $ f x (single (AnyName nm) (AnyName x))
     Pat  -> f nm empty

  open c a (Bn r j x) | level c == j =
    case nthpat a x of
      AnyName nm -> case gcastR (getR nm) r nm of
        Just nm' -> nm'
        Nothing  -> error "Internal error in open: sort mismatch"
  open _ _ n = n

  close c a nm@(Nm r n) =
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

instance Alpha AnyName  where
  fv' c n@(AnyName (Nm _ _))  | mode c == Term = S.singleton n
  fv' c (AnyName (Bn _ _ _))  | mode c == Term = S.empty
  fv' c n                     | mode c == Pat  = S.empty

  swaps' c p x = case mode c of
                   Term -> apply p x
                   Pat  -> x

  match' _ x y | x == y          = Just empty
  match' c (AnyName n1) (AnyName n2)
    | mode c == Term =
      case gcastR (getR n1) (getR n2) n1 of
        Just n1' -> Just $ single (AnyName n1) (AnyName n2)
        Nothing  -> Nothing
  match' c _ _           | mode c == Pat   = Just empty

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

{-
instance (Alpha a, Alpha b) => Alpha (SBind a b) where
    open i a (SB x y)    = SB (open i a x)  (open (incr i) a y)
    close i a (SB x y)   = SB (close i a x) (close (incr i) a y)

    swaps' p pm (SB x y) =
        (SB (swaps' (pat p) pm x) (swaps' (incr p) pm y))

    fv' p (SB x y) = fv' (pat p) x ++ fv' p y

    freshen' p (SB x y) = do
      (x', pm1) <- freshen' (pat p) x
      (y', pm2) <- freshen' (incr p) (swaps' (incr p) pm1 y)
      return (SB x' y', pm1 <> pm2)

    lfreshen' p (SB x y) f =
      avoid (fv' p x) $
        lfreshen' (pat p) x (\ x' pm1 ->
        lfreshen' (incr p)   (swaps' (incr p) pm1 y) (\ y' pm2 ->
        f (SB x' y') (pm1 <> pm2)))

    -- determine a permutation of free variables
    -- such that p (SB x1 y1) `aeq` SB x2 y2
    -- this is fairly inefficient with the locally
    -- nameless representation (unless we can match bound names too)
    -- but to do that, we need to pass the binding level as
    -- an argument to match'
    match' p (SB x1 y1) (SB x2 y2) = do
      px <- match' (pat p) x1 x2
      py <- match' (incr p) (swaps' (incr p) px y1) (swaps' (incr p) px y2)
      return (px <> py)
-}

instance (Alpha a, Alpha b) => Alpha (Bind a b) where
    swaps' c pm (B x y) =
        (B (swaps' (pat c) pm x)
           (swaps' (incr c) pm y))

    fv' c (B x y) = fv' (pat c) x `S.union` fv' (incr c) y

    freshen' c (B x y) = do
      (x', pm1) <- freshen' (pat c) x
      (y', pm2) <- freshen' (incr c) (swaps' (incr c) pm1 y)
      return (B x' y', pm1 <> pm2)

    lfreshen' c (B x y) f =
--      avoid (S.elems $ fv' c x) $ -- I don't think we need this
        lfreshen' (pat c) x (\ x' pm1 ->
        lfreshen' (incr c) (swaps' (incr c) pm1 y) (\ y' pm2 ->
        f (B x' y') (pm1 <> pm2)))

    match' c (B x1 y1) (B x2 y2) = do
      px <- match' (pat c) x1 x2
      --- check this!
      py <- match' (incr c) y1 y2
      -- need to make sure that all permutations of
      -- bound variables at this
      -- level are the identity
      (px `join` py)

    open  c a (B x y)    = B (open (pat c) a x)  (open  (incr c) a y)
    close c a (B x y)    = B (close (pat c) a x) (close (incr c) a y)

instance (Alpha a, Alpha b) => Alpha (Rebind a b) where

  swaps' p pm (R x y) = R (swaps' p pm x) (swaps' (incr p) pm y)

  fv' p (R x y) =  fv' p x `S.union` fv' (incr p) y

  lfreshen' p (R x y) g =
    lfreshen' p x $ \ x' pm1 ->
      lfreshen' (incr p) (swaps' (incr p) pm1 y) $ \ y' pm2 ->
        g (R x' y') (pm1 <> pm2)

  freshen' p (R x y) = do
      (x', pm1) <- freshen' p x
      (y', pm2) <- freshen' (incr p) (swaps' (incr p) pm1 y)
      return (R x' y', pm1 <> pm2)

  match' p (R x1 y1) (R x2 y2) = do
     px <- match' p x1 x2
     py <- match' (incr p)  y1 y2
     (px `join` py)

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


instance Alpha a => Alpha (Annot a) where
   swaps' c pm (Annot t) | mode c == Pat  = Annot (swaps' (term c) pm t)
   swaps' c pm (Annot t) | mode c == Term = Annot t

   fv' c (Annot t) | mode c == Pat  = fv' (term c) t
   fv' c _         | mode c == Term = S.empty

   freshen' c (Annot t) | mode c == Pat = do
       (t', p) <- freshen' (term c) t
       return (Annot t', p)
   freshen' c a | mode c == Term = return (a, empty)

---   lfreshen' c (Annot t) | mode c == Pat


   match' c (Annot x) (Annot y) | mode c == Pat  = match' (term c) x y
   match' c (Annot x) (Annot y) | mode c == Term = if x `aeq` y
                                    then Just empty
                                    else Nothing
   findpatrec _ _ = (0, False)
   nthpatrec nm i = (i, Nothing)

-- Instances for other types use the default definitions.
instance Alpha Bool where
instance Alpha Float where
instance Alpha () where
instance Alpha a => Alpha [a] where
instance Alpha Int where
instance Alpha Integer where
instance Alpha Double where
instance Alpha Char where
instance Alpha a => Alpha (Maybe a) where
instance (Alpha a,Alpha b) => Alpha (Either a b) where
instance (Alpha a,Alpha b) => Alpha (a,b) where
instance (Alpha a,Alpha b,Alpha c) => Alpha (a,b,c) where
instance (Alpha a, Alpha b,Alpha c, Alpha d) => Alpha (a,b,c,d)
instance (Alpha a, Alpha b,Alpha c, Alpha d, Alpha e) =>
   Alpha (a,b,c,d,e)

instance (Rep a) => Alpha (R a) where
  swaps'      = abs_swaps
  fv'         = abs_fv
  freshen'    = abs_freshen
  match'      = abs_match
  nthpatrec  = abs_nthpatrec
  findpatrec = abs_findpatrec
  close      = abs_close
  open       = abs_open


-- Definitions of the class members for abstract types.
-- These will go away soon.
abs_swaps _ p s = s
abs_fv _ s = S.empty
abs_freshen _ b = return (b, empty)
abs_match _ x1 x2 = if x1 == x2 then Just empty else Nothing
abs_nthpatrec b i = (i, Nothing)
abs_findpatrec b n = (0, False)
abs_close i b x = x
abs_open i b x = x


----------------------------------------------------------
-- | A smart constructor for binders, also sometimes known as
-- \"close\".
bind ::(Alpha b, Alpha c) => b -> c -> Bind b c
bind b c = B b (close initial b c)

-- | A destructor for binders that does /not/ guarantee fresh
--   names for the binders.
unsafeUnBind :: (Alpha a, Alpha b) => Bind a b -> (a,b)
unsafeUnBind (B a b) = (a, open initial a b)

-- | The 'Eq' instance for 'Bind' compares bindings for
-- alpha-equality.
instance (Alpha a, Alpha b, Eq b) => Eq (Bind a b) where
   b1 == b2 = b1 `aeq` b2

-- fixme: in the 'otherwise' case the comparison is not alpha-respecting,
-- e.g.
--   compare (bind [name1] name1) (bind [name1,name1] name1) == LT
--   compare (bind [name3] name3) (bind [name1,name1] name1) == GT
instance (Alpha a, Alpha b, Ord a, Ord b) => Ord (Bind a b) where
   compare (B a1 b1) (B a2 b2) =
       case (match a1 a2) of
         Just p  -> case compare a1 (swaps p a2) of
                      EQ -> compare b1 b2
                      otherwise -> otherwise
         Nothing -> compare a1 a2

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


-- | Constructor for binding in patterns.
rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind a b = R a (close initial a b)

-- | Compare for alpha-equality.
instance (Alpha a, Alpha b, Eq b) => Eq (Rebind a b) where
   b1 == b2 = b1 `aeq` b2

instance (Show a, Show b) => Show (Rebind a b) where
  showsPrec p (R a b) = showParen (p>0)
      (showString "<<" . showsPrec p a . showString ">> " . showsPrec 0 b)

-- | destructor for binding patterns, the names should have already
-- been freshened.
reopen :: (Alpha a, Alpha b) => Rebind a b -> (a, b)
reopen (R a b) = (a, open initial a b)

-- | Determine alpha-equivalence.
aeq :: Alpha a => a -> a -> Bool
aeq t1 t2 = case match t1 t2 of
              Just p -> isid p
              _      -> False

-- | List all the binding variables (of a particular sort) in a pattern.
binders :: (Rep a, Alpha b) => b -> Set (Name a)
binders = fv

-- | List variables of a particular sort that occur freely in
--   annotations (not bindings).
patfv :: (Rep a, Alpha b) => b -> Set (Name a)
patfv = S.map fromJust . S.filter isJust . S.map toSortedName . fv' (pat initial)

-- | Calculate the free variables of a particular sort contained in a term.
fv :: (Rep b, Alpha a) => a -> Set (Name b)
fv = S.map fromJust . S.filter isJust . S.map toSortedName . fv' initial

-- | Apply a permutation to a term.
swaps :: Alpha a => Perm AnyName -> a -> a
swaps = swaps' initial

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

------------------------------------------------------------
-- Freshening
------------------------------------------------------------

-- | Type class for contexts which can generate new globally fresh
-- integers.
class HasNext m where
  -- | Get a new, globally fresh 'Integer'.
  nextInteger :: m Integer

  -- | Reset the internal state, i.e. forget about 'Integers' that
  -- have already been generated.
  resetNext   :: Integer -> m ()

-- | Type class for monads which can generate new globally unique
-- 'Name's based on a given 'Name'.
class Monad m => Fresh m where
  fresh :: Name a -> m (Name a)

-- | A monad @m@ supports the 'fresh' operation if it
-- can generate a new unique names.
instance (Monad m, HasNext m) => Fresh m where
  fresh (Nm r (s,j)) = do { n <- nextInteger; return (Nm r (s,n)) }
  fresh (Bn _ _ _)   = error "BUG: cannot freshen bound vars"


-- | Unbind (also known as \"open\") is the destructor for
-- bindings. It ensures that the names in the binding are fresh.
unbind  :: (Fresh m, Alpha b, Alpha c) => Bind b c -> m (b,c)
unbind (B b c) = do
      (b', _) <- freshen b
      return (b', open initial b' c)

-- | Unbind two terms with the same fresh names, provided the
-- binders match.
unbind2  :: (Fresh m, Alpha b, Alpha c, Alpha d) =>
            Bind b c -> Bind b d -> m (Maybe (b,c,d))
unbind2 (B b1 c) (B b2 d) = do
      case match b1 b2 of
         Just _ -> do
           (b', _) <- freshen b1
           return $ Just (b', open initial b' c, open initial b' d)
         Nothing -> return Nothing

unbind3  :: (Fresh m, Alpha b, Alpha c, Alpha d, Alpha e) =>
            Bind b c -> Bind b d -> Bind b e ->  m (Maybe (b,c,d,e))
unbind3 (B b1 c) (B b2 d) (B b3 e) = do
      case (match b1 b2, match b1 b3) of
         (Just _, Just _) -> do
           (b', _) <- freshen b1
           return $ Just (b', open initial b' c, open initial b' d, open initial b' e)
         _ -> return Nothing

---------------------------------------------------
-- LFresh

-- | This is the class of monads that support freshness in an
-- (implicit) local scope.  Generated names are fresh for the current
-- local scope, but not globally fresh.  This class has a basic
-- instance based on the reader monad.
class Monad m => LFresh m where
  -- | Pick a new name that is fresh for the current (implicit) scope.
  lfresh  :: Rep a => Name a -> m (Name a)
  -- | Avoid the given names when freshening in the subcomputation.
  avoid   :: [AnyName] -> m a -> m a

-- XXX TODO: move these instances somewhere else
-- | Simple reader monad instance for 'LFresh'.
instance LFresh (Reader Integer) where
  lfresh (Nm r (s,j)) = do { n <- ask; return (Nm r (s, max j (n+1))) }
  avoid []          = id
  avoid names       = local (max k)
    where k = maximum (map anyName2Integer names)

-- | A monad instance for 'LFresh' which renames to the lowest
--  number not currently being used
instance LFresh (Reader (Set AnyName)) where
  lfresh nm = do
    let s = name2String nm
    used <- ask
    return $ head (filter (\x -> not (S.member (AnyName x) used))
                          (map (makeName s) [0..]))
  avoid names = local (S.union (S.fromList names))


-- | Destruct a binding in an 'LFresh' monad.
lunbind :: (LFresh m, Alpha a, Alpha b) => Bind a b -> ((a, b) -> m c) -> m c
lunbind (B a b) g =
  -- avoid (S.elems $ fv b) $ -- don't think we need this
  lfreshen a (\x _ -> g (x, open initial x b))


-- | Unbind two terms with the same fresh names, provided the
--   binders match.
lunbind2  :: (LFresh m, Alpha b, Alpha c, Alpha d) =>
            Bind b c -> Bind b d -> (Maybe (b,c,d) -> m e) -> m e
lunbind2 (B b1 c) (B b2 d) g =
      case match b1 b2 of
         Just _ ->
           lunbind (B b1 c) $ \ (b', c') ->
             g $ Just (b', c', open initial b' d)  -- BAY: the c' used to be c,
         Nothing -> g Nothing                      -- am I correct in assuming
                                                   -- that was a bug?

-- | Unbind three terms with the same fresh names, provided the
--   binders match.
lunbind3  :: (LFresh m, Alpha b, Alpha c, Alpha d, Alpha e) =>
            Bind b c -> Bind b d -> Bind b e ->  (Maybe (b,c,d,e) -> m f) -> m f
lunbind3 (B b1 c) (B b2 d) (B b3 e) g = do
      case (match b1 b2, match b1 b3) of
         (Just _, Just _) ->
           lunbind (B b1 c) $ \ (b', c') ->
              g $ Just (b', c', open initial b' d, open initial b' e)
         _ -> g Nothing

------------------------------------------------------------
-- Substitution
------------------------------------------------------------

-- | The 'Subst' class governs capture-avoiding substitution.  To
--   derive this class, you only need to indicate where the variables
--   are in the data type, by overriding the method 'isvar'.
class (Rep1 (SubstD b) a) => Subst b a where

  -- | If the argument is a variable, return its name and a function
  --   to generate a substituted term.  Return 'Nothing' for
  --   non-variable arguments.
  isvar :: a -> Maybe (Name b, b -> a)
  isvar x = Nothing

  -- | @'subst' nm sub tm@ substitutes @sub@ for @nm@ in @tm@.
  subst :: Name b -> b -> a -> a
  subst n u x =
      case isvar x of
        Just (m, f) | m == n -> f u
        Just (_, _) -> x
        Nothing -> substR1 rep1 n u x

  -- | Perform several simultaneous substitutions.
  substs :: [Name b] -> [b] -> a -> a
  substs ns us x =
      case isvar x of
        Just (m, f) ->
          if length ns /= length us
            then error "BUG: Number of vars and terms must match in multisubstitution"
            else case m `List.elemIndex` ns of
               Just i  -> f (us !! i)
               Nothing -> x
        Nothing -> substsR1 rep1 ns us x

-- | Reified class dictionary for 'Subst'.
data SubstD b a = SubstD {
  isvarD  :: a -> Maybe (Name b, b -> a),
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


-------------------- TESTING CODE --------------------------------
data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp) deriving (Show)

$(derive [''Exp])

instance Alpha Exp
instance Subst Exp Exp where
   isvar (V n) = Just (n, id)
   isvar _     = Nothing

deriving instance Eq Exp
deriving instance Ord Exp

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

perm = single nameA nameB

tests_aeq = do
   assert "a1" $ (bind nameA nameA) /= (bind nameA nameB)
   assert "a2" $ (bind nameA nameA) == (bind nameA nameA)
   assert "a3" $ (bind nameA nameA) == (bind nameB nameB)
   assert "a4" $ (bind nameA nameB) /= (bind nameB nameA)
   assert "a5" $ (bind (nameA, Annot nameB) nameA) /=
                 (bind (nameA, Annot nameC) nameA)
   assert "a6" $ (bind (nameA, Annot nameB) nameA) ==
                 (bind (nameA, Annot nameB) nameA)
   assert "a7" $ (bind (nameA, Annot nameB) nameA) ==
                 (bind (nameB, Annot nameB) nameB)
   assert "a8" $ rebind nameA nameB /= rebind nameB nameB
   assert "a9" $ rebind nameA nameA /= rebind nameB nameB
   assert "a9" $ (bind (rebind nameA (Annot nameA)) nameA) ==
                 (bind (rebind nameB (Annot nameB)) nameB)
   assert "a10" $ bind (rebind (nameA, Annot nameA) ()) nameA ==
                  bind (rebind (nameB, Annot nameA) ()) nameB
   assert "a11" $ bind (rebind (nameA, Annot nameA) ()) nameA /=
                  bind (rebind (nameB, Annot nameB) ()) nameB
   assert "a12" $ bind (Annot nameA) () /= bind (Annot nameB) ()
   assert "a13" $ bind (Annot nameA) () == bind (Annot nameA) ()
   assert "a14" $ bind (rebind (Annot nameA) ()) () /=
                  bind (rebind (Annot nameB) ()) ()
   assert "a15" $ (rebind (nameA, Annot nameA) ()) /=
                  (rebind (name4, Annot nameC) ())
   assert "a16" $ bind (nameA, nameB) nameA /= bind (nameB, nameA) nameA
   assert "a17" $ bind (nameA, nameB) nameA /= bind (nameA, nameB) nameB
   assert "a18" $ (nameA, nameA) /= (nameA, nameB)
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
   assert "b1" $ big1 /= big2
   assert "b2" $ fv big1 == emptyNE
   assert "b3" $ big1 == subst name11 (V name11) big1

-- properties
-- if match t1 t2 = Some p then swaps p t1 = t2

-- $paynoattention
-- These type representation objects are exported so they can be
-- referenced by auto-generated code.  Please pretend they do not
-- exist.