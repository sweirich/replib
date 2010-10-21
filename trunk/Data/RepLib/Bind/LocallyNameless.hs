{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, TemplateHaskell, TypeOperators, ScopedTypeVariables, TypeSynonymInstances, RankNTypes, GADTs, EmptyDataDecls, StandaloneDeriving #-}

{- TODO:

X - Permutation type
X - Better type for freshen
Story about polarity
X - Easier instances for Patterns/Alphas
  - coalesced Pattern and Alpha type classes together
  - as there does not seem to be a good reason to distinguish them.
Extensive testing
X - Nominal version
Multiple name types -- see GenericBindLNa.hs

free vars returns a set instead of a list.


-}

{- Tricky things about the design.

Equality for binders is defined in terms of aeq, *not* equality for
the subcomponents. If you want to use a specialized form of equality
for a particular type, (to ignore source locations for example) you
need to edit match to take that into accont. Merely creating a special
instance of Eq won't work!

Single/multiple substitutions are *not* defined in terms of
eachother.

 -}


-- | Generic implementation of name binding functions, based on the library
-- RepLib, using a locally nameless representation
-- Datatypes with binding can be defined using the 'Name', 'Bind' types.
-- Expressive patterns for binding come from the 'Annot' and 'Rebind' types.
-- Important classes are:
--     'Alpha' -- the class of types and patterns that include binders, and
--     'Subst' -- for subtitution functions.
-- Name generation is controlled via the 'Fresh' and 'LFresh' monads.
module Data.RepLib.Bind.LocallyNameless
  ( -- * --
    Name, Bind, Annot(..), Rebind,
    -- * --
    integer2Name,string2Name,
    name1,name2,name3,name4,name5,name6,name7,name8,name9, name10,
    name2Int,  -- change to integer
    -- * -- Ignore all methods of this class
    Alpha(..),
    binders, patfv, fv, -- use these instead
    aeq,
    -- * --
    Fresh(..),
    -- * -- Bind operations
    bind,unbind,unbind2,unbind3,unsafeUnBind,
    -- * -- revise? eliminate?
    HasNext(..),LFresh(..),lunbind,lunbind2,lunbind3,
    -- * -- Rebind operations
    rebind,reopen,
    -- * -- Substitution
    Subst(..),
    -- * -- For abstract types
    abs_swaps',abs_fv',abs_freshen',abs_match',
    abs_nthpatrec,abs_findpatrec,abs_close,abs_open,
   -- * -- Advanced
   AlphaCtx,matchR1,
   -- * -- Please ignore
   rName,rBind,rRebind,rAnnot
) where

import Data.RepLib
import Data.RepLib.Bind.Perm

import qualified Data.List as List
import qualified Data.Char as Char
import qualified Text.Read as R
import Prelude hiding (or)
import Data.Monoid
import Control.Monad.Reader (Reader,ask,local,runReader)
import System.IO.Unsafe (unsafePerformIO)

---------------------------------------------------
-- | Names are things that get bound.
data Name = Nm (String, Integer)   -- free names
          | Bn Integer Integer     -- bound names / binding level + pattern index
   deriving (Eq, Ord)


-- | Type of a binding.  Morally, the type a should be a
-- 'Pattern' and the type b should be in the class 'AlphaTerm'.
-- We can Bind an "a" object in a "b" object if we
-- can create "fresh" a objects, and Names can be
-- unbound in "b" objects. Often "a" is Name
-- but that need not be the case.
data Bind a b = B a b

data SBind a b = SB a b

-- | An annotation is a 'hole' in a pattern where variables
-- can be used, but not bound. For example patterns may include
-- type annotations, and those annotations can reference variables
-- without binding them.
-- Annotations do nothing special when they appear elsewhere in terms
newtype Annot a = Annot a deriving (Show, Read, Eq)

-- | Rebinding is for telescopes --- i.e. to support patterns that
-- also bind variables that appear later
data Rebind a b = R a (Bind a b)

-- | Special type for "OR" patterns, those that match two different ways
-- yet bind the same variables
data Or a b = Or a b deriving (Show, Read, Eq)

-- fragily deriving the replib instances for Bind and Name
-- in the same file that they are defined in. This shouldn't
-- work but it does.
$(derive [''Bind, ''Name, ''Annot, ''Rebind, ''Or])

---------------------------------------------------------------
-- Constructors and destructors for builtin types
---------------------------------------------------------------

name1 :: Name
name1 = Nm ("",1)
name2 :: Name
name2 = Nm ("",2)
name3 :: Name
name3 = Nm ("",3)
name4 :: Name
name4 = Nm ("",4)
name5 :: Name
name5 = Nm ("",5)
name6 = Nm ("",6)
name7 = Nm ("",7)
name8 = Nm ("",8)
name9 = Nm ("",9)
name10 = Nm ("",10)
name11 = Nm ("",11)


--instance Read Name where
--  read s = error "FIXME"

instance Show Name  where
  show (Nm ("",n)) = "_" ++ (show n)
  show (Nm (x,0)) = x
  show (Nm (x,n)) = x ++ (show n)
  show (Bn x y) =  show x ++ "@" ++ show y

name2Int :: Name -> Integer
name2Int (Nm (_,x)) = x
name2Int (Bn _ _) = error "Internal Error: cannot call name2Int for bound names"

integer2Name :: Integer -> Name
integer2Name n = Nm ("",n)

string2Name :: String -> Name
string2Name s = Nm(s,0)

----------------------------------------------------------
-- | Smart constructor for binders
-- (aka close)
bind :: (Alpha b, Alpha c) => b -> c -> Bind b c
bind b c = B b (close initial b c)

-- | A destructor for binders that does not guarantee fresh
-- names for the binders.
unsafeUnBind :: (Alpha a, Alpha b) => Bind a b -> (a,b)
unsafeUnBind (B a b) = (a, open initial a b)

instance (Alpha a, Alpha b, Eq b) => Eq (Bind a b) where
   b1 == b2 = b1 `aeq` b2

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


-- | Constructor for binding in patterns
rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind a b = R a (bind a b)

instance (Alpha a, Alpha b, Eq b) => Eq (Rebind a b) where
   b1 == b2 = b1 `aeq` b2

instance (Show a, Show b) => Show (Rebind a b) where
  showsPrec p (R a (B _ b)) = showParen (p>0)
      (showString "<<" . showsPrec p a . showString ">> " . showsPrec 0 b)

-- | destructor for binding patterns, the names should have already
-- been freshened.
reopen :: (Alpha a, Alpha b) => Rebind a b -> (a, b)
reopen (R a (B _ b)) = (a, open initial a b)

-- | or patterns must bind exactly the same list of names
or :: (Alpha a, Alpha b) => a -> b -> Maybe (Or a b)
or a b = if fv a == fv b then Just (Or a b) else Nothing

unOr :: Or a b -> (a, b)
unOr (Or a b) = (a,b)

---------------------------------------------------------------
--- | Determine alpha-equivalence
aeq :: Alpha a => a -> a -> Bool
aeq t1 t2 = case match t1 t2 of
              Just p -> isid p
              _      -> False

-- | List the binding variables in a pattern
binders :: Alpha b => b -> [ Name ]
binders = fv

-- | List variables that occur freely in annotations (not binding)
patfv :: Alpha b => b -> [ Name ]
patfv = fv' (pat initial)

-- | calculate the free variables of the term
fv :: Alpha a => a -> [Name]
fv = fv' initial

-- | The method "swaps" applys a permutation
swaps :: Alpha a => Perm Name -> a -> a
swaps = swaps' initial

-- | "Locally" freshen an object
lfreshen :: Alpha a => LFresh m => a -> (a -> Perm Name -> m b) -> m b
lfreshen = lfreshen' initial

-- | An object of type "b" can be freshened if a new
-- copy of "b" can be produced where all old *binding* Names
-- in "b" are replaced with new fresh Names, and the
-- permutation reports which Names were swapped by others.
freshen :: (Fresh m, Alpha a) => a -> m (a, Perm Name)
freshen = freshen' initial

-- | Match compares two data structures and produces a permutation
-- of their Names that will make them alpha-equivalent to
-- eachother. (Names that appear in annotations must match exactly.)
-- Also note that two terms are alpha-equivalent when the empty
-- permutation is returned.
match   :: Alpha a => a -> a -> Maybe (Perm Name)
match   = match' initial


-- | lookup up the nth name in the pattern b
-- PRECONDITION: number of names in the pattern must be at least n
nthpat :: Alpha a => a -> Integer -> Name
nthpat x i = case nthpatrec x i of
                 (j, Nothing) -> error
                   ("BUG: pattern index " ++ show i ++ " out of bounds by " ++ show j ++ "in" ++ show x)
                 (_, Just n)  -> n

-- | find the (first) index of the name in the pattern
-- if it exists
findpat :: Alpha a => a -> Name -> Maybe Integer
findpat x n = case findpatrec x n of
                   (i, True) -> Just i
                   (_, False) -> Nothing


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

-- A mode is basically a flag that tells us whether we should be
-- looking at the names in the term, or if we are in a pattern and
-- should *only* be looking at the names in the annotations. The
-- standard mode is to use 'Term', the function 'fv', 'swaps',
-- 'lfreshen', 'freshen' and 'match' do this by default.
data Mode = Term | Pat deriving (Show, Eq, Read)

-- | The next class is for all terms that may contain binders The
-- 'Rep1' class constraint means that we can only make instances of
-- this class for types that have generic representations. (Derive
-- these using TH and RepLib.) Most of the time, the default (generic)
-- definitions of these methods will suffice. Furthermore, these methods
-- should not (and cannot) be called directly, as they maintain state
-- about the iteration.
class (Show a, Rep1 AlphaD a) => Alpha a where

  -- | See 'swaps'
  swaps' :: AlphaCtx -> Perm Name -> a -> a
  swaps' = swapsR1 rep1

  -- | See 'fv'
  fv' :: AlphaCtx -> a -> [Name]
  fv' = fvR1 rep1

  -- | See 'lfreshen'
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm Name -> m b) -> m b
  lfreshen' = lfreshenR1 rep1

  -- | See 'freshen'
  freshen' :: Fresh m => AlphaCtx -> a -> m (a, Perm Name)
  freshen' = freshenR1 rep1

  -- | See 'match'
  match'   :: AlphaCtx -> a -> a -> Maybe (Perm Name)
  match'   = matchR1 rep1

  -- | replace free Names by bound Names
  close :: (Alpha b) => AlphaCtx -> b -> a -> a
  close = closeR1 rep1

  -- | replace bound Names by free Names
  -- level, new Names,
  open :: Alpha b => AlphaCtx -> b -> a -> a
  open = openR1 rep1

  ---------------- PATTERN OPERATIONS ----------------------------

  -- | lookup the nth name in the pattern b, returning
  -- the number of names encoundered if not found
  nthpatrec :: a -> Integer -> (Integer, Maybe Name)
  nthpatrec = nthpatR1 rep1

  -- | find the (first) index of the name in the pattern if
  -- it exists, if not found (bool = false) return the number
  -- of names encountered
  findpatrec :: a -> Name -> (Integer, Bool)
  findpatrec = findpatR1 rep1


-- class constraint hackery to allow us to override the
-- default definitions for certain classes
data AlphaD a = AlphaD {
  swapsD    :: AlphaCtx -> Perm Name -> a -> a,
  fvD       :: AlphaCtx -> a -> [Name],
  freshenD  :: forall m. Fresh m => AlphaCtx -> a -> m (a, Perm Name),
  lfreshenD :: forall b m. LFresh m => AlphaCtx -> a -> (a -> Perm Name -> m b) -> m b,
  matchD    :: AlphaCtx -> a -> a -> Maybe (Perm Name),

  closeD    :: Alpha b => AlphaCtx -> b -> a -> a,
  openD     :: Alpha b => AlphaCtx -> b -> a -> a,
  findpatD  :: a -> Name -> (Integer, Bool),
  nthpatD   :: a -> Integer -> (Integer, Maybe Name)


 }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD swaps' fv' freshen' lfreshen' match'
           close open findpatrec nthpatrec


-- Generic definitions of the functions in the swap
-- class. (All functions that take representations end
-- in 'R1')

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


swapsR1 :: R1 AlphaD a -> AlphaCtx -> Perm Name -> a -> a
swapsR1 (Data1 _ cons)  = \ p x d ->
  case (findCon cons d) of
    Val c rec kids -> to c (map_l (\z -> swapsD z p x) rec kids)
swapsR1 _               = \ _ _ d -> d


fvR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> [Name]
fvR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> List.nub (fv1 rec p kids)
fvR1 _ = \ _ _ -> []

fv1 :: MTup (AlphaD) l -> AlphaCtx -> l -> [Name]
fv1 MNil _ Nil = []
fv1 (r :+: rs) p (p1 :*: t1) =
   fvD r p p1 ++ fv1 rs p t1

-- Generic definition of freshen and match

matchR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> a -> Maybe (Perm Name)
matchR1 (Data1 _ cons) = loop cons where
  loop (Con emb reps : rest) p x y =
    case (from emb x, from emb y) of
      (Just p1, Just p2) -> match1 reps p p1 p2
      (Nothing, Nothing) -> loop rest p x y
      (_,_)              -> Nothing
  loop [] _ _ _ = error "Impossible"
matchR1 Int1 = \ _ x y -> if x == y then Just mempty else Nothing
matchR1 Integer1 = \ _ x y -> if x == y then Just mempty else Nothing
matchR1 Char1 = \ _ x y -> if x == y then Just mempty else Nothing
matchR1 _ = \ _ _ _ -> Nothing

match1 :: MTup (AlphaD) l -> AlphaCtx -> l -> l -> Maybe (Perm Name)
match1 MNil _ Nil Nil = Just mempty
match1 (r :+: rs) c (p1 :*: t1) (p2 :*: t2) = do
  l1 <- matchD r c p1 p2
  l2 <- match1 rs c t1
                    (map_l (\z -> swapsD z c l1) rs t2)
  return (l1 <> l2)

freshenR1 :: Fresh m => R1 (AlphaD) a -> AlphaCtx -> a -> m (a,Perm Name)
freshenR1 (Data1 _ cons) = \ p d ->
   case findCon cons d of
     Val c rec kids -> do
       (l, p') <- freshenL rec p kids
       return (to c l, p')
freshenR1 _ = \ _ n -> return (n, mempty)

freshenL :: Fresh m => MTup (AlphaD) l -> AlphaCtx -> l -> m (l, Perm Name)
freshenL MNil _ Nil = return (Nil, mempty)
freshenL (r :+: rs) p (t :*: ts) = do
  (xs, p2) <- freshenL rs p ts
  (x, p1) <- freshenD r p (swapsD r p p2 t)
  return ( x :*: xs, p1 <> p2)

lfreshenR1 :: LFresh m => R1 AlphaD a -> AlphaCtx -> a ->
              (a -> Perm Name -> m b) -> m b
lfreshenR1 (Data1 _ cons) = \p d f ->
   case findCon cons d of
     Val c rec kids -> lfreshenL rec p kids (\ l p' -> f (to c l) p')
lfreshenR1 _ = \ _ n f -> f n mempty

lfreshenL :: LFresh m => MTup (AlphaD) l -> AlphaCtx -> l ->
              (l -> Perm Name -> m b) -> m b
lfreshenL MNil _ Nil f = f Nil mempty
lfreshenL (r :+: rs) p (t :*: ts) f =
  lfreshenL rs p ts ( \ y p2 ->
  lfreshenD r p (swapsD r p p2 t) ( \ x p1 ->
     f (x :*: y) (p1 <> p2)))


-- returns either (# of names in b, false) or (index, true)
findpatR1 :: R1 AlphaD b -> b -> Name -> (Integer, Bool)
findpatR1 (Data1 dt cons) = \ d n ->
   case findCon cons d of
     Val c rec kids -> findpatL rec kids n
findpatR1 _ = \ x n -> (0, False)

findpatL :: MTup AlphaD l -> l -> Name -> (Integer, Bool)
findpatL MNil Nil n = (0, False)
findpatL (r :+: rs) (t :*: ts) n =
  case findpatD r t n of
    s@(i, True) -> s
    (i, False) -> case findpatL rs ts n of
                    (j, b) -> (i+j, b)

nthpatR1 :: R1 AlphaD b -> b -> Integer -> (Integer, Maybe Name)
nthpatR1 (Data1 dt cons) = \ d n ->
   case findCon cons d of
     Val c rec kids -> nthpatL rec kids n
nthpatR1 _ = \ x n -> (n, Nothing)

nthpatL :: MTup AlphaD l -> l -> Integer -> (Integer, Maybe Name)
nthpatL MNil Nil i = (i, Nothing)
nthpatL (r :+: rs) (t :*: ts) i =
  case nthpatD r t i of
    s@(_, Just n) -> s
    (j, Nothing) -> nthpatL rs ts j

---------------- Specific instances ----------------------------

instance Alpha Name  where
  fv' c (Nm n)   | mode c == Term = [ Nm n ]
  fv' c (Bn _ _) | mode c == Term = []
  fv' c n        | mode c == Pat  = []

  swaps' c p x = case mode c of
                   Term -> apply p x
                   Pat  -> x

  match' _ x y           | x == y          = Just mempty
  match' c (Nm x) (Nm y) | mode c == Term  = Just $ single (Nm x) (Nm y)
  match' c (Bn x1 y1) (Bn x2 y2) |
   mode c == Term && x1 == x2 = Just $ single (Bn x1 y1) (Bn x2 y2)
  match' c _ _           | mode c == Pat   = Just mempty
  match' _ _ _                             = Nothing

  freshen' c nm = case mode c of
     Term -> do { x <- fresh nm; return(x, single nm x) }
     Pat  -> return (nm, mempty)

  --lfreshen' :: LFresh m => Pat a -> (a -> Perm Name -> m b) -> m b
  lfreshen' c nm f = case mode c of
     Term -> do { x <- lfresh nm; avoid [x] $ f x (single nm x) }
     Pat  -> f nm mempty

  open c a (Bn j x) | level c == j = nthpat a x
  open _ _ n = n

  close c a (Nm n) = case findpat a (Nm n) of
                        Just x -> Bn (level c) x
                        Nothing -> Nm n
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
        (B (swaps' (pat c) pm x) (swaps' (incr c) pm y))

    fv' c (B x y) = fv' (pat c) x ++ fv' (incr c) y

    freshen' c (B x y) = do
      (x', pm1) <- freshen' (pat c) x
      (y', pm2) <- freshen' (incr c) (swaps' (incr c) pm1 y)
      return (B x' y', pm1 <> pm2)

    lfreshen' c (B x y) f =
      avoid (fv' c x) $
        lfreshen' (pat c) x (\ x' pm1 ->
        lfreshen' (incr c) (swaps' (incr c) pm1 y) (\ y' pm2 ->
        f (B x' y') (pm1 <> pm2)))

    match' c (B x1 y1) (B x2 y2) = do
      px <- match' (pat c) x1 x2
      --- check this!
      py <- match' (incr c) y1
                            (swaps' (incr c) px y2)
      -- need to make sure that all permutations of bound variables at this
      -- level are the identity
      return (px <> py)

    open  c a (B x y)    = B (open c a x)  (open  (incr c) a y)
    close c a (B x y)    = B (close c a x) (close (incr c) a y)



instance (Alpha a, Alpha b) => Alpha (Rebind a b) where
--  swaps' p pm (R x bnd) = R (swaps' pm x) (swaps' pm bnd)
  fv' p (R x (B x' y)) =  fv' p x ++ fv' p y

  freshen' p (R x (B x1 y)) = do
      (x', pm1) <- freshen' p x
      (y', pm2) <- freshen' (incr p) (swaps' (incr p) pm1 y)
      return (R x (B x1 y'), pm1 <> pm2)

  match' p (R x1 (B x1' y1)) (R x2 (B x2' y2)) = do
     px <- match' p x1 x2
     --- check!!
     py <- match' (incr p)  y1
                           (swaps' (incr p) px y2)
     return (px <> py)

  findpatrec (R x (B x' y)) nm =
     case findpatrec x nm of
         (i, True) -> (i, True)
         (i, False) -> case findpatrec y nm of
                         (j, True) -> (i + j, True)
                         (j, False) -> (i+j, False)

  nthpatrec (R x (B x' y)) i =
      case nthpatrec x i of
        (j , Just n) -> (j, Just n)
        (j , Nothing) -> nthpatrec y j


instance Alpha a => Alpha (Annot a) where
   swaps' c pm (Annot t) | mode c == Pat  = Annot (swaps' (term c) pm t)
   swaps' c pm (Annot t) | mode c == Term = Annot t

   fv' c (Annot t) | mode c == Pat  = fv' (term c) t
   fv' c _         | mode c == Term = []

   freshen' c (Annot t) | mode c == Pat = do
       (t', p) <- freshen' (term c) t
       return (Annot t', p)
   freshen' c a | mode c == Term = return (a, mempty)

---   lfreshen' c (Annot t) | mode c == Pat


   match' c (Annot x) (Annot y) | mode c == Pat  = match' (term c) x y
   match' c (Annot x) (Annot y) | mode c == Term = if x `aeq` y
                                    then Just mempty
                                    else Nothing
   findpatrec _ _ = (0, False)
   nthpatrec nm i = (i, Nothing)


instance (Alpha a, Alpha b) => Alpha (Or a b) where
   freshen' p (Or a b) = do
    (a', pm) <- freshen' p a
    let b' = swaps' p pm b
    return (Or a' b', pm)

   match' p (Or a1 b1) (Or a2 b2) = do
    p1 <- match' p a1 a2
    p2 <- match' p b1 b2
    if p1 == p2 then Just p1 else Nothing

   fv' c (Or a b) | mode c == Term = fv' (term c) a
   fv' c (Or a b) | mode c == Pat  = fv' (term c) a ++ fv' (pat c) b

   findpatrec (Or a b) nm = findpatrec a nm
   nthpatrec (Or a b) i   = nthpatrec a i

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

-- Definitions of the class members for abstract types.
abs_swaps' :: Alpha a => AlphaCtx -> Perm Name -> a -> a
abs_swaps' _ p s = s
abs_fv' :: Alpha a => AlphaCtx -> a -> [Name]
abs_fv' _ s = []
abs_freshen' :: (Fresh m, Alpha a) => AlphaCtx -> a -> m (a, Perm Name)
abs_freshen' _ b = return (b, mempty)
abs_match' :: (Eq a, Alpha a) => AlphaCtx -> a -> a -> Maybe (Perm Name)
abs_match' _ x1 x2 = if x1 == x2 then Just mempty else Nothing
abs_nthpatrec :: Alpha a => a -> Integer -> (Integer, Maybe Name)
abs_nthpatrec b i = (i, Nothing)
abs_findpatrec :: Alpha a => a -> Name -> (Integer, Bool)
abs_findpatrec b n = (0, False)
abs_close :: (Alpha a, Alpha b) => AlphaCtx -> b -> a -> a
abs_close i b x = x
abs_open :: (Alpha a, Alpha b) => AlphaCtx -> b -> a -> a
abs_open i b x = x


-------------------------------------------------------
-- | Select a new name, fresh for the given set, based on the
--  given name. Preference is to return the same name if it
--  is not already in the set.
{-
freshFor :: Name -> [Name] -> Name
freshFor n@(Nm (s,j)) ns | not (n `List.in` ns) -> n
                         | otherwise -> error "UNIMP"

-}



-------------------------------------------------------
-- | Global freshness monad
-- A monad "m" supports the nextInteger operation if it
-- can generate new integers that are fresh for a global scope.

-- XXX remove Monad constraint
class Monad m => HasNext m where
  nextInteger :: m Integer  -- reads integer and increments it
  resetNext   :: Integer -> m ()

-- XXX remove Monad constraint
class Monad m => Fresh m where
  fresh  :: Name -> m Name

-- | A monad "m" supports the "fresh" operation if it
-- can generate a new unique names.
instance HasNext m => Fresh m where
  fresh (Nm (s,j)) = do { n <- nextInteger; return (Nm (s,n)) }
  fresh (Bn _ _) = error "BUG: cannot freshen bound vars"


-- | Unbind is the destructor of a binding. It ensures that
-- the names in the binding b are fresh.
-- aka open
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
-- | Locally fresh monad
-- This is the class of
-- monads that support freshness in an (implicit) local scope.  Names
-- drawn are fresh for this particular scope, but not globally fresh.
-- This class has a basic instance based on the reader monad.
         -- XXX remove Monad constraint
class Monad m => LFresh m where
  -- | pick a new name that is fresh for the current (implicit) scope.
  lfresh  :: Name -> m Name
  -- | avoid these names when freshening in the subcomputation.
  avoid   :: [Name] -> m a -> m a




-- | Reader monad instance for local freshness class.
instance LFresh (Reader Integer) where
  lfresh (Nm (s,j)) = do { n <- ask; return (Nm (s, max j (n+1))) }
  avoid []          = id
  avoid names       = local (max k) where
        k = maximum (map name2Int names)

-- | Destruct a binding in the LFresh monad.
lunbind :: (LFresh m, Alpha a, Alpha b) => Bind a b -> m (a, b)
lunbind (B a b) =
  avoid (fv b) $
  lfreshen a (\x _ -> return (x, open initial x b))

lunbind2  :: (LFresh m, Alpha b, Alpha c, Alpha d) =>
            Bind b c -> Bind b d -> m (Maybe (b,c,d))
lunbind2 (B b1 c) (B b2 d) = do
      case match b1 b2 of
         Just _ -> do
           (b', c') <- lunbind (B b1 c)
           return $ Just (b', c, open initial b' d)
         Nothing -> return Nothing

lunbind3  :: (LFresh m, Alpha b, Alpha c, Alpha d, Alpha e) =>
            Bind b c -> Bind b d -> Bind b e ->  m (Maybe (b,c,d,e))
lunbind3 (B b1 c) (B b2 d) (B b3 e) = do
      case (match b1 b2, match b1 b3) of
         (Just _, Just _) -> do
           (b', c') <- lunbind (B b1 c)
           return $ Just (b', c', open initial b' d, open initial b' e)
         _ -> return Nothing

---------------------------------------------------------------
{-
instance Subst Ty   Term where
   -- no variable cases for ty in term
instance Subst Term Term where
   isvar (Var x) = Just (x, id)
   isvar _       = Nothing
-}

-- | Capture-avoiding substitution
-- To derive this class, you only need to indicate where the variables
-- are in the datatype a , by overriding the method 'isvar'
class (Rep1 (SubstD b) a) => Subst b a where
  isvar :: a -> Maybe (Name, b -> a)
  isvar x = Nothing

  subst :: Name -> b -> a -> a
  subst n u x =
      case isvar x of
        Just (m, f) | m == n -> f u
        Just (_, _) -> x
        Nothing -> substR1 rep1 n u x


  substs :: [Name] -> [b] -> a -> a
  substs ns us x =
      case isvar x of
        Just (m, f) ->
          if length ns /= length us
            then error "BUG: Number of vars and terms must match in multisubstitution"
            else case m `List.elemIndex` ns of
               Just i  -> f (us !! i)
               Nothing -> x
        Nothing -> substsR1 rep1 ns us x

data SubstD b a = SubstD {
  substD ::  Name -> b -> a -> a ,
  substsD :: [Name] -> [b] -> a -> a
}
instance Subst b a => Sat (SubstD b a) where
  dict = SubstD subst substs

substDefault :: Rep1 (SubstD b) a => Name -> b -> a -> a
substDefault = substR1 rep1

substR1 :: R1 (SubstD b) a -> Name -> b -> a -> a
substR1 (Data1 dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substD w x y) rec kids
      in (to c z)
substR1 r               = \ x y c -> c

substsR1 :: R1 (SubstD b) a -> [Name] -> [b] -> a -> a
substsR1 (Data1 dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = map_l (\ w -> substsD w x y) rec kids
      in (to c z)
substsR1 r               = \ x y c -> c

instance Subst b Int where
instance Subst b Bool where
instance Subst b () where
instance Subst b Char where
instance Subst b Integer where
instance Subst b Float where
instance Subst b Double where

instance Subst b Name where

instance (Subst c a, Subst c b) => Subst c (a,b) where
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d) where
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e) where
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) =>
   Subst c (a,b,d,e,f) where
instance (Subst c a) => Subst c [a] where
instance (Subst c a) => Subst c (Maybe a) where
instance (Subst c a, Subst c b) => Subst c (Either a b) where

instance (Subst c b, Subst c a, Alpha a,Alpha b) =>
    Subst c (Bind a b) where
instance (Subst c b, Subst c a, Alpha a, Alpha b) =>
    Subst c (Rebind a b) where

instance (Subst c a) => Subst c (Annot a) where
instance (Subst c a, Subst c b) => Subst c (Or a b) where



-------------------- TESTING CODE --------------------------------
data Exp = V Name
         | A Exp Exp
         | L (Bind Name Exp) deriving (Show)

$(derive [''Exp])

instance Alpha Exp where
instance Subst Exp Exp where
   isvar (V n) =  Just (n, id)
   isvar _     = Nothing

deriving instance Eq Exp
deriving instance Ord Exp


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

perm = single name1 name2

tests_aeq = do
   assert "a1" $ (bind name1 name1) /= (bind name1 name2)
   assert "a2" $ (bind name1 name1) == (bind name1 name1)
   assert "a3" $ (bind name1 name1) == (bind name2 name2)
   assert "a4" $ (bind name1 name2) /= (bind name2 name1)
   assert "a5" $ (bind (name1, Annot name2) name1) /=
                 (bind (name1, Annot name3) name1)
   assert "a6" $ (bind (name1, Annot name2) name1) ==
                 (bind (name1, Annot name2) name1)
   assert "a7" $ (bind (name1, Annot name2) name1) ==
                 (bind (name2, Annot name2) name2)
   assert "a8" $ rebind name1 name2 /= rebind name2 name2
   assert "a9" $ rebind name1 name1 /= rebind name2 name2
   assert "a9" $ (bind (rebind name1 (Annot name1)) name1) ==
                 (bind (rebind name2 (Annot name2)) name2)
   assert "a10" $ bind (rebind (name1, Annot name1) ()) name1 ==
                  bind (rebind (name2, Annot name1) ()) name2
   assert "a11" $ bind (rebind (name1, Annot name1) ()) name1 /=
                  bind (rebind (name2, Annot name2) ()) name2
   assert "a12" $ bind (Annot name1) () /= bind (Annot name2) ()
   assert "a13" $ bind (Annot name1) () == bind (Annot name1) ()
   assert "a14" $ bind (rebind (Annot name1) ()) () /=
                  bind (rebind (Annot name2) ()) ()
   assert "a15" $ (rebind (name1, Annot name1) ()) /=
                  (rebind (name4, Annot name3) ())
   assert "a16" $ bind (name1, name2) name1 /= bind (name2, name1) name1
   assert "a17" $ bind (name1, name2) name1 /= bind (name1, name2) name2
   assert "a18" $ (name1, name1) /= (name1, name2)

tests_fv = do
   assert "f1" $ fv (bind name1 name1) == []
   assert "f2" $ fv' (pat initial) (bind name1 name1) == []
   assert "f4" $ fv (bind name1 name2) == [name2]
   assert "f5" $ fv (bind (name1, Annot name2) name1) == [name2]
   assert "f7" $ fv (bind (name2, Annot name2) name2) == [name2]
   assert "f8" $ fv (rebind name1 name2) == [name1, name2]
   assert "f9" $ fv' (pat initial) (rebind name1 name1) == []
   assert "f3" $ fv (bind (rebind name1 (Annot name1)) name1) == []
   assert "f10" $ fv (rebind (name1, Annot name1) ()) == [name1]
   assert "f11" $ fv' (pat initial) (rebind (name1, Annot name1) ()) == [name1]
   assert "f12" $ fv (bind (Annot name1) ()) == [name1]
   assert "f14" $ fv (rebind (Annot name1) ()) == []

mkbig :: [Name] -> Exp -> Exp
mkbig (n : names) body =
    L (bind n (mkbig names (A (V n) body)))
mkbig [] body = body

big1 = mkbig (map integer2Name (take 100 [1 ..])) (V name11)
big2 = mkbig (map integer2Name (take 101 [1 ..])) (V name11)


tests_nth = do
  assert "n1" $ nthpat ([name1],name2) 0 == name1
  assert "n2" $ nthpat ([name1],name2) 1 == name2
  assert "n3" $ nthpat (name1, name2) 0 == name1
  assert "p1" $ findpat ([name1],name2) name1 == Just 0
  assert "p2" $ findpat ([name1],name2) name2 == Just 1
  assert "p3" $ findpat ([name1],name2) name3 == Nothing

tests_big = do
   assert "b1" $ big1 /= big2
   assert "b2" $ fv big1 == []
   assert "b3" $ big1 == subst name11 (V name11) big1



-- properties
-- if match t1 t2 = Some p then swaps p t1 = t2

