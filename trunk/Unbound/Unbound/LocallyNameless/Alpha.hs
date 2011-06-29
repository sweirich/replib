{-# LANGUAGE RankNTypes
           , FlexibleContexts
           , GADTs
           , TypeFamilies
  #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless.Alpha
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Portability :  GHC only (-XKitchenSink)
--
----------------------------------------------------------------------

module Unbound.LocallyNameless.Alpha where

import Generics.RepLib hiding (GT)
import Unbound.PermM
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Fresh
import Unbound.Util

import Data.List (intersect)
import Data.Maybe (isJust)

import Data.Monoid

------------------------------------------------------------
-- Overview
--
-- We have two classes of types:
--    Terms (which contain variables) and
--    Patterns (which contain binders)
--
-- Terms include
--    Names
--    Bind p t when p is a Pattern and t is a Term
--    Standard type constructors (Unit, (,), Maybe, [], etc)
--
-- Patterns include
--    Names
--    Embed t when t is a Term
--    Rebind p q when p and q are both Patterns
--    Rec p when p is a pattern
--    Shift a when a is an Embed or some number of Shifts wrapped around Embed
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
-- The Alpha class
------------------------------------------------------------

-- | The @Alpha@ type class is for types which may contain names.  The
--   'Rep1' constraint means that we can only make instances of this
--   class for types that have generic representations (which can be
--   automatically derived by RepLib.)
--
--   Note that the methods of @Alpha@ should almost never be called
--   directly.  Instead, use other methods provided by this module
--   which are defined in terms of @Alpha@ methods.
--
--   Most of the time, the default definitions of these methods will
--   suffice, so you can make an instance for your data type by simply
--   declaring
--
--   > instance Alpha MyType
--
--   Occasionally, however, it may be useful to override the default
--   implementations of one or more @Alpha@ methods for a particular
--   type.  For example, consider a type like
--
--   > data Term = ...
--   >           | Annotation Stuff Term
--
--   where the @Annotation@ constructor of @Term@ associates some sort
--   of annotation with a term --- say, information obtained from a
--   parser about where in an input file the term came from.  This
--   information is needed to produce good error messages, but should
--   not be taken into consideration when, say, comparing two @Term@s
--   for alpha-equivalence.  In order to make 'aeq' ignore
--   annotations, you can override the implementation of @aeq'@ like
--   so:
--
--   > instance Alpha Term where
--   >   aeq' c (Annotation _ t1) t2 = aeq' c t1 t2
--   >   aeq' c t1 (Annotation _ t2) = aeq' c t1 t2
--   >   aeq' c t1 t2 = aeqR1 rep1 t1 t2
--
--   Note how the call to 'aeqR1' handles all the other cases generically.
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

  -- | See 'acompare'.
  acompare' :: AlphaCtx -> a -> a -> Ordering
  acompare' = acompareR1 rep1

{-
  -- | See 'match'.
  match'   :: AlphaCtx -> a -> a -> Maybe (Perm AnyName)
  match'   = matchR1 rep1
-}

  -- | Replace free names by bound names.
  close :: Alpha b => AlphaCtx -> b -> a -> a
  close = closeR1 rep1

  -- | Replace bound names by free names.
  open :: Alpha b => AlphaCtx -> b -> a -> a
  open = openR1 rep1

  -- | @isPat x@ dynamically checks whether @x@ can be used as a valid
  --   pattern.  The default instance returns @Just@ if at all
  --   possible.  If successful, returns a list of names bound by the
  --   pattern.
  isPat :: a -> Maybe [AnyName]
  isPat = isPatR1 rep1

  -- | @isTerm x@ dynamically checks whether @x@ can be used as a
  --   valid term. The default instance returns @True@ if at all
  --   possible.
  isTerm :: a -> Bool
  isTerm = isTermR1 rep1

  -- | @isEmbed@ is needed internally for the implementation of
  --   @isPat@.  @isEmbed@ is true for terms wrapped in @Embed@ and zero
  --   or more occurrences of @Shift@.  The default implementation
  --   simply returns @False@.
  isEmbed :: a -> Bool
  isEmbed _ = False
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

-- | Type class for embedded terms (either @Embed@ or @Shift@).
class IsEmbed e where
  type Embedded e :: *

  -- | Construct an embedded term, which is an instance of 'Embed'
  --   with any number of enclosing 'Shift's.  That is, @embed@ can have
  --   any of the types
  --
  -- * @t -> Embed t@
  --
  -- * @t -> Shift (Embed t)@
  --
  -- * @t -> Shift (Shift (Embed t))@
  --
  -- and so on.
  embed   :: Embedded e -> e

  -- | Destruct an embedded term.  @unembed@ can have any of the types
  --
  -- * @Embed t -> t@
  --
  -- * @Shift (Embed t) -> t@
  --
  -- and so on.
  unembed :: e -> Embedded e

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

-- | Find the (first) index of the name in the pattern, if it exists.
findpat :: Alpha a => a -> AnyName -> Maybe Integer
findpat x n = case findpatrec x n of
                   Index i     -> Just i
                   NamesSeen _ -> Nothing


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

-- | @'nthpat' b n@ looks up up the @n@th name in the pattern @b@
-- (zero-indexed).  PRECONDITION: the number of names in the pattern
-- must be at least @n@.
nthpat :: Alpha a => a -> Integer -> AnyName
nthpat x i = case runNthCont (nthpatrec x) i of
                 CurIndex j -> error
                   ("BUG: pattern index " ++ show i ++
                    " out of bounds by " ++ show j ++ "in" ++ show x)
                 Found nm   -> nm

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
  isPatD    :: a -> Maybe [AnyName],
  isTermD   :: a -> Bool,
  isEmbedD  :: a -> Bool,
  swapsD    :: AlphaCtx -> Perm AnyName -> a -> a,
  fvD       :: Collection f => AlphaCtx -> a -> f AnyName,
  freshenD  :: Fresh m => AlphaCtx -> a -> m (a, Perm AnyName),
  lfreshenD :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b,
  aeqD      :: AlphaCtx -> a -> a -> Bool,
  -- matchD    :: AlphaCtx -> a -> a -> Maybe (Perm AnyName),
  closeD    :: Alpha b => AlphaCtx -> b -> a -> a,
  openD     :: Alpha b => AlphaCtx -> b -> a -> a,
  findpatD  :: a -> AnyName -> FindResult,
  nthpatD   :: a -> NthCont,
  acompareD :: AlphaCtx -> a -> a -> Ordering
  }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD isPat isTerm isEmbed swaps' fv' freshen' lfreshen' aeq' -- match'
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

{-
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
-}

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

combine :: Maybe [AnyName] -> Maybe [AnyName] -> Maybe [AnyName]
combine (Just ns1) (Just ns2) | ns1 `intersect` ns2 == [] =
                                  Just (ns1 ++ ns2)
combine _ _ = Nothing

isPatR1 :: R1 AlphaD b -> b -> Maybe [AnyName]
isPatR1 (Data1 dt cons) = \ d ->
   case findCon cons d of
     Val c rec kids ->
       foldl_l (\ c b a -> combine (isPatD c a) b) (Just []) rec kids
isPatR1 _ = \ d -> Just []

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
--      Name, Bind, Embed, Rebind, Rec, Shift
-----------------------------------------------------------

-- In the Name instance, if the mode is Term then the operation
-- observes the name. In Pat mode the name is a binder, so the name is
-- usually ignored.
instance Rep a => Alpha (Name a) where

  -- Both bound and free names are valid terms.
  isTerm _ = True

  -- Only free names are valid as patterns, which serve as binders.
  isPat n@(Nm _ _) = Just [AnyName n]
  isPat _          = Nothing

  fv' c n@(Nm _ _)  | mode c == Term = singleton (AnyName n)
  fv' _ _                            = emptyC

  swaps' c p x | mode c == Term =
                     case apply p (AnyName x) of
                       AnyName y ->
                         case gcastR (getR y) (getR x) y of
                           Just y' -> y'
                           Nothing -> error "Internal error in swaps': sort mismatch"
  swaps' c p x | mode c == Pat  = x

  aeq' c x y   | mode c == Term = x == y
  aeq' c _ _   | mode c == Pat  = True

{-
  match' _ x  y   | x == y         = Just empty
  match' c n1 n2  | mode c == Term = Just $ single (AnyName n1) (AnyName n2)
  match' c _ _    | mode c == Pat  = Just empty
-}

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

  isPat n@(AnyName (Nm _ _)) = Just [n]
  isPat _                    = Nothing

  fv' c n@(AnyName (Nm _ _))  | mode c == Term = singleton n
  fv' _ _                                      = emptyC

  swaps' c p x = case mode c of
                   Term -> apply p x
                   Pat  -> x

  aeq' _ x y | x == y         = True
  aeq' c _ _ | mode c == Term = False
  aeq' c _ _ | mode c == Pat  = True

{-
  match' _ x y | x == y          = Just empty
  match' c (AnyName n1) (AnyName n2)
    | mode c == Term =
      case gcastR (getR n1) (getR n2) n1 of
        Just n1' -> Just $ single (AnyName n1) (AnyName n2)
        Nothing  -> Nothing
  match' c _ _           | mode c == Pat   = Just empty
-}

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
    isPat _ = Nothing
    isTerm (B p t) = isJust (isPat p) && isTerm t

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

{-
    match' c (B p1 t1) (B p2 t2) = do
      pp <- match' (pat c) p1 p2
      pt <- match' (incr c) t1 t2
      -- need to make sure that all permutations of
      -- bound variables at this
      -- level are the identity
      (pp `join` pt)
-}

    open  c a (B p t)    = B (open (pat c) a p)  (open  (incr c) a t)
    close c a (B p t)    = B (close (pat c) a p) (close (incr c) a t)

    --  Comparing two binding terms.
    acompare' c (B p1 t1) (B p2 t2) =
      lexord (acompare' (pat c) p1 p2) (acompare' (incr c) t1 t2)

    findpatrec _ b = error $ "Binding " ++ show b ++ " used as a pattern"
    nthpatrec    b = error $ "Binding " ++ show b ++ " used as a pattern"

instance (Alpha p, Alpha q) => Alpha (Rebind p q) where
  isTerm _ = False
  isPat (R p q) = combine (isPat p) (isPat q)

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

{-
  match' c (R p1 q1) (R p2 q2) = do
     pp <- match' c p1 p2
     pq <- match' (incr c)  q1 q2
     (pp `join` pq)
-}

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


-- note: for Embeds, when the mode is "term" then we are
-- implementing the "binding" version of the function
-- and we generally should treat the annots as constants
instance Alpha t => Alpha (Embed t) where
   isPat (Embed t)   = if (isTerm t) then Just [] else Nothing
   isTerm t          = False
   isEmbed (Embed t) = isTerm t

   swaps' c pm (Embed t) | mode c == Pat  = Embed (swaps' (term c) pm t)
   swaps' c pm (Embed t) | mode c == Term = Embed t

   fv' c (Embed t) | mode c == Pat  = fv' (term c) t
   fv' c _         | mode c == Term = emptyC

   freshen' c p | mode c == Term = error "freshen' called on a term"
                | otherwise      = return (p, empty)

   lfreshen' c p f         | mode c == Term = error "lfreshen' called on a term"
                           | otherwise      = f p empty

   aeq' c (Embed x) (Embed y) = aeq' (term c) x y

   acompare' c (Embed x) (Embed y) = acompare' (term c) x y

{-
   match' c (Embed x) (Embed y) | mode c == Pat  = match' (term c) x y
   match' c (Embed x) (Embed y) | mode c == Term =
                                    if x `aeq` y
                                    then Just empty
                                    else Nothing
-}

   close c b (Embed x) | mode c == Pat  = Embed (close (term c) b x)
                       | mode c == Term = error "close on Embed"

   open c b (Embed x) | mode c == Pat  = Embed (open (term c) b x)
                      | mode c == Term = error "open on Embed"

   findpatrec _ _ = mempty
   nthpatrec _    = mempty

instance IsEmbed (Embed t) where
  type Embedded (Embed t) = t

  embed             = Embed
  unembed (Embed t) = t

instance Alpha a => Alpha (Shift a) where

  -- The contents of Shift may only be an Embed or another Shift.
  isPat (Shift a)   = if (isEmbed a) then Just [] else Nothing
  isTerm a          = False
  isEmbed (Shift a) = isEmbed a

  close c b (Shift x) = Shift (close (decr c) b x)
  open  c b (Shift x) = Shift (open  (decr c) b x)

instance IsEmbed e => IsEmbed (Shift e) where
  type Embedded (Shift e) = Embedded e

  embed             = Shift . embed
  unembed (Shift e) = unembed e

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