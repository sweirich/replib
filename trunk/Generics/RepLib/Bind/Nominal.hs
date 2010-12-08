{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, TemplateHaskell, TypeOperators, ScopedTypeVariables, TypeSynonymInstances, RankNTypes, GADTs, EmptyDataDecls, StandaloneDeriving #-}

----------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib.Bind.Nominal
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  non-portable (-XKitchenSink)
--
-- Generic implementation of name binding functions, based on the library
-- RepLib. This version uses a nominal representation of binding structure.
--
-- DISCLAIMER: this module probably contains bugs and is noticeably
-- slower than "Generics.RepLib.Bind.LocallyNameless".  At this point
-- we recommend it only for the curious or intrepid.
--
-- Datatypes with binding defined using the 'Name' and 'Bind' types.
-- Important classes are
--     'Alpha' -- the class of types that include binders.
-- These classes are generic, and default implementations exist for all
-- representable types. This file also defines a third generic class,
--     'Subst' -- for subtitution functions.
--
--------------------------------------------------------------------------
module Generics.RepLib.Bind.Nominal
  (-- * Basic types
    Name, Bind, Annot(..), Rebind,

    -- ** Utilities
    integer2Name, string2Name, name2Integer, name2String, makeName,
    name1,name2,name3,name4,name5,name6,name7,name8,name9,name10,
    translate, 

    -- * The 'Alpha' class
    Alpha(..),
    swaps, -- is a bit wonky
    match,
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

   -- * Advanced
   AlphaCtx, matchR1,

   -- * Pay no attention to the man behind the curtain
   -- $paynoattention
   rName, rBind, rRebind, rAnnot) where

import Generics.RepLib
import Generics.RepLib.Bind.PermM

import qualified Data.List as List
import qualified Text.Read as R
import Data.Set (Set)
import Data.Maybe
import qualified Data.Set as S
import Prelude hiding (or)
import Data.Monoid
import qualified Control.Monad as Monad
import Control.Monad.Reader (Reader,ask,local,runReader)
import System.IO.Unsafe (unsafePerformIO)

---------------------------------------------------

$(derive_abstract [''R])
-- The above only works with GHC 7.

-- | Names are things that get bound. The usual protocol
-- is for names to get created by some automatic process,
-- that preserves alpha renaming under operations over
-- Binding instances.
data Name a = Nm (R a) (String,Integer) deriving (Eq, Ord)

-- | Type of a binding.  Morally, the type a should be in the
-- class 'Pattern' and the type b should be in the class 'Alpha'.
-- The Pattern class contains the constructor and a safe
-- destructor for these types.
-- We can Bind an "a" object in a "b" object if we
-- can create "fresh" a objects, and Names can be
-- swapped in "b" objects. Often "a" is Name
-- but that need not be the case.
data Bind a b = B a b


-- | A name with a hidden (existentially quantified) sort.
data AnyName = forall a. Rep a => AnyName (Name a)

-- | An annotation is a 'hole' in a pattern where variables
-- can be used, but not bound. For example patterns may include
-- type annotations, and those annotations can reference variables
-- without binding them.
-- Annotations do nothing special when they appear elsewhere in terms
newtype Annot a = Annot a deriving (Read, Eq)

-- | Rebinding is for telescopes --- i.e. to support patterns that
-- also bind variables that appear later
data Rebind a b = R a (Bind [AnyName] b)

-- Fragily deriving the replib instances for Bind and Name
-- in the same file that they are defined in. This shouldn't
-- work but it does.
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

-- | Get the integer index of an 'AnyName'.
anyName2Integer :: AnyName -> Integer
anyName2Integer (AnyName nm) = name2Integer nm

-- | Get the string part of an 'AnyName'.
anyName2String :: AnyName -> String
anyName2String (AnyName nm) = name2String nm

toSortedName :: Rep a => AnyName -> Maybe (Name a)
toSortedName (AnyName n) = gcastR (getR n) rep n

---------------------------------------------------------------
-- Constructors and destructors for builtin types
---------------------------------------------------------------
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

instance Show (Name a)  where
  show (Nm _ ("",n)) = "_" ++ (show n)
  show (Nm _ (x,0)) = x
  show (Nm _ (x,n)) = x ++ (show n)

name2Integer :: Name a -> Integer
name2Integer (Nm _ (_,x)) = x

integer2Name :: Rep a => Integer -> Name a
integer2Name n = Nm rep ("",n)

-- | Get the string part of a 'Name'.
name2String :: Name a -> String
name2String (Nm _ (s,_)) = s

string2Name :: Rep a => String -> Name a
string2Name s = Nm rep (s,0)

makeName :: Rep a => String -> Integer -> Name a
makeName s i = Nm rep (s,i)

-- | Determine the sort of a 'Name'.
getR :: Name a -> R a
getR (Nm r _)   = r

-- | Change the sort of a name
translate :: (Rep b) => Name a -> Name b
translate (Nm _ x) = Nm rep x

----------------------------------------------------------
-- Binding operations & instances
----------------------------------------------------------
-- | Smart constructor for binders
bind :: (Alpha b,Alpha c) => b -> c -> Bind b c
bind a b = B a b

-- | A destructor for binders that does not guarantee fresh
-- names for the binders.
unsafeUnBind :: Bind a b -> (a,b)
unsafeUnBind (B a b) = (a,b)

instance (Show a, Show b) => Show (Bind a b) where
  showsPrec p (B a b) = showParen (p>0)
      (showString "<" . showsPrec p a . showString "> " . showsPrec 0 b)

instance (Show a) => Show (Annot a) where
  showsPrec p (Annot a) = (showString "[:" . showsPrec 0 a . showString "]")

instance (Alpha a, Alpha b, Read a, Read b) => Read (Bind a b) where
         readPrec = R.parens $ (R.prec app_prec $ do
                                  R.Ident "B" <- R.lexP
                                  m1 <- R.step R.readPrec
                                  m2 <- R.step R.readPrec
                                  return (bind m1 m2))
           where app_prec = 10

         readListPrec = R.readListPrecDefault

----------------------------------------------------------
-- Rebinding operations
----------------------------------------------------------

-- | Constructor for binding in patterns
rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind a b = R a (bind (binders' initial a) b)

instance (Alpha a, Show a, Show b) => Show (Rebind a b) where
  showsPrec p (R a (B a' b)) =  showParen (p>0)
      (showString "<<" . showsPrec p a . sa' . showString ">> " . showsPrec 0 b)
   where sa' =  if binders' initial a == a' then showString ""
                  else showString "/" . showsPrec p a'

-- | destructor for binding patterns, the external names 
-- should have already
-- been freshen'ed. We swap the internal names so that they use the
-- external names
reopen :: (Alpha a, Alpha b) => Rebind a b -> (a, b)
reopen (R a1 (B names b)) = (a1, swaps p b) where
   p = fromJust $ Monad.foldM join empty 
          (zipWith single (binders' initial a1) names)

----------------------------------------------------------
-- Wrappers for operations in the Alpha class
----------------------------------------------------------

aeq :: Alpha a => a -> a -> Bool
aeq t1 t2 = -- aeq' initial t1 t2
  case match t1 t2 of
              Just p -> isid p
              _       -> False


-- | calculate the free variables of the term
fv :: (Rep b, Alpha a) => a -> Set (Name b)
fv = S.map fromJust . S.filter isJust . S.map toSortedName . fv' initial

-- | List the binding variables in a pattern
binders :: (Rep b, Alpha b) => b -> [AnyName]
binders = binders' initial

-- | Set of variables that occur freely in annotations (not binding)
patfv :: (Rep a, Alpha b) => b -> Set (Name a)
patfv = S.map fromJust . S.filter isJust . S.map toSortedName . fv' (pat initial)

-- | The method "swaps" applys a permutation to all free variables
-- in the term.
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


-- | "Locally" freshen an object
lfreshen :: Alpha a => LFresh m => a -> (a -> Perm AnyName -> m b) -> m b
lfreshen = lfreshen' initial

-- | A pattern of type "b" can be freshened if a new
-- copy of "b" can be produced where all old *binding* Names
-- in "b" are replaced with new fresh Names, and the
-- permutation reports which Names were swapped by others.
freshen :: (Fresh m, Alpha a) => a -> m (a, Perm AnyName)
freshen = freshen' initial

-- | Match compares two data structures and produces a permutation
-- of their Names that will make them alpha-equivalent to
-- eachother. (Names that appear in annotations must match exactly.)
-- Also note that two terms are alpha-equivalent when the empty
-- permutation is returned.
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

---------------------------------------------------------------
-- | Many of the operations in the 'Alpha' class take an 'AlphaCtx':
-- stored information about the iteration as it progresses. This type
-- is abstract, as classes that override these operations should just pass
-- the context on.
data AlphaCtx = Term | Pat deriving (Show, Eq, Read)

initial :: AlphaCtx
initial = Term

pat  :: AlphaCtx -> AlphaCtx
pat c  = Pat

term  :: AlphaCtx -> AlphaCtx
term c  = Term

mode :: AlphaCtx -> AlphaCtx
mode = id

-- | The Alpha class is for all terms that may contain binders
-- The 'Rep1' class constraint means that we can only
-- make instances of this class for types that have
-- generic representations. (Derive these using TH and
-- RepLib.)

class (Rep1 (AlphaD) a) => Alpha a where

  aeq' :: AlphaCtx -> a -> a -> Bool
  aeq' = aeqR1 rep1

  -- | swap everything, including bound and free variables, 
  -- parts in annots, etc.
  swapall' :: AlphaCtx -> Perm AnyName -> a -> a
  swapall' = swapallR1 rep1

  -- | The method "swaps'" applys a compound permutation
  swaps' :: AlphaCtx -> Perm AnyName -> a -> a
  swaps' = swapsR1 rep1

  -- | calculate the free variables (aka support)
  fv' :: AlphaCtx -> a -> Set AnyName
  fv' = fvR1 rep1

  -- | list the binding variables in a pattern, in order
  binders' :: AlphaCtx -> a -> [AnyName]
  binders' = bindersR1 rep1

  -- | Match' compares two data structures and produces a
  -- permutation of their free variables that will make them
  -- alpha-equivalent to eachother.
  match' :: AlphaCtx -> a -> a -> Maybe (Perm AnyName)
  match' = matchR1 rep1

  -- | An object of type "a" can be freshened if a new
  -- copy of "a" can be produced where all old Names
  -- in "a" are replaced with new fresh Names, and the
  -- permutation reports which names were swapped by others.
  freshen' :: Fresh m => AlphaCtx -> a -> m (a,Perm AnyName)
  freshen' = freshenR1 rep1

  -- | See 'lfreshen'
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
  lfreshen' = lfreshenR1 rep1


-- class constraint hackery to allow us to override the
-- default definitions for certain classes
data AlphaD a = AlphaD {
  aeqD     :: AlphaCtx -> a -> a -> Bool,
  swapallD   :: AlphaCtx -> (Perm AnyName) -> a -> a,
  swapsD   :: AlphaCtx -> (Perm AnyName) -> a -> a,
  fvD      :: AlphaCtx -> a -> Set AnyName,
  bindersD :: AlphaCtx -> a -> [AnyName],

  matchD   :: AlphaCtx -> a -> a -> Maybe (Perm AnyName),
  freshenD :: forall m. Fresh m => AlphaCtx -> a -> m (a,Perm AnyName),
  lfreshenD :: forall b m. LFresh m => AlphaCtx -> a -> (a -> Perm AnyName -> m b) -> m b
 }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD aeq' swapall' swaps' fv' binders' match' freshen' lfreshen'

-- Generic definitions of the class functions.
-- (All functions that take representations end
-- in 'R1')
aeqR1 :: R1 AlphaD a -> AlphaCtx -> a -> a -> Bool
aeqR1 (Data1 _ cons) = loop cons where
  loop (Con emb reps : rest) p x y =
    case (from emb x, from emb y) of
      (Just p1, Just p2) -> aeq1 reps p p1 p2
      (Nothing, Nothing) -> loop rest p x y
      (_,_)              -> False
  loop [] _ _ _ = error "Impossible"
aeqR1 Int1 = \ _ x y -> x == y
aeqR1 Integer1 = \ _ x y -> x == y
aeqR1 Char1 = \ _ x y -> x == y
aeqR1 _ = \ _ _ _ -> error "Cannot aeq this type"

aeq1 :: MTup (AlphaD) l -> AlphaCtx -> l -> l -> Bool
aeq1 MNil _ Nil Nil = True
aeq1 (r :+: rs) c (p1 :*: t1) (p2 :*: t2) =
  aeqD r c p1 p2 && aeq1 rs c t1 t2

swapsR1 :: R1 (AlphaD) a -> AlphaCtx -> (Perm AnyName) -> a -> a
swapsR1 Char1           = \ _ _ c -> c
swapsR1 Int1            = \ _ _ c -> c
swapsR1 Float1          = \ _ _ c -> c
swapsR1 Integer1        = \ _ _ c -> c
swapsR1 (Data1 _ cons)  = \ p x d ->
  case (findCon cons d) of
  Val c rec kids -> to c (map_l (\z -> swapsD z p x) rec kids)
swapsR1 r               = error ("Cannot swap type " ++ (show r))


swapallR1 :: R1 (AlphaD) a -> AlphaCtx -> (Perm AnyName) -> a -> a
swapallR1 Char1           = \ _ _ c -> c
swapallR1 Int1            = \ _ _ c -> c
swapallR1 Float1          = \ _ _ c -> c
swapallR1 Integer1        = \ _ _ c -> c
swapallR1 (Data1 _ cons)  = \ p x d ->
  case (findCon cons d) of
  Val c rec kids -> to c (map_l (\z -> swapallD z p x) rec kids)
swapallR1 r               = error ("Cannot swap type " ++ (show r))

fvR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> Set AnyName
fvR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> fv1 rec p kids
fvR1 _ = \ _ _ -> S.empty

fv1 :: MTup (AlphaD) l -> AlphaCtx -> l -> Set AnyName
fv1 MNil _ Nil = S.empty
fv1 (r :+: rs) p (p1 :*: t1) =
   fvD r p p1 `S.union` fv1 rs p t1

bindersR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> [AnyName]
bindersR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> binders1 rec p kids
bindersR1 _ = \ _ _ -> []

binders1 :: MTup (AlphaD) l -> AlphaCtx -> l -> [AnyName]
binders1 MNil _ Nil = []
binders1 (r :+: rs) p (p1 :*: t1) =
   bindersD r p p1 ++ binders1 rs p t1


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


freshenR1 :: R1 (AlphaD) a -> Fresh m => AlphaCtx -> a -> m (a,Perm AnyName)
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


instance (Rep a) => Alpha (Name a) where
  fv' c n@(Nm _ _)  | mode c == Term = S.singleton (AnyName n)
  fv' c n           | mode c == Pat  = S.empty

  binders' c n@(Nm _ _)  | mode c == Term = [AnyName n]
  binders' c n           | mode c == Pat  = []

  swapall' c p x =
      case apply p (AnyName x) of
       AnyName y ->
        case cast y of
          Just y' -> y'
          Nothing -> error "Internal error in swaps': sort mismatch"

  swaps' c p x | mode c == Term =
      case apply p (AnyName x) of
       AnyName y ->
        case cast y of
          Just y' -> y'
          Nothing -> error "Internal error in swaps': sort mismatch"
  swaps' c p x | mode c == Pat = x

  aeq' c x y = x == y

  match' c x y  | x == y         = Just empty
  match' c x y  | mode c == Term =
    Just $ single (AnyName x) (AnyName y)
  match' c _ _  | mode c == Pat  = Just empty

  freshen' c nm = case mode c of
     Term -> do x <- fresh nm
                return (x, single (AnyName nm) (AnyName x))
     Pat  -> return (nm, empty)

  lfreshen' c nm f = case mode c of
     Term -> do x <- lfresh nm
                avoid [AnyName x] $ 
                  f x (single (AnyName nm) (AnyName x))
     Pat  -> f nm empty


instance Alpha AnyName  where

  fv' Term n = S.singleton n
  fv' Pat n  = S.empty

  binders' Term n = [n]
  binders' Pat n  = []

  swapall' c p x = apply p x

  swaps' Term p x = apply p x
  swaps' Pat perm x = x

  aeq' c x y = x == y

  match' Term x y = if x == y then Just empty else Just (single x y)
  match' Pat x y = Just empty

  freshen' Term (AnyName nm) = do { x <- fresh nm; return(AnyName x,
                                  (single (AnyName nm) (AnyName x))) }
  freshen' Pat nm = return (nm, empty)

  lfreshen' c (AnyName nm) f = case mode c of
     Term -> do { x <- lfresh nm; avoid [AnyName x] $ f (AnyName x)
                     (single (AnyName nm) (AnyName x)) }
     Pat  -> f (AnyName nm) empty

instance (Alpha a, Alpha b) => Alpha (Bind a b) where
    -- default definition of swapall

    -- to swap in a binder, swap the free variables in the
    -- pattern, then remove the binders from the permutation
    -- and swap in the body
    -- ? why don't we just swap everywhere? we need to be 
    -- able to freshen patterns with annotations
    swaps' p pm (B x y) =
        B (swaps' (pat p) pm x) (swaps' p pm' y) where
            pm' = restrict pm (binders x)

    -- free variables of a binder are the free variables in
    -- the annotations in the pattern plus the free variables
    -- of the body, minus the binders.
    fv' p (B x y) = fv' Pat x `S.union` (fv' p y S.\\ fv' Term x)

    binders' p (B x y) = binders' Pat x ++
                         (binders' p y List.\\ binders' Term x)

    -- default definition of freshen'
{-
    freshen' p (B x y) = do
--       (x', p1)  <- freshen' (all p) x -- freshen the binders & annots
       (y', p3) <- freshen' p (swaps' p p1 y) -- freshen body
       return (B x' y', p1 <> p3)
-}

    lfreshen' c (B x y) f =
      avoid (S.elems $ fv' c x) $
        lfreshen' (pat c) x (\ x' pm1 ->
        lfreshen' c (swaps' c pm1 y) (\ y' pm2 ->
        f (B x' y') (pm1 <> pm2)))

    -- this version of aeq seems to work
    aeq' p (B x1 y1) (B x2 y2) 
       -- if the binders match, compare the patterns & bodies
       | bx1 == bx2 = aeq' p x1 x2 && aeq' p y1 y2
       -- if any binders of the first appear freely in the 
       -- second body, not aeq
       | (S.fromList bx1) `S.intersection` 
         (fv' Term y2 S.\\ fv' Term y1) /= S.empty = False
       -- otherwise swap the binding variables in the pattern
       -- and *all* of the variables in the body
       | True = aeq' p x1 (swaps' Term pm x2) && 
                aeq' p y1 (swapall' Term pm y2)
     where bx1 = binders' Term x1
           bx2 = binders' Term x2
           pm  = foldl (<>) empty (zipWith single bx1 bx2)


    -- basic idea of match
    -- if binders x1 == binders x2 then
        --- match the annots in x1 and x2 and match the bodies y1 y2
    -- if binders x1 /= binders x2 then
        -- make sure binders of x1 are not free in the body of y2
        -- swap (x1,x2) in y2
        -- match the annots & match the bodies
        -- make sure none of the binders escapes in the resulting match
    -- ingredients:
        -- match the binders, ignoring the annots
        -- match the annots, ignoring the binders
        -- list the binding variables
    match' p (B x1 y1) (B x2 y2) 
      |  bx1 == bx2 = do
            pm1 <- match' Pat x1 x2
            pm2 <- match' p y1 y2
            pm1 `join` pm2
      | (S.fromList bx1) `S.intersection` 
        (fv' Term y2 S.\\ fv' Term y1)
            /= S.empty = Nothing
      | True = do
            -- make sure that we can match up the binders
            -- this will fail if there are repeated vars
            pm <- Monad.foldM join empty (zipWith single bx1 bx2)
            let x2' = swaps' initial pm x2
            let y2' = swapall' initial pm y2
            pm1 <- match' Pat x1 x2'
            pm2 <- match' p   y1 y2'
            -- note pm2 should not permute binders
            -- (see a16) Dropping would give us "set binding"
            if S.fromList bx1 `S.intersection` 
               S.fromList (support pm2) /= S.empty
              then Nothing
              else pm1 `join` pm2
       where bx1 = binders' Term x1
             bx2 = binders' Term x2

instance (Alpha a, Alpha b) => Alpha (Rebind a b) where

   -- free variables of the external binder
   -- plus free vars of the annots in the binder
   -- plus free vars of the body minus any
   --     binding vars of internal binder
   fv' p (R x (B ns y)) = fv' p x `S.union`
      (fv' p y S.\\ S.fromList ns)

   binders' p (R x (B ns y)) = binders' p x ++
      (binders' p y List.\\ ns)


   swaps' Term pm (R x (B ns y)) =
      R (swaps' Term pm x) (B ns (swaps' Term pm' y)) where
            pm' = restrict pm ns

   match' p (R x1 (B n1 y1)) (R x2 (B n2 y2)) = do
      px  <- match' p x1 x2   -- external names
      pb  <- match' p (B n1 y1) (B n2 y2)
      px `join` pb

   freshen' p (R x (B x1 y)) = do
      (x', pm1) <- freshen' p x
      (y', pm2) <- freshen' p (swaps' p pm1 y)
      return (R x (B x1 y'), pm1 <> pm2)


instance (Eq a, Alpha a) => Alpha (Annot a) where

   swaps' Pat  pm (Annot t) = Annot (swaps' Term pm t)
   swaps' Term pm (Annot t) = Annot t

   fv' Pat (Annot t)        = fv' Term t
   fv' Term _               = S.empty

   binders' Pat (Annot t)   = binders' Term t
   binders' Term _          = []


   freshen' Pat (Annot t)  = do
     (t', p) <- freshen' Term t
     return (Annot t', p)
   freshen' Term a       = return (a, empty)

   match' Pat (Annot x) (Annot y)  = match' Term x y
   match' Term (Annot x) (Annot y) = if x `aeq` y
                                    then Just empty
                                    else Nothing

-- Instances for other types (mostly) use the default definitions.
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


-- Definitions of the class members for abstract types.
{-
abs_swaps' :: Alpha a => AlphaCtx -> Perm Name -> a -> a
abs_swaps' _ p s = s
abs_fv' :: Alpha a => AlphaCtx -> a -> [Name]
abs_fv' _ s = []
abs_freshen' :: (Fresh m, Alpha a) => AlphaCtx -> a -> m (a, Perm Name)
abs_freshen' _ b = return (b, empty)
abs_match' :: (Eq a, Alpha a) => AlphaCtx -> a -> a -> Maybe (Perm Name)
abs_match' _ x1 x2 = if x1 == x2 then Just empty else Nothing
-}

-------------------------------------------------------
-- | A monad "m" supports the nextInteger operation if it
-- can generate new fresh integers

class Monad m => HasNext m where
  nextInteger :: m Integer
  resetNext   :: Integer -> m ()

-- | A monad "m" supports the "fresh" operation if it
-- can generate a new unique names.

class (Monad m, HasNext m) => Fresh m where
  fresh :: Name a -> m (Name a)
  fresh (Nm r (s,j)) = do { i <- nextInteger; return (Nm r (s,i)) }

instance HasNext m => Fresh m where
  fresh (Nm r (s,j)) = do { n <- nextInteger; return (Nm r (s,n)) }

-- | Unbind is the destructor of a binding. It ensures that
-- the names in the binding b are fresh.
unbind  :: (Alpha b,Fresh m,Alpha c) => Bind b c -> m (b,c)
unbind (B x y) = do
    (x',perm) <- freshen x
    return(x', swaps perm y)

-- | Destruct two bindings simultanously, if they match, using the
-- same list of fresh names
unbind2  :: (Fresh m,Alpha b,Alpha c, Alpha d) =>
   Bind b c -> Bind b d -> m (Maybe (b,c,d))
unbind2 (B x1 y1) (B x2 y2) = do
   (x1', perm1) <- freshen x1
   case match x1' x2 of
      (Just perm2) ->
         return $ Just (x1', swaps perm1 y1, swaps perm2 y2)
      Nothing -> return Nothing

unbind3  :: (Fresh m,Alpha b,Alpha c, Alpha d, Alpha e) =>
   Bind b c -> Bind b d -> Bind b e -> m (Maybe (b,c,d,e))
unbind3 (B x1 y1) (B x2 y2) (B x3 y3) = do
   (x1', perm1) <- freshen x1
   case (match x1' x2, match x1' x3) of
      (Just perm2, Just perm3) ->
         return $ Just (x1', swaps perm1 y1, swaps perm2 y2, swaps perm3 y3)
      _ -> return Nothing

-----------------------------------------------------------------
-- | Locally fresh monad
-- This is the class of
-- monads that support freshness in an (implicit) local scope.  Names
-- drawn are fresh for this particular scope, but not globally fresh.
-- This class has a basic instance based on the reader monad.
class Monad m => LFresh m where
  -- | pick a new name that is fresh for the current (implicit) scope.
  lfresh  :: Rep a => Name a -> m (Name a)
  -- | avoid these names when freshening in the subcomputation.
  avoid   :: [AnyName] -> m a -> m a

-- | Reader monad instance for local freshness class.
instance LFresh (Reader Integer) where
  lfresh (Nm r (s,j)) = do { n <- ask; return (Nm r (s, max j (n+1))) }
  avoid []          = id
  avoid names       = local (max k) where
        k = maximum (map anyName2Integer names)

-- | Destruct a binding in the LFresh monad.
lunbind :: (LFresh m, Alpha a, Alpha b) => Bind a b -> m (a, b)
lunbind (B a b) =
  avoid (S.elems $ fv' initial b) $ error "UNIMP"


lunbind2  :: (LFresh m, Alpha b, Alpha c, Alpha d) =>
            Bind b c -> Bind b d -> m (Maybe (b,c,d))
lunbind2 (B b1 c) (B b2 d) = do
      case match b1 b2 of
         Just _ -> do
           (b', c') <- lunbind (B b1 c)
           return $ error "UNIMP"
         Nothing -> return Nothing

lunbind3  :: (LFresh m, Alpha b, Alpha c, Alpha d, Alpha e) =>
            Bind b c -> Bind b d -> Bind b e ->  m (Maybe (b,c,d,e))
lunbind3 (B b1 c) (B b2 d) (B b3 e) = do
      case (match b1 b2, match b1 b3) of
         (Just _, Just _) -> do
           (b', c') <- lunbind (B b1 c)
           return $ error "UNIMP"
         _ -> return Nothing


---------------------------------------------------------------

-- | Capture-avoiding substitution, in a monad so that we can rename
-- variables at binding locations and avoid capture

subst :: (Alpha a, Alpha b, Subst b a) => Name b -> b -> a -> a
subst n u x =
 runReader (avoid ([AnyName n] ++ (S.elems $ fv' initial u)++(S.elems $ fv' initial x)) $ lsubst n u x) (0 :: Integer)

substs :: (Alpha a, Alpha b, Subst b a) => [Name b] -> [b] -> a -> a
substs ns us x =
 runReader (avoid ((map AnyName ns) ++ (concatMap (S.elems . (fv' initial)) us)++(S.elems $ fv' initial x)) $ lsubsts ns us x)
     (0 :: Integer)


class (Rep1 (SubstD b) a) => Subst b a where
  isvar :: a -> Maybe (Name b, b -> a)
  isvar x = Nothing

  lsubst :: LFresh m => Name b -> b -> a -> m a
  lsubst n u x =
      case isvar x of
        Just (m, f) | m == n -> return (f u)
        Just (_, _) -> return x
        Nothing -> substR1 rep1 n u x


  lsubsts :: LFresh m => [Name b] -> [b] -> a -> m a
  lsubsts ns us x =
      case isvar x of
        Just (m, f) -> case m `List.elemIndex` ns of
                    Just i  -> return (f (us !! i))
                    Nothing -> return x
        Nothing -> substsR1 rep1 ns us x


data SubstD b a = SubstD {
   substD  :: LFresh m => Name b -> b -> a -> m a
  ,substsD :: LFresh m => [Name b] -> [b] -> a -> m a
}

instance Subst b a => Sat (SubstD b a) where
  dict = SubstD lsubst lsubsts

substR1 :: LFresh m => R1 (SubstD b) a -> Name b -> b -> a -> m a
substR1 (Data1 _ cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids -> do
      w <- mapM_l (\z -> substD z x y) rec kids
      return (to c w)
substR1 _               = \ _ _ c -> return c

substsR1 :: LFresh m => R1 (SubstD b) a -> [Name b] -> [b] -> a -> m a
substsR1 (Data1 _ cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids -> do
      z <- mapM_l (\ w -> substsD w x y) rec kids
      return (to c z)
substsR1 _               = \ _ _ c -> return c

instance Subst c AnyName where

instance Subst b Int where
instance Subst b Bool where
instance Subst b () where
instance Subst b Char where
instance Subst b Integer where
instance Subst b Float where
instance Subst b Double where
instance (Subst c a, Subst c b) => Subst c (a,b) where
instance (Subst c a, Subst c b, Subst c d) => Subst c (a,b,d) where
instance (Subst c a, Subst c b, Subst c d, Subst c e) => Subst c (a,b,d,e) where
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) => Subst c (a,b,d,e,f) where

instance (Subst c a) => Subst c [a] where
instance (Subst c a) => Subst c (Maybe a) where
instance (Subst c a, Subst c b) => Subst c (Either a b) where

instance Rep a => Subst b (R a) where
instance Rep a => Subst b (Name a) where


instance (Subst c a, Alpha a, Subst c b, Alpha b) =>
    Subst c (Bind a b) where
  lsubst n u (B a b) =
      lfreshen' Term a ( \ a' p -> do
         let b' = swapall' Term p b
         a'' <- lsubst n u a'
         b'' <- lsubst n u b'
         return (B a'' b''))

  lsubsts n u (B a b) =
      lfreshen' Term a ( \ a' p -> do
         a'' <- lsubsts n u a'
         let b' = swaps' Pat p (swaps' Term p b)
         b'' <- lsubsts n u b'
         return (B a'' b''))

instance (Subst c b, Subst c a, Alpha a, Alpha b) =>
    Subst c (Rebind a b) where
instance (Subst c a) => Subst c (Annot a) where


-------------------- TESTING CODE --------------------------------
data Exp = V (Name Exp)
         | A Exp Exp
         | L (Bind (Name Exp) Exp) deriving (Show)

$(derive [''Exp])

instance Alpha Exp
instance Subst Exp Exp where
   isvar (V n) = Just (n, id)
   isvar _     = Nothing

-- deriving instance Eq Exp
-- deriving instance Ord Exp

nameA, nameB, nameC :: Name Exp
nameA = string2Name "A"
nameB = string2Name "B"
nameC = string2Name "C"

assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
   tests_aeq
   tests_fv
   tests_big
   tests_subst

perm = single (AnyName nameA)(AnyName nameB)

naeq x y = not (aeq x y)

a10a = bind (rebind (nameA, Annot nameC) ()) nameA
a10b = bind (rebind (nameB, Annot nameC) ()) nameB

a10c = bind (rebind (nameA, Annot nameA) ()) nameA
a10d = bind (rebind (nameB, Annot nameA) ()) nameB

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
   assert "a9a" $ (bind (rebind nameA (Annot nameA)) nameA) `aeq`
                  (bind (rebind nameB (Annot nameB)) nameB)
   assert "a10" $ bind (rebind (nameA, Annot nameA) ()) nameA `aeq`
                  bind (rebind (nameB, Annot nameA) ()) nameB
   assert "a10a" $ a10a `aeq` a10b
   assert "a11" $ bind (rebind (nameA, Annot nameA) ()) nameA `naeq`
                  bind (rebind (nameB, Annot nameB) ()) nameB
   assert "a12" $ bind (Annot nameA) () `naeq` bind (Annot nameB) ()
   assert "a13" $ bind (Annot nameA) () `aeq` bind (Annot nameA) ()
   assert "a14" $ bind (rebind (Annot nameA) ()) () `naeq`
                  bind (rebind (Annot nameB) ()) ()
   assert "a15" $ (rebind (nameA, Annot nameA) ()) `naeq`
                  (rebind (name4, Annot nameC) ())
   assert "a16" $ bind (nameA, nameB) nameA `naeq` 
                  bind (nameB, nameA) nameA
   assert "a17" $ bind (nameA, nameB) nameA `naeq` bind (nameA, nameB) nameB
   assert "a18" $ (nameA, nameA) `naeq` (nameA, nameB)
   assert "a19" $ match (nameA, nameA) (nameB, nameC) == Nothing
   assert "a20" $ (L (bind name2 (L (bind name3 (L (bind name4  (A (V name2) (A (V name3) (V name4))))))))) `aeq`  (L (bind name1 (L (bind name2 (L (bind name3  (A (V name1) (A (V name2) (V name3)))))))))

emptyNE :: Set (Name Exp)
emptyNE = S.empty

tests_fv = do
   assert "f1" $ fv (bind nameA nameA) == emptyNE
   assert "f2" $ fv' Pat (bind nameA nameA) == S.empty
   assert "f3" $ fv (bind (rebind nameA (Annot nameA)) nameA) == emptyNE
   assert "f4" $ fv (bind nameA nameB) == S.singleton nameB
   assert "f5" $ fv (bind (nameA, Annot nameB) nameA) == S.singleton nameB
   assert "f7" $ fv (bind (nameB, Annot nameB) nameB) == S.singleton nameB
   assert "f8" $ fv (rebind nameA nameB) == S.fromList [nameA, nameB]
   assert "f9" $ fv' Pat (rebind nameA nameA) == S.empty
   assert "f9a" $ fv (rebind nameA (Annot nameA)) == S.singleton nameA
   assert "f9b" $ fv' Pat (rebind nameA (Annot nameA)) == S.empty
   assert "f10" $ fv (rebind (nameA, Annot nameA) ()) == S.singleton nameA
   assert "f11" $ fv' Pat (rebind (nameA, Annot nameA) ()) == S.singleton (AnyName nameA)
   assert "f10a" $ fv (rebind (nameA, Annot nameB) ()) == S.singleton nameA
   assert "f11a" $ fv' Pat (rebind (nameA, Annot nameB) ()) == S.singleton (AnyName nameB)


   assert "f12" $ fv (bind (Annot nameA) ()) == S.singleton nameA
   assert "f12a" $ fv' Pat (bind (Annot nameA) ()) == S.singleton (AnyName nameA)

   assert "f14" $ fv (rebind (Annot nameA) ()) == emptyNE
   assert "f14a" $ fv' Pat (rebind (Annot nameA) ()) == S.singleton (AnyName nameA)

tests_subst = do
   assert "s1" $ subst nameA (V nameB) (V nameA) `aeq` (V nameB)
   assert "s2" $ subst nameA (V nameB) (V nameC) `aeq` (V nameC)
   assert "s3" $ subst nameA (V nameB) (L (bind nameA (V nameA))) `aeq`
                                       (L (bind nameA (V nameA)))

   assert "s4" $ subst nameA (V nameB) (L (bind nameB (V nameB))) `aeq`
                                       (L (bind nameA (V nameA)))

   assert "s5" $ subst nameA (V nameB) (L (bind nameC (V nameA))) `aeq`
                                       (L (bind nameC (V nameB)))

   assert "s6" $ subst nameA (V nameA) (L (bind nameC (V nameA))) `aeq`
                                       (L (bind nameC (V nameA)))

   assert "s7" $ subst nameA (V nameA) (L (bind nameA (V nameB))) `aeq`
                                       (L (bind nameA (V nameB)))
   assert "s9" $ subst name1 (V name1)
                  (L (bind name1 (L (bind name2 (L (bind name3
                           (A (V name1) (A (V name2) (V name3))))))))) `aeq`
                  (L (bind name1 (L (bind name2 (L (bind name3
                           (A (V name1) (A (V name2) (V name3)))))))))


mkbig :: [Name Exp] -> Exp -> Exp
mkbig (n : names) body =
    L (bind n (mkbig names (A (V n) body)))
mkbig [] body = body

big1 = mkbig (map integer2Name (take 100 [1 ..])) (V name11)
big2 = mkbig (map integer2Name (take 101 [1 ..])) (V name11)

tests_big = do
   assert "b1" $ big1 `naeq` big2
   assert "b2" $ fv big1 == emptyNE
   assert "b3" $ big1 `aeq` subst name11 (V name11) big1


