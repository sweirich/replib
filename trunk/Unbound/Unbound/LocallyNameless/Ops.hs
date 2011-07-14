{-# OPTIONS_GHC -fno-warn-orphans #-}
----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless.Ops
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Portability :  GHC only (-XKitchenSink)
--
-- Generic operations defined in terms of the RepLib framework and the
-- 'Alpha' type class.
----------------------------------------------------------------------
module Unbound.LocallyNameless.Ops where

import Generics.RepLib

import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Fresh
import Unbound.Util
import Unbound.PermM

import Data.Maybe as Maybe
import Data.List  as List

import Control.Monad (liftM)
import qualified Text.Read as R

----------------------------------------------------------
-- Binding operations
----------------------------------------------------------

-- | A smart constructor for binders, also sometimes referred to as
--   \"close\".  Free variables in the term are taken to be references
--   to matching binders in the pattern.  (Free variables with no
--   matching binders will remain free.)
bind :: (Alpha p, Alpha t) => p -> t -> Bind p t
bind p t = B p (closeT p t)

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

----------------------------------------------------------
-- Set Binding operations
----------------------------------------------------------

permCloseAny :: (Alpha t) => [AnyName] -> t -> ([AnyName],t)
permCloseAny ns t = (ns', closeT ns' t) where
        -- find where the names occur in the body of the term
        list   = map (\n -> (n, findpat t n)) ns
        -- remove unused names
        list'  = filter (\(n,posn) -> Maybe.isJust posn) list
        -- sort by position
        list'' :: [(AnyName, Maybe Integer)]
        list'' = List.sortBy (\(n1,Just p1) (n2,Just p2) -> compare p1 p2) list'
        -- new names
        ns'    = map fst list''

-- Given a list of names and a term, close the term with those names
-- where the indices of the bound variables occur in sequential order
-- and return the equivalent ordering of the names, dropping those 
-- that do not occur in the term at all
-- For example:
--    permClose [b,c]    (b,c)   =  ([b,c], (0,1))    -- standard close
--    permClose [b,c]    (c,b)   =  ([c,b], (0,1))    -- vars reordered
--    permClose [a,b,c]  (c,b)   =  ([c,b], (0,1))    -- var dropped
--    permClose [a,b,c]  (c,b,c) =  ([c,b], (0,1,0))  -- additional occurrence ok

permClose :: (Alpha a, Alpha t) => [Name a] -> t -> ([Name a],t)
permClose ns t = (ns', closeT ns' t) where
        -- find where the names occur in the body of the term
        list   = map (\n -> (n, findpat t (AnyName n))) ns
        -- remove unused names
        list'  = filter (\(n,posn) -> Maybe.isJust posn) list
        -- sort by position
        list'' = List.sortBy (\(n1,Just p1) (n2,Just p2) -> compare p1 p2) list'
        -- new names
        ns'    = map fst list''

-- | Bind the pattern in the term "up-to-permutation" of bound variables.
-- For example, the following 4 terms are *all* alpha-equivalent
--     permbind [a,b] (a,b)
--     permbind [a,b] (b,a)
--     permbind [b,a] (a,b)
--     permbind [b,a] (b,a)
-- None of these terms is equivalent to a term with a redundant pattern
--     permbind [a,b,c] (a,b)
permbind :: (Alpha p, Alpha t) => p -> t -> Bind p t
permbind p t = B p t' where
         (ns, t') = permCloseAny (bindersAny p) t

-- | Bind the list of names in the term "up-to" permutation and dropping
-- of unused variables.
-- For example, the following 5 terms are *all* alpha-equivalent
--     setbind [a,b] (a,b)
--     setbind [a,b] (b,a)
--     setbind [b,a] (a,b)
--     setbind [b,a] (b,a)
--     setbind [a,b,c] (a,b)
setbind ::(Alpha a, Alpha t) => [Name a] -> t -> Bind [Name a] t
setbind p t = B ns t' where
         (ns, t') = permClose (binders p) t

setbindAny :: (Alpha t) => [AnyName] -> t -> Bind [AnyName] t
setbindAny p t = B ns t' where
         (ns, t') = permCloseAny (bindersAny p) t
           

 
----------------------------------------------------------
-- Rebinding operations
----------------------------------------------------------

-- | Constructor for rebinding patterns.
rebind :: (Alpha p1, Alpha p2) => p1 -> p2 -> Rebind p1 p2
rebind p1 p2 = R p1 (closeP p1 p2)

-- | Compare for alpha-equality.
instance (Alpha p1, Alpha p2, Eq p2) => Eq (Rebind p1 p2) where
   b1 == b2 = b1 `aeqBinders` b2

-- | Destructor for rebinding patterns.  It does not need a monadic
--   context for generating fresh names, since @Rebind@ can only occur
--   in the pattern of a 'Bind'; hence a previous call to 'unbind' (or
--   something similar) must have already freshened the names at this
--   point.
unrebind :: (Alpha p1, Alpha p2) => Rebind p1 p2 -> (p1, p2)
unrebind (R p1 p2) = (p1, openP p1 p2)

----------------------------------------------------------
-- Rec operations
----------------------------------------------------------

-- | Constructor for recursive patterns.
rec :: (Alpha p) => p -> Rec p
rec p = Rec (closeP p p) where

-- | Destructor for recursive patterns.
unrec :: (Alpha p) => Rec p -> p
unrec (Rec p) = openP p p

----------------------------------------------------------
-- TRec operations
----------------------------------------------------------

-- | Constructor for recursive abstractions.
trec :: Alpha p => p -> TRec p
trec p = TRec $ bind (rec p) ()

-- | Destructor for recursive abstractions which picks globally fresh
--   names for the binders.
untrec :: (Fresh m, Alpha p) => TRec p -> m p
untrec (TRec b) = (unrec . fst) `liftM` unbind b

-- | Destructor for recursive abstractions which picks /locally/ fresh
--   names for binders (see 'LFresh').
luntrec :: (LFresh m, Alpha p) => TRec p -> m p
luntrec (TRec b) = lunbind b $ return . unrec . fst

----------------------------------------------------------
-- Wrappers for operations in the Alpha class
----------------------------------------------------------

-- | Determine the alpha-equivalence of two terms.
aeq :: Alpha t => t -> t -> Bool
aeq t1 t2 = aeq' initial t1 t2

-- | Determine (alpha-)equivalence of patterns.  Do they bind the same
--   variables in the same patterns and have alpha-equivalent
--   annotations in matching positions?
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
fv :: (Rep a, Alpha t, Collection f) => t -> f (Name a)
fv = filterC
   . cmap toSortedName
   . fvAny

-- | Calculate the variables (of any sort) that occur freely in terms
--   embedded within a pattern (but are not bound by the pattern).
patfvAny :: (Alpha p, Collection f) => p -> f AnyName
patfvAny = fv' (pat initial)

-- | Calculate the variables of a particular sort that occur freely in
--   terms embedded within a pattern (but are not bound by the pattern).
patfv :: (Rep a, Alpha p, Collection f) => p -> f (Name a)
patfv = filterC
      . cmap toSortedName
      . patfvAny

-- | Calculate the binding variables (of any sort) in a pattern.
bindersAny :: (Alpha p, Collection f) => p -> f AnyName
bindersAny = fvAny

-- | Calculate the binding variables (of a particular sort) in a
--   pattern.
binders :: (Rep a, Alpha p, Collection f) => p -> f (Name a)
binders = fv


-- | Apply a permutation to a term.
swaps :: Alpha t => Perm AnyName -> t -> t
swaps = swaps' initial

-- | Apply a permutation to the binding variables in a pattern.
--   Embedded terms are left alone by the permutation.
swapsBinders :: Alpha p => Perm AnyName -> p -> p
swapsBinders = swaps' initial

-- | Apply a permutation to the embedded terms in a pattern. Binding
--   names are left alone by the permutation.
swapsEmbeds :: Alpha p => Perm AnyName -> p -> p
swapsEmbeds = swaps' (pat initial)

-- | \"Locally\" freshen a pattern, replacing all binding names with
--   new names that are not already \"in scope\". The second argument
--   is a continuation, which takes the renamed term and a permutation
--   that specifies how the pattern has been renamed.  The resulting
--   computation will be run with the in-scope set extended by the
--   names just generated.
lfreshen :: (Alpha p, LFresh m) => p -> (p -> Perm AnyName -> m b) -> m b
lfreshen = lfreshen' (pat initial)

-- | Freshen a pattern by replacing all old binding 'Name's with new
--   fresh 'Name's, returning a new pattern and a @'Perm' 'Name'@
--   specifying how 'Name's were replaced.
freshen :: (Alpha p, Fresh m) => p -> m (p, Perm AnyName)
freshen = freshen' (pat initial)

{-
-- | Compare two terms and produce a permutation of their 'Name's that
-- will make them alpha-equivalent to each other.  Return 'Nothing' if
-- no such renaming is possible.  Note that two terms are
-- alpha-equivalent if the empty permutation is returned.
match   :: Alpha a => a -> a -> Maybe (Perm AnyName)
match   = match' initial

-- | Compare two patterns, ignoring the names of binders, and produce
-- a permutation of their annotations to make them alpha-equivalent
-- to eachother. Return 'Nothing' if no such renaming is possible.
matchEmbeds :: Alpha a => a -> a -> Maybe (Perm AnyName)
matchEmbeds = match' (pat initial)

-- | Compare two patterns for equality and produce a permutation of
-- their binding 'Names' to make them alpha-equivalent to each other
-- (Free 'Name's that appear in annotations must match exactly). Return
-- 'Nothing' if no such renaming is possible.
matchBinders ::  Alpha a => a -> a -> Maybe (Perm AnyName)
matchBinders = match' initial
-}

------------------------------------------------------------
-- Opening binders
------------------------------------------------------------

-- | Unbind (also known as \"open\") is the simplest destructor for
--   bindings. It ensures that the names in the binding are globally
--   fresh, using a monad which is an instance of the 'Fresh' type
--   class.
unbind :: (Fresh m, Alpha p, Alpha t) => Bind p t -> m (p,t)
unbind (B p t) = do
      (p', _) <- freshen p
      return (p', openT p' t)

-- | Unbind two terms with the /same/ fresh names, provided the
--   binders have the same number of binding variables.  If the
--   patterns have different numbers of binding variables, return
--   @Nothing@.  Otherwise, return the renamed patterns and the
--   associated terms.
unbind2 :: (Fresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2) =>
            Bind p1 t1 -> Bind p2 t2 -> m (Maybe (p1,t1,p2,t2))
unbind2 (B p1 t1) (B p2 t2) = do
      case mkPerm (fvAny p2) (fvAny p1) of
         Just pm -> do
           (p1', pm') <- freshen p1
           return $ Just (p1', openT p1' t1,
                          swaps (pm' <> pm) p2, openT p1' t2)
         Nothing -> return Nothing

-- | Unbind three terms with the same fresh names, provided the
--   binders have the same number of binding variables.  See the
--   documentation for 'unbind2' for more details.
unbind3 :: (Fresh m, Alpha p1, Alpha p2, Alpha p3, Alpha t1, Alpha t2, Alpha t3) =>
            Bind p1 t1 -> Bind p2 t2 -> Bind p3 t3 ->  m (Maybe (p1,t1,p2,t2,p3,t3))
unbind3 (B p1 t1) (B p2 t2) (B p3 t3) = do
      case ( mkPerm (fvAny p2) (fvAny p1)
           , mkPerm (fvAny p3) (fvAny p1) ) of
         (Just pm12, Just pm13) -> do
           (p1', p') <- freshen p1
           return $ Just (p1', openT p1' t1,
                          swaps (p' <> pm12) p2, openT p1' t2,
                          swaps (p' <> pm13) p3, openT p1' t3)
         _ -> return Nothing

-- | @lunbind@ opens a binding in an 'LFresh' monad, ensuring that the
--   names chosen for the binders are /locally/ fresh.  The components
--   of the binding are passed to a /continuation/, and the resulting
--   monadic action is run in a context extended to avoid choosing new
--   names which are the same as the ones chosen for this binding.
--
--   For more information, see the documentation for the 'LFresh' type
--   class.
lunbind :: (LFresh m, Alpha p, Alpha t) => Bind p t -> ((p, t) -> m c) -> m c
lunbind (B p t) g =
  lfreshen p (\x _ -> g (x, openT x t))


-- | Unbind two terms with the same locally fresh names, provided the
--   patterns have the same number of binding variables.  See the
--   documentation for 'unbind2' and 'lunbind' for more details.
lunbind2  :: (LFresh m, Alpha p1, Alpha p2, Alpha t1, Alpha t2) =>
            Bind p1 t1 -> Bind p2 t2 -> (Maybe (p1,t1,p2,t2) -> m r) -> m r
lunbind2 (B p1 t1) (B p2 t2) g =
  case mkPerm (fvAny p2) (fvAny p1) of
    Just pm1 ->
      lfreshen p1 (\p1' pm2 -> g $ Just (p1', openT p1' t1,
                                         swaps (pm2 <> pm1) p2, openT p1' t2))
    Nothing -> g Nothing

-- | Unbind three terms with the same locally fresh names, provided
--   the binders have the same number of binding variables.  See the
--   documentation for 'unbind2' and 'lunbind' for more details.
lunbind3 :: (LFresh m, Alpha p1, Alpha p2, Alpha p3, Alpha t1, Alpha t2, Alpha t3) =>
            Bind p1 t1 -> Bind p2 t2 -> Bind p3 t3 ->
            (Maybe (p1,t1,p2,t2,p3,t3) -> m r) ->
            m r
lunbind3 (B p1 t1) (B p2 t2) (B p3 t3) g =
  case ( mkPerm (fvAny p2) (fvAny p1)
       , mkPerm (fvAny p3) (fvAny p1) ) of
         (Just pm12, Just pm13) ->
           lfreshen p1 (\p1' pm' -> g $ Just (p1', openT p1' t1,
                                              swaps (pm' <> pm12) p2, openT p1' t2,
                                              swaps (pm' <> pm13) p3, openT p1' t3))
         _ -> g Nothing
