module Unbound.LocallyNameless.Ops where

import Generics.RepLib

import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Fresh
import Unbound.Util
import Unbound.PermM

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
-- Rebinding operations
----------------------------------------------------------

-- | Constructor for binding in patterns.
rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind a b = R a (closeP a b)

-- | Compare for alpha-equality.
instance (Alpha a, Alpha b, Eq b) => Eq (Rebind a b) where
   b1 == b2 = b1 `aeqBinders` b2

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

----------------------------------------------------------
-- TRec operations
----------------------------------------------------------

trec :: Alpha p => p -> TRec p
trec p = TRec $ bind (rec p) ()

untrec :: (Fresh m, Alpha p) => TRec p -> m p
untrec (TRec b) = (unrec . fst) `liftM` unbind b

luntrec :: (LFresh m, Alpha p) => TRec p -> m p
luntrec (TRec b) = lunbind b $ return . unrec . fst

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
fv :: (Rep a, Alpha t, Collection f) => t -> f (Name a)
fv = filterC
   . cmap toSortedName
   . fvAny

-- | Calculate the variables (of any sort) that occur freely within
--   pattern annotations (but are not bound by the pattern).
patfvAny :: (Alpha p, Collection f) => p -> f AnyName
patfvAny = fv' (pat initial)

-- | Calculate the variables of a particular sort that occur freely in
--   pattern annotations (but are not bound by the pattern).
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
swaps :: Alpha a => Perm AnyName -> a -> a
swaps = swaps' initial

-- | Apply a permutation to the binding variables in a pattern.
-- Embedded terms are left alone by the permutation.
swapsBinders :: Alpha a => Perm AnyName -> a -> a
swapsBinders = swaps' initial

-- | Apply a permutation to the annotations in a pattern. Binding
-- names are left alone by the permutation.
swapsEmbeds :: Alpha a => Perm AnyName -> a -> a
swapsEmbeds = swaps' (pat initial)


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
      case mkPerm (fvAny p1) (fvAny p2) of
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
      case ( mkPerm (fvAny p1) (fvAny p2)
           , mkPerm (fvAny p1) (fvAny p3) ) of
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
  case mkPerm (fvAny p1) (fvAny p2) of
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
  case ( mkPerm (fvAny p1) (fvAny p2)
       , mkPerm (fvAny p1) (fvAny p3) ) of
         (Just pm12, Just pm13) ->
           lfreshen p1 (\p1' pm' -> g $ Just (p1', openT p1' t1,
                                              swaps (pm' <> pm12) p2, openT p1' t2,
                                              swaps (pm' <> pm13) p3, openT p1' t3))
         _ -> g Nothing
