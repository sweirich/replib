{-# LANGUAGE FlexibleInstances, UndecidableInstances, FlexibleContexts, MultiParamTypeClasses, TemplateHaskell, TypeOperators, ScopedTypeVariables, TypeSynonymInstances, RankNTypes, GADTs, EmptyDataDecls, StandaloneDeriving #-}

-- | Generic implementation of name binding functions, based on the library
-- RepLib.
-- Datatypes with binding defined using the 'Name' and 'Bind' types.
-- Important classes are
--     'Alpha' -- the class of types that include binders.
-- These classes are generic, and default implementations exist for all
-- representable types. This file also defines a third generic class,
--     'Subst' -- for subtitution functions.
-- A generic substitution function requires implementing the case for
-- variables and then calling the function 'substR1' for the other cases.
module Generics.RepLib.Bind.Nominal
  (Fresh(..),Alpha(..),HasNext(..)
  ,aeq
  ,AlphaCtx
  ,Name,Perm,Bind,rName,rBind
  ,Subst(..),substR1,subst,substs
  ,unsafeUnBind,bind,unbind,unbind2,unbind3
  ,Rebind,rRebind,rebind,reopen
  ,Annot(..),rAnnot,Or,or
  ,name1,name2,name3,name4,name5,name2Int
  ,integer2Name,string2Name
  ,binders,patfv,fv,matchR1
  ,abs_swaps',abs_fv',abs_freshen',abs_match'
  ) where

import Generics.RepLib
import Generics.RepLib.Bind.PermM

import qualified Data.List as List
import qualified Text.Read as R
import Data.Set (Set)
import qualified Data.Set as S
import Prelude hiding (or)
import Data.Monoid
import Control.Monad.Reader (Reader,ask,local,runReader)
import System.IO.Unsafe (unsafePerformIO)

---------------------------------------------------

-- | Names are things that get bound. The usual protocol
-- is for names to get created by some automatic process,
-- that preserves alpha renaming under operations over
-- Binding instances.
newtype Name = Nm (String,Integer) deriving (Eq, Ord,Read)

-- | Type of a binding.  Morally, the type a should be in the
-- class 'Pattern' and the type b should be in the class 'Alpha'.
-- The Pattern class contains the constructor and a safe
-- destructor for these types.
-- We can Bind an "a" object in a "b" object if we
-- can create "fresh" a objects, and Names can be
-- swapped in "b" objects. Often "a" is Name
-- but that need not be the case.
data Bind a b = B a b deriving (Show)

-- | An annotation is a 'hole' in a pattern where variables
-- can be used, but not bound. For example patterns may include
-- type annotations, and those annotations can reference variables
-- without binding them.
-- Annotations do nothing special when they appear elsewhere in terms
newtype Annot a = Annot a deriving (Show, Read, Eq)

-- | Rebinding is for telescopes --- i.e. to support patterns that
-- also bind variables that appear later
data Rebind a b = R a (Bind a b) deriving (Show)

-- | Special type for 'OR' patterns, those that match two different ways
-- yet bind the same variables
data Or a b = Or a b deriving (Show, Read, Eq)

-- Fragily deriving the replib instances for Bind and Name
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

instance Show Name  where
  show (Nm ("",n)) = "_" ++ (show n)
  show (Nm (x,0)) = x
  show (Nm (x,n)) = x ++ (show n)

name2Int :: Name -> Integer
name2Int (Nm (_,x)) = x

integer2Name :: Integer -> Name
integer2Name n = Nm ("",n)

string2Name :: String -> Name
string2Name s = Nm(s,0)

-- | Generate a name that is fresh for a set of names
freshFor :: [Name] -> Name
freshFor l = integer2Name (1 + maximum (map name2Int l))

-- | Smart constructor for binders
bind :: (Alpha b,Alpha c) => b -> c -> Bind b c
bind a b = B a b

-- | A destructor for binders that does not guarantee fresh
-- names for the binders.
unsafeUnBind :: Bind a b -> (a,b)
unsafeUnBind (B a b) = (a,b)

instance (Alpha a, Alpha b, Eq b) => Eq (Bind a b) where
   (B x y) == (B m n) =
      case match x m of
         Just p | isid p -> y == n
         Just p -> y == swaps p n &&
                   S.null (fv x `S.intersection` fv n)
         Nothing -> False

instance (Alpha a, Alpha b, Ord a, Ord b) => Ord (Bind a b) where
   compare (B a1 b1) (B a2 b2) =
       case (match a1 a2) of
         Just p  -> case compare a1 (swaps p a2) of
                      EQ -> compare b1 b2
                      otherwise -> otherwise
         Nothing -> compare a1 a2

instance (Alpha a, Alpha b, Read a, Read b) => Read (Bind a b) where
         readPrec = R.parens $ (R.prec app_prec $ do
                                  R.Ident "B" <- R.lexP
                                  m1 <- R.step R.readPrec
                                  m2 <- R.step R.readPrec
                                  return (bind m1 m2))
           where app_prec = 10

         readListPrec = R.readListPrecDefault

-- | Constructor for binding in patterns
rebind :: (Alpha a, Alpha b) => a -> b -> Rebind a b
rebind a b = R a (bind a b)

instance (Eq a, Alpha a, Alpha b, Eq b) => Eq (Rebind a b) where
   (R a1 b1) == (R a2 b2) = a1 == a2 && b1 == b2


-- | destructor for binding patterns, the external names should have already
-- been freshen'ed. We swap the internal names so that they use the
-- external names
reopen :: (Alpha a, Alpha b) => Rebind a b -> (a, b)
reopen (R a1 (B a2 b)) = (a1, swaps p b) where
   p = foldl (<>) empty (zipWith single (S.elems $ fv a1) (S.elems $ fv a2))

-- | Or patterns must bind exactly the same list of names
or :: (Alpha a, Alpha b) => a -> b -> Maybe (Or a b)
or a b = if fv a == fv b then Just (Or a b) else Nothing

unOr :: Or a b -> (a, b)
unOr (Or a b) = (a,b)

---------------------------------------------------------------
aeq :: Alpha a => a -> a -> Bool
aeq t1 t2 = case match t1 t2 of
              Just p -> isid p
              _       -> False

-- | List the binding variables in a pattern
binders :: Alpha b => b -> Set Name
binders = fv

-- | List variables that occur freely in annotations (not binding)
patfv :: Alpha b => b -> Set Name
patfv = fv' (pat initial)

-- | calculate the free variables of the term
fv :: Alpha a => a -> Set Name
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

  -- | The method "swaps'" applys a compound permutation.
  swaps' :: AlphaCtx -> Perm Name -> a -> a
  swaps' = swapsR1 rep1

  -- | calculate the free variables (aka support)
  fv' :: AlphaCtx -> a -> Set Name
  fv' = fvR1 rep1

  -- | Match' compares two data structures and produces a
  -- permutation of their free variables that will make them
  -- alpha-equivalent to eachother.
  match' :: AlphaCtx -> a -> a -> Maybe (Perm Name)
  match' = matchR1 rep1

  -- | An object of type "a" can be freshened if a new
  -- copy of "a" can be produced where all old Names
  -- in "a" are replaced with new fresh Names, and the
  -- permutation reports which names were swapped by others.
  freshen' :: Fresh m => AlphaCtx -> a -> m (a,Perm Name)
  freshen' = freshenR1 rep1

  -- | See 'lfreshen'
  lfreshen' :: LFresh m => AlphaCtx -> a -> (a -> Perm Name -> m b) -> m b
  lfreshen' = lfreshenR1 rep1


-- class constraint hackery to allow us to override the
-- default definitions for certain classes
data AlphaD a = AlphaD {
  swapsD   :: AlphaCtx -> (Perm Name) -> a -> a,
  fvD      :: AlphaCtx -> a -> Set Name,
  matchD   :: AlphaCtx -> a -> a -> Maybe (Perm Name),
  freshenD :: forall m. Fresh m => AlphaCtx -> a -> m (a,Perm Name),
  lfreshenD :: forall b m. LFresh m => AlphaCtx -> a -> (a -> Perm Name -> m b) -> m b
 }

instance Alpha a => Sat (AlphaD a) where
  dict = AlphaD swaps' fv' match' freshen' lfreshen'

-- Generic definitions of the class functions.
-- (All functions that take representations end
-- in 'R1')
swapsR1 :: R1 (AlphaD) a -> AlphaCtx -> (Perm Name) -> a -> a
swapsR1 Char1           = \ _ _ c -> c
swapsR1 Int1            = \ _ _ c -> c
swapsR1 Float1          = \ _ _ c -> c
swapsR1 Integer1        = \ _ _ c -> c
swapsR1 (Data1 _ cons)  = \ p x d ->
  case (findCon cons d) of
  Val c rec kids -> to c (map_l (\z -> swapsD z p x) rec kids)
swapsR1 r               = error ("Cannot swap type " ++ (show r))

fvR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> Set Name
fvR1 (Data1 _ cons) = \ p  d ->
  case (findCon cons d) of
    Val _ rec kids -> fv1 rec p kids
fvR1 _ = \ _ _ -> S.empty

fv1 :: MTup (AlphaD) l -> AlphaCtx -> l -> Set Name
fv1 MNil _ Nil = S.empty
fv1 (r :+: rs) p (p1 :*: t1) =
   fvD r p p1 `S.union` fv1 rs p t1

matchR1 :: R1 (AlphaD) a -> AlphaCtx -> a -> a -> Maybe (Perm Name)
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

match1 :: MTup (AlphaD) l -> AlphaCtx -> l -> l -> Maybe (Perm Name)
match1 MNil _ Nil Nil = Just empty
match1 (r :+: rs) c (p1 :*: t1) (p2 :*: t2) = do
  l1 <- matchD r c p1 p2
  l2 <- match1 rs c t1 t2
  (l1 `join` l2)


freshenR1 :: R1 (AlphaD) a -> Fresh m => AlphaCtx -> a -> m (a,Perm Name)
freshenR1 (Data1 _ cons) = \ p d ->
   case findCon cons d of
     Val c rec kids -> do
       (l, p') <- freshenL rec p kids
       return (to c l, p')
freshenR1 _ = \ _ n -> return (n, empty)

freshenL :: Fresh m => MTup (AlphaD) l -> AlphaCtx -> l -> m (l, Perm Name)
freshenL MNil _ Nil = return (Nil, empty)
freshenL (r :+: rs) p (t :*: ts) = do
  (xs, p2) <- freshenL rs p ts
  (x, p1) <- freshenD r p (swapsD r p p2 t)
  return ( x :*: xs, p1 <> p2)

lfreshenR1 :: LFresh m => R1 AlphaD a -> AlphaCtx -> a ->
              (a -> Perm Name -> m b) -> m b
lfreshenR1 (Data1 _ cons) = \p d f ->
   case findCon cons d of
     Val c rec kids -> lfreshenL rec p kids (\ l p' -> f (to c l) p')
lfreshenR1 _ = \ _ n f -> f n empty

lfreshenL :: LFresh m => MTup (AlphaD) l -> AlphaCtx -> l ->
              (l -> Perm Name -> m b) -> m b
lfreshenL MNil _ Nil f = f Nil empty
lfreshenL (r :+: rs) p (t :*: ts) f =
  lfreshenL rs p ts ( \ y p2 ->
  lfreshenD r p (swapsD r p p2 t) ( \ x p1 ->
     f (x :*: y) (p1 <> p2)))

instance Alpha Name  where

  fv' Term n = S.singleton n
  fv' Pat n  = S.empty

  swaps' Term p x = apply p x
  swaps' Pat perm x = x

  match' Term x y = if x == y then Just empty else Just (single x y)
  match' Pat x y = if x == y then Just empty else Nothing

  freshen' Term nm = do { x <- fresh nm; return(x,(single nm x)) }
  freshen' Pat nm = return (nm, empty)

  lfreshen' c nm f = case mode c of
     Term -> do { x <- lfresh nm; avoid [x] $ f x (single nm x) }
     Pat  -> f nm empty

instance (Alpha a, Alpha b) => Alpha (Bind a b) where
    -- default swaps'

    fv' p (B x y) = fv' (pat p) x `S.union` (fv' p y S.\\ fv' Term x)
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

    -- basic idea of match
    -- if binders x1 == binders x2 then
        --- match the annots in x1 and x2 and match the bodies y1 y2
    -- if binders x1 /= binders x2 then
        -- make sure binders of x1 are not free in (B x2 y2)
        -- swap x1,x2 in y2
        -- match the annots & match the bodies
    -- ingredients:
        -- match the binders, ignoring the annots
        -- match the annots, ignoring the binders
        -- list the binding variables
    match' Term (B x1 y1) (B x2 y2) =
        case (match' Term x1 x2) of
          Just pmt | isid pmt -> do
            pm1 <- match' Pat x1 x2
            pm2 <- match' Term y1 y2
            (pm1 `join` pm2)
          Just pmt ->
            let xs = binders x1 in
            if xs `S.intersection` fv y2 == S.empty then do
               pm1 <- match' Pat x1 x2
               pm2 <- match' Term y1 (swaps' Term pmt y2)
               (pm1 `join` pm2)
             else Nothing
          _ -> Nothing
    match' Pat _ _ = error "cannot match binders here."


instance (Alpha a, Alpha b) => Alpha (Rebind a b) where
   fv' Term (R x (B x' y)) = fv' Term x `S.union` fv' Term y
   fv' Pat  (R x (B x' y)) = fv' Pat x `S.union`
                   ((fv' Pat y) S.\\ (fv' Term x))

   freshen' p (R x (B x1 y)) = do
      (x', pm1) <- freshen' p x
      (y', pm2) <- freshen' p (swaps' p pm1 y)
      return (R x (B x1 y'), pm1 <> pm2)

   match' p (R x1 (B x1' y1)) (R x2 (B x2' y2)) = do
     px <- match' p x1 x2
     py <- match' p y1 (swaps' Pat px y2)
     return (px <> py)


instance (Eq a, Alpha a) => Alpha (Annot a) where

   swaps' Pat  pm (Annot t) = Annot (swaps' Term pm t)
   swaps' Term pm (Annot t) = Annot t

   fv' Pat (Annot t)       = fv' Term t
   fv' Term _              = S.empty

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


-- Definitions of the class members for abstract types.
abs_swaps' :: Alpha a => AlphaCtx -> Perm Name -> a -> a
abs_swaps' _ p s = s
abs_fv' :: Alpha a => AlphaCtx -> a -> [Name]
abs_fv' _ s = []
abs_freshen' :: (Fresh m, Alpha a) => AlphaCtx -> a -> m (a, Perm Name)
abs_freshen' _ b = return (b, empty)
abs_match' :: (Eq a, Alpha a) => AlphaCtx -> a -> a -> Maybe (Perm Name)
abs_match' _ x1 x2 = if x1 == x2 then Just empty else Nothing

-------------------------------------------------------
-- | A monad "m" supports the nextInteger operation if it
-- can generate new fresh integers

class Monad m => HasNext m where
  nextInteger :: m Integer
  resetNext   :: Integer -> m ()

-- | A monad "m" supports the "fresh" operation if it
-- can generate a new unique names.

class (Monad m, HasNext m) => Fresh m where
  fresh :: Name -> m Name
  fresh (Nm (s,j)) = do { i <- nextInteger; return (Nm (s,i)) }

instance HasNext m => Fresh m where
  fresh (Nm (s,j)) = do { n <- nextInteger; return (Nm (s,n)) }

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
  lfresh  :: Name -> m Name
  -- | avoid these names when freshening in the subcomputation.
  avoid   :: [Name] -> m a -> m a

-- | Reader monad instance for local freshness class.
instance LFresh (Reader Integer) where
  lfresh (Nm (s,j)) = do { n <- ask; return (Nm (s, max j (n+1))) }
  avoid names       = local (max k) where
        k = maximum (map name2Int names)

-- | Destruct a binding in the LFresh monad.
lunbind :: (LFresh m, Alpha a, Alpha b) => Bind a b -> m (a, b)
lunbind (B a b) =
  avoid (S.elems $ fv b) $ error "UNIMP"


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

subst :: (Alpha a, Alpha b, Subst b a) => Name -> b -> a -> a
subst n u x =
 runReader (avoid ([n] ++ (S.elems $ fv u)++(S.elems $ fv x)) $ lsubst n u x) (0 :: Integer)

substs :: (Alpha a, Alpha b, Subst b a) => [Name] -> [b] -> a -> a
substs ns us x =
 runReader (avoid (ns ++ (concatMap (S.elems . fv) us)++(S.elems $ fv x)) $ lsubsts ns us x)
     (0 :: Integer)


class (Rep1 (SubstD b) a) => Subst b a where
  isvar :: a -> Maybe (Name, b -> a)
  isvar x = Nothing

  lsubst :: LFresh m => Name -> b -> a -> m a
  lsubst n u x =
      case isvar x of
        Just (m, f) | m == n -> return (f u)
        Just (_, _) -> return x
        Nothing -> substR1 rep1 n u x


  lsubsts :: LFresh m => [Name] -> [b] -> a -> m a
  lsubsts ns us x =
      case isvar x of
        Just (m, f) -> case m `List.elemIndex` ns of
                    Just i  -> return (f (us !! i))
                    Nothing -> return x
        Nothing -> substsR1 rep1 ns us x


data SubstD b a = SubstD {
  substD :: LFresh m => Name -> b -> a -> m a
  ,substsD :: LFresh m => [Name] -> [b] -> a -> m a
}

instance Subst b a => Sat (SubstD b a) where
  dict = SubstD lsubst lsubsts

substR1 :: LFresh m => R1 (SubstD b) a -> Name -> b -> a -> m a
substR1 (Data1 _ cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids -> do
      w <- mapM_l (\z -> substD z x y) rec kids
      return (to c w)
substR1 _               = \ _ _ c -> return c

substsR1 :: LFresh m => R1 (SubstD b) a -> [Name] -> [b] -> a -> m a
substsR1 (Data1 _ cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids -> do
      z <- mapM_l (\ w -> substsD w x y) rec kids
      return (to c z)
substsR1 _               = \ _ _ c -> return c

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
instance (Subst c a, Subst c b, Subst c d, Subst c e, Subst c f) => Subst c (a,b,d,e,f) where

instance (Subst c a) => Subst c [a] where
instance (Subst c a) => Subst c (Maybe a) where
instance (Subst c a, Subst c b) => Subst c (Either a b) where

instance (Subst c a, Alpha a, Subst c b, Alpha b) =>
    Subst c (Bind a b) where
  lsubst n u (B a b) =
      lfreshen' Term a ( \ a' p -> do
         let b' = swaps' Term p b
         a'' <- lsubst n u a'
         b'' <- lsubst n u b'
         return (B a'' b''))

  lsubsts n u (B a b) =
      lfreshen' Term a ( \ a' p -> do
         a'' <- lsubsts n u a'
         let b' = swaps' Term p b
         b'' <- lsubsts n u b'
         return (B a'' b''))

instance (Subst c b, Subst c a, Alpha a, Alpha b) =>
    Subst c (Rebind a b) where
instance (Subst c a) => Subst c (Annot a) where
instance (Subst c a, Subst c b) => Subst c (Or a b) where


-------------------- TESTING CODE --------------------------------
data V = V Name deriving (Show,Eq,Ord)
$(derive [''V])


ftest :: Alpha a => a -> (a , Perm Name)
ftest x = runReader
          (lfreshen x (\ x' p' -> return (x', p'))) (5 :: Integer)


instance Alpha V where
instance Subst V V where
   isvar (V n) =  Just (n, id)


assert :: String -> Bool -> IO ()
assert s True = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

do_tests :: ()
do_tests =
   unsafePerformIO $ do
   tests_aeq
   tests_fv
   tests_big

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
   assert "a9a" $ (bind (rebind name1 (Annot name1)) name1) ==
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

tests_fv = do
   assert "f1" $ fv (bind name1 name1) == S.empty
   assert "f2" $ fv' (pat initial) (bind name1 name1) == S.empty
   assert "f4" $ fv (bind name1 name2) == S.singleton name2
   assert "f5" $ fv (bind (name1, Annot name2) name1) == S.singleton name2
   assert "f7" $ fv (bind (name2, Annot name2) name2) == S.singleton name2
   assert "f8" $ fv (rebind name1 name2) == S.fromList [name1, name2]
   assert "f9" $ fv' (pat initial) (rebind name1 name1) == S.empty
   assert "f3" $ fv (bind (rebind name1 (Annot name1)) name1) == S.empty
   assert "f10" $ fv (rebind (name1, Annot name1) ()) == S.singleton name1
   assert "f11" $ fv' (pat initial) (rebind (name1, Annot name1) ()) == S.singleton name1
   assert "f12" $ fv (bind (Annot name1) ()) == S.singleton name1
   assert "f14" $ fv (rebind (Annot name1) ()) == S.empty

big1 =
    bind name1
      (bind name2
       (bind name3
        (bind name4
          (bind name5
            (bind name6
              (bind name7
                (bind name8
                  (bind name9
                   (bind name10
                     (name1, name2, name3, (name4, name5, name6, (name7, name8, name9, name10, V name11))))))))))))

big2 =
    bind name2
      (bind name1
       (bind name3
        (bind name4
          (bind name5
            (bind name6
              (bind name7
                (bind name8
                  (bind name9
                   (bind name10
                     (name2, name1, name3, (name4, name5, name6, (name7, name8, name9, name10, V name11))))))))))))

tests_big = do
   assert "b1" $ big1 == big2
   assert "b2" $ fv big1 == S.singleton name11
   assert "b3" $ big1 == subst name11 (V name11) big1


