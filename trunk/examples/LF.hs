{- Type checker for LF, based on algorithm in Harper and Pfennig, "On
   Equivalence and Canonical Forms in the LF Type Theory", ACM
   Transactions on Computational Logic, 2000.
-}

{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , MultiParamTypeClasses
           , FlexibleContexts
           , UndecidableInstances
           , TypeSynonymInstances
           , TypeFamilies
  #-}

module LF where

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.Parsec.String

import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Applicative hiding (many)

import qualified Data.Map as M

-- Kinds
data Kind = KPi (Bind (Name Tm, Annot Ty) Kind) -- {x:ty} k
          | Type                                -- type
  deriving Show

-- Types, also called "Families"
data Ty   = TyPi (Bind (Name Tm, Annot Ty) Ty)  -- {x:ty} ty
          | TyApp Ty Tm                         -- ty tm
          | TyConst (Name Ty)                   -- a
  deriving Show

-- Terms, also called "Objects"
data Tm   = Lam (Bind (Name Tm, Annot Ty) Tm)   -- [x:ty] tm
          | TmApp Tm Tm                         -- tm tm
          | TmVar (Name Tm)                     -- x
          | TmConst (Name Tm)                   -- c
  deriving Show

$(derive [''Kind, ''Ty, ''Tm])

instance Alpha Kind
instance Alpha Ty
instance Alpha Tm

-- There are no term variables in types or kinds, so we can just
-- use the default structural Subst instances.
instance Subst Tm Kind
instance Subst Tm Ty

-- For Tm we must implement isvar so the Subst instance knows about
-- term variables.
instance Subst Tm Tm where
  isvar (TmVar v) = Just (v, id)
  isvar _         = Nothing

-- TODO: do this more simply, without binding.
-- A declaration is either a type constant declaration (a name and a kind)
-- or a term constant declaration (a name, type, and optional definition).
data Decl = DeclTy (Name Ty) (Annot Kind)
          | DeclTm (Name Tm) (Annot Ty) (Maybe (Annot Tm))  -- is this right?

-- A program is a sequence of declarations, where each name is bound
-- in the remainder of the program.  We parse files into a Prog, then
-- take the Prog apart piece by piece to typecheck it.  This way we
-- get the full power of the binding library to help us with name
-- shadowing and so on.
data Prog = Nil
          | Cons (Bind Decl Prog)

-- Signatures/contexts

-- todo: don't distinguish between signatures and contexts?

-- A type signature is a mapping from type variables to kinds.
type TySig = M.Map (Name Ty) Kind

-- A term signature is a mappint from term variables to types and
-- (optionally) a definition.
type TmSig = M.Map (Name Tm) (Ty, Maybe Tm)

-- A signature is a pair of a type and term signature.
type Sig = (TySig, TmSig)

-- A context is a mapping from term variables to types.
type Context = M.Map (Name Tm) Ty

extend :: Ord k => M.Map k a -> k -> a -> M.Map k a
extend g x a = M.insert x a g

--------------------
-- Erasure ---------
--------------------

-- Simple kinds and types (no dependency)
data SKind = SKType
           | SKArr STy SKind
  deriving (Eq, Show)
data STy   = STyConst (Name Ty)
           | STyArr STy STy
  deriving (Eq, Show)  -- structural equality is OK here, since there
                       -- are no bound variables.  Otherwise we could
                       -- use 'aeq' from
                       -- Generics.RepLib.Bind.LocallyNameless.

-- Simple contexts map variables to simple types.
type SContext = M.Map (Name Tm) STy

class Erasable t where
  type Erased t :: *
  erase :: t -> Erased t

instance Erasable Kind where
  type Erased Kind = SKind
  erase Type = SKType
  erase (KPi b) = SKArr (erase ty) (erase k)
    where ((_, Annot ty), k) = unsafeUnBind b
          -- this is actually safe since we ignore the name
          -- and promise to erase it from k.

instance Erasable Ty where
  type Erased Ty = STy
  erase (TyPi b)      = STyArr (erase t1) (erase t2)
    where ((_, Annot t1), t2) = unsafeUnBind b
  erase (TyApp ty _)  = erase ty
  erase (TyConst c)   = STyConst c

instance Erasable Context where
  type Erased Context = SContext
  erase = M.map erase

------------------------------
-- Weak head reduction -------
------------------------------

-- TODO: move these to replib
instance (Functor m, LFresh m) => LFresh (MaybeT m) where
  lfresh    = MaybeT . fmap Just . lfresh
  avoid nms = MaybeT . avoid nms . runMaybeT

instance LFresh m => LFresh (ReaderT e m) where
  lfresh    = ReaderT . const . lfresh
  avoid nms = ReaderT . fmap (avoid nms) . runReaderT

-- Reduce a term to weak-head normal form, if it is head-reducible.
--   (Note, this fails if the term is already in WHNF.)
whr :: (LFresh m, MonadPlus m)
    => Tm -> m Tm
whr (TmApp (Lam b) m1) =
  lunbind b $ \((x,_),m2) ->
    return $ subst x m1 m2

whr (TmApp m1 m2) = TmApp `liftM` whr m1 `ap` return m2

whr _ = mzero

-- Reduce a term to weak-head normal form, or return it unchanged if
-- it is not head-reducible.
wh :: (LFresh m, MonadPlus m)
   => Tm -> m Tm
wh t = whr t `mplus` return t

------------------------------
-- Term equality -------------
------------------------------

-- todo: expand in whr, not in tmEqS.

-- Type-directed term equality.  In context Delta, is M <==> N at
-- simple type tau?
tmEq :: (LFresh m, MonadPlus m, MonadReader Sig m)
     => SContext -> Tm -> Tm -> STy -> m ()
tmEq delta m n t = do
  m' <- wh m
  n' <- wh n
  tmEq' delta m' n' t

  -- XXX todo: might be nice to have 'lfresh' and 'lfreshen', the
  -- first NOT taking an argument

  -- XXX todo: need nicer way of doing "string2Name"
-- Type-directed term equality on terms in WHNF
tmEq' :: (LFresh m, MonadPlus m, MonadReader Sig m)
      => SContext -> Tm -> Tm -> STy -> m ()
tmEq' delta m n (STyArr t1 t2) = do
  x <- lfresh (string2Name "_x")
  avoid [AnyName x] $
    tmEq' (extend delta x t1) (TmApp m (TmVar x)) (TmApp n (TmVar x)) t2
tmEq' delta m n a@(STyConst {}) = do
  a' <- tmEqS delta m n
  guard $ a == a'

embedMaybe :: (MonadPlus m) => Maybe a -> m a
embedMaybe = maybe mzero return

-- Structural term equality.  Check whether two terms are structurally
-- equal, and return their "approximate type" if so.
tmEqS :: (LFresh m, MonadPlus m, MonadReader Sig m)
      => SContext -> Tm -> Tm -> m STy

-- First, expand out term constants with definitions.
tmEqS delta a b = do
  a' <- expand a
  b' <- expand b
  tmEqS' delta a' b'

expand :: (MonadPlus m, MonadReader Sig m)
       => Tm -> m Tm
expand (TmConst a) =
  (do
     tmSig <- asks snd
     (_, Just defn) <- embedMaybe $ M.lookup a tmSig
     expand defn
  )
  `mplus` return (TmConst a)
expand b = return b

-- Structural term equality, with the precondition that neither term
-- is a constant with an associated definition.
tmEqS' :: (LFresh m, MonadPlus m, MonadReader Sig m)
       => SContext -> Tm -> Tm -> m STy
tmEqS' delta (TmVar x) (TmVar y) = do
  guard $ x == y
  embedMaybe $ M.lookup x delta

  -- Guaranteed that these term constants have no definition.
tmEqS' _ (TmConst a) (TmConst b) = do
  guard $ a == b
  tmSig <- asks snd
  (tyA,_) <- embedMaybe $ M.lookup a tmSig
  return $ erase tyA

tmEqS' delta (TmApp m1 m2) (TmApp n1 n2) = do
  STyArr t2 t1 <- tmEqS delta m1 n1
  tmEq delta m2 n2 t2
  return t1

tmEqS' _ _ _ = mzero

------------------------------
-- Type equality -------------
------------------------------

-- Kind-directed type equality.
tyEq :: (LFresh m, MonadPlus m, MonadReader Sig m)
     => SContext -> Ty -> Ty -> SKind -> m ()

tyEq delta (TyPi bnd1) (TyPi bnd2) SKType =
  lunbind bnd1 $ \((x, Annot a1), a2) ->
  lunbind bnd2 $ \((_, Annot b1), b2) -> do
    tyEq delta a1 b1 SKType
    tyEq (extend delta x (erase a1)) a2 b2 SKType

tyEq delta a b SKType = do
  t <- tyEqS delta a b
  guard $ t == SKType

tyEq delta a b (SKArr t k) = do
  x <- lfresh (string2Name "_x")
  avoid [AnyName x] $
    tyEq (extend delta x t) (TyApp a (TmVar x)) (TyApp b (TmVar x)) k

-- Structural type equality.
tyEqS :: (LFresh m, MonadPlus m, MonadReader Sig m)
      => SContext -> Ty -> Ty -> m SKind
tyEqS _ (TyConst a) (TyConst b) = do
  guard $ a == b
  tySig <- asks fst
  erase `liftM` (embedMaybe $ M.lookup a tySig)

tyEqS delta (TyApp a m) (TyApp b n) = do
  SKArr t k <- tyEqS delta a b
  tmEq delta m n t
  return k

tyEqS _ _ _ = mzero

------------------------------
-- Kind equality -------------
------------------------------

-- Algorithmic kind equality.
kEq :: (LFresh m, MonadPlus m, MonadReader Sig m)
    => SContext -> Kind -> Kind -> m ()

kEq _ Type Type = return ()

kEq delta (KPi bnd1) (KPi bnd2) =
  lunbind bnd1 $ \((x, Annot a), k) ->
  lunbind bnd2 $ \((_, Annot b), l) -> do
    tyEq delta a b SKType
    kEq (extend delta x (erase a)) k l

kEq _ _ _ = mzero

------------------------------
-- Type checking -------------
------------------------------

-- Compute the type of a term.
tyCheck :: (LFresh m, MonadPlus m, MonadReader Sig m)
        => Context -> Tm -> m Ty
tyCheck gamma (TmVar x)     = embedMaybe $ M.lookup x gamma
tyCheck _     (TmConst c)   = liftM fst . embedMaybe . M.lookup c =<< asks snd
tyCheck gamma (TmApp m1 m2) = do
  TyPi bnd <- tyCheck gamma m1
  a2       <- tyCheck gamma m2
  lunbind bnd $ \((x, Annot a2'), a1) -> do
    tyEq (erase gamma) a2' a2 SKType
    return $ subst x m2 a1
tyCheck gamma (Lam bnd) =
  lunbind bnd $ \((x, Annot a1), m2) -> do
    Type <- kCheck gamma a1
    a2   <- tyCheck (extend gamma x a1) m2
    return $ TyPi (bind (x, Annot a1) a2)

-- Compute the kind of a type.
kCheck :: (LFresh m, MonadPlus m, MonadReader Sig m)
       => Context -> Ty -> m Kind
kCheck _     (TyConst a) = embedMaybe . M.lookup a =<< asks fst
kCheck gamma (TyApp a m) = do
  KPi bnd <- kCheck gamma a
  b       <- tyCheck gamma m
  lunbind bnd $ \((x, Annot b'), k) -> do
    tyEq (erase gamma) b' b SKType
    return $ subst x m k
kCheck gamma (TyPi bnd) =
  lunbind bnd $ \((x, Annot a1), a2) -> do
    Type <- kCheck gamma a1
    Type <- kCheck (extend gamma x a1) a2
    return Type

-- Check the validity of a kind.
sortCheck :: (LFresh m, MonadPlus m, MonadReader Sig m)
          => Context -> Kind -> m ()
sortCheck _     Type      = return ()
sortCheck gamma (KPi bnd) =
  lunbind bnd $ \((x, Annot a), k) -> do
    Type <- kCheck gamma a
    sortCheck (extend gamma x a) k

------------------------------------------------------------
--  Parser  ------------------------------------------------
------------------------------------------------------------

-- to do:
--   1. parse types
--   2. parse declarations
--   3. handle infix operators + precedence

-- XXX "_" should not be a valid name
lexer    = P.makeTokenParser haskellDef

parens   = P.parens     lexer
braces   = P.braces     lexer
brackets = P.brackets   lexer
var      = P.identifier lexer
sym      = P.symbol     lexer

parseTm :: Parser Tm
parseTm = parseAtom `chainl1` (pure TmApp)

parseAtom :: Parser Tm
parseAtom = parens parseTm
        <|> TmVar . string2Name <$> var
            -- parse all identifiers as TmVars for now.  Later, while typechecking,
            -- we will decide which of them to change into TmConsts. (???)
        <|> Lam <$> (
              bind
                <$> brackets ((,) <$> (string2Name <$> var)
                                  <*> (Annot <$> (sym ":" *> parseTy))
                             )
                <*> parseTm
              )

parseTy :: Parser Ty
parseTy = parens parseTy
      <|> foldl TyApp <$> parseTyAtom <*> many parseTm

parseTyAtom :: Parser Ty
parseTyAtom = TyPi <$> (
                bind
                  <$> braces ((,) <$> (string2Name <$> var)
                                  <*> (Annot <$> (sym ":" *> parseTy))
                             )
                  <*> parseTy
                )
            -- XXX parse S -> T using "_" as the name.
          <|> TyConst . string2Name <$> var
