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
           , GeneralizedNewtypeDeriving
  #-}

module LF where

import Prelude hiding (lookup)

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
import qualified Data.Set as S

------------------------------
-- Syntax --------------------
------------------------------

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
  deriving Show
  -- Harper and Pfennig distinguish between term *variables* and term
  -- *constants*, but for our purposes there is no need to distinguish
  -- between them.

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

-- A declaration is either
--   * a type constant declaration (a name and a kind),
--   * a term constant declaration (a name, type, and optional definition), or
--   * a fixity/precedence declaration.
data Decl = DeclTy (Name Ty) Kind
          | DeclTm (Name Tm) Ty (Maybe Tm)
          | DeclInfix (Name Tm) Assoc Int

data Assoc = L | R

-- A program is a sequence of declarations.
type Prog = [Decl]

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

$(derive [''SKind, ''STy])

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

instance Erasable Tm where
  type Erased Tm = Tm
  erase t = t

instance (Erasable a, Erasable b) => Erasable (a,b) where
  type Erased (a,b) = (Erased a, Erased b)
  erase (x,y) = (erase x, erase y)

------------------------------
-- Signatures/contexts -------
------------------------------

data Context tm ty = C (M.Map (Name Tm) tm) (M.Map (Name Ty) ty)

emptyCtx :: Context tm ty
emptyCtx = C M.empty M.empty

extendTm :: Name Tm -> tm -> Context tm ty -> Context tm ty
extendTm x t (C tm ty) = C (M.insert x t tm) ty

extendTy :: Name Ty -> ty -> Context tm ty -> Context tm ty
extendTy x k (C tm ty) = C tm (M.insert x k ty)

lookupTm :: (MonadPlus m, MonadReader (Context tm ty) m)
         => Name Tm -> m tm
lookupTm x = ask >>= \(C tm _) -> embedMaybe (M.lookup x tm)

lookupTy :: (MonadPlus m, MonadReader (Context tm ty) m)
         => Name Ty -> m ty
lookupTy x = ask >>= \(C _ ty) -> embedMaybe (M.lookup x ty)

embedMaybe :: (MonadPlus m) => Maybe a -> m a
embedMaybe = maybe mzero return

instance Erasable a => Erasable (M.Map k a) where
  type Erased (M.Map k a) = M.Map k (Erased a)
  erase = M.map erase

instance (Erasable tm, Erasable ty) => Erasable (Context tm ty) where
  type Erased (Context tm ty) = Context (Erased tm) (Erased ty)
  erase (C tm ty) = C (erase tm) (erase ty)

instance (Erasable a) => Erasable (Maybe a) where
  type Erased (Maybe a) = Maybe (Erased a)
  erase = fmap erase

type Ctx  = Context (Ty, Maybe Tm) Kind
type SCtx = Erased Ctx

withTmBinding :: (MonadReader (Context (tm, Maybe Tm) ty) m, LFresh m)
              => Name Tm -> tm -> m r -> m r
withTmBinding x b = do
  avoid [AnyName x] . local (extendTm x (b, Nothing))

withTmDefn :: (MonadReader (Context tm ty) m, LFresh m)
           => Name Tm -> tm -> m r -> m r
withTmDefn x b = do
  avoid [AnyName x] . local (extendTm x b)

withTyBinding :: (MonadReader (Context tm ty) m, LFresh m)
              => Name Ty -> ty -> m r -> m r
withTyBinding x b = do
  avoid [AnyName x] . local (extendTy x b)

------------------------------
-- Typechecking monad --------
------------------------------

newtype TcM ctx a = TcM { unTcM :: MaybeT (ReaderT ctx FreshM) a }
  deriving (Functor, Applicative, Monad, MonadReader ctx, MonadPlus, LFresh)

getTcMAvoids :: TcM ctx (S.Set AnyName)
getTcMAvoids = TcM . lift . lift $ getAvoids

-- | Continue a TcM computation, given a context and set of names to
--   avoid.
contTcM :: TcM ctx a -> ctx -> S.Set AnyName -> Maybe a
contTcM (TcM m) c nms = flip contFreshM nms . flip runReaderT c . runMaybeT $ m

-- | Run a TcM computation in an empty context.
runTcM :: TcM (Context tm ty) a -> Maybe a
runTcM m = contTcM m emptyCtx S.empty

-- | Run a subcomputation with an erased context.
withErasedCtx :: TcM SCtx a -> TcM Ctx a
withErasedCtx m = do
  c <- ask
  nms <- getTcMAvoids
  embedMaybe $ contTcM m (erase c) nms

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

-- Reduce a term to weak-head normal form, or return it unchanged if
-- it is not head-reducible.  Works in erased or unerased contexts.
whr :: (LFresh m, MonadReader (Context (a,Maybe Tm) b) m, MonadPlus m)
    => Tm -> m Tm
whr (TmVar a) = (do
  (_, Just defn) <- lookupTm a
  whr defn)
  `mplus`
  return (TmVar a)

whr (TmApp (Lam b) m1) =
  lunbind b $ \((x,_),m2) ->
    whr $ subst x m1 m2

whr (TmApp m1 m2) = TmApp `liftM` whr m1 `ap` return m2

whr t = return t

------------------------------
-- Term equality -------------
------------------------------

-- Type-directed term equality.  In context Delta, is M <==> N at
-- simple type tau?
tmEq :: (LFresh m, MonadPlus m, MonadReader SCtx m)
     => Tm -> Tm -> STy -> m ()
tmEq m n t = do
  m' <- whr m
  n' <- whr n
  tmEq' m' n' t

  -- XXX todo: might be nice to have 'lfresh' and 'lfreshen', the
  -- first NOT taking an argument

  -- XXX todo: need nicer way of doing "string2Name"
-- Type-directed term equality on terms in WHNF
tmEq' :: (LFresh m, MonadPlus m, MonadReader SCtx m)
      => Tm -> Tm -> STy -> m ()
tmEq' m n (STyArr t1 t2) = do
  x <- lfresh (string2Name "_x")
  withTmBinding x t1 $
    tmEq' (TmApp m (TmVar x)) (TmApp n (TmVar x)) t2
tmEq' m n a@(STyConst {}) = do
  a' <- tmEqS m n
  guard $ a == a'

-- Structural term equality.  Check whether two terms in WHNF are
-- structurally equal, and return their "approximate type" if so.
tmEqS :: (LFresh m, MonadPlus m, MonadReader SCtx m)
      => Tm -> Tm -> m STy

tmEqS (TmVar a) (TmVar b) = do
  guard $ a == b
  (tyA,_) <- lookupTm a
  return tyA

tmEqS (TmApp m1 m2) (TmApp n1 n2) = do
  STyArr t2 t1 <- tmEqS m1 n1
  tmEq m2 n2 t2
  return t1

tmEqS _ _ = mzero

------------------------------
-- Type equality -------------
------------------------------

-- Kind-directed type equality.
tyEq :: (LFresh m, MonadPlus m, MonadReader SCtx m)
     => Ty -> Ty -> SKind -> m ()

tyEq (TyPi bnd1) (TyPi bnd2) SKType =
  lunbind bnd1 $ \((x, Annot a1), a2) ->
  lunbind bnd2 $ \((_, Annot b1), b2) -> do
    tyEq a1 b1 SKType
    withTmBinding x (erase a1) $ tyEq a2 b2 SKType

tyEq a b SKType = do
  t <- tyEqS a b
  guard $ t == SKType

tyEq a b (SKArr t k) = do
  x <- lfresh (string2Name "_x")
  withTmBinding x t $ tyEq (TyApp a (TmVar x)) (TyApp b (TmVar x)) k

-- Structural type equality.
tyEqS :: (LFresh m, MonadPlus m, MonadReader SCtx m)
      => Ty -> Ty -> m SKind
tyEqS (TyConst a) (TyConst b) = do
  guard $ a == b
  lookupTy a

tyEqS (TyApp a m) (TyApp b n) = do
  SKArr t k <- tyEqS a b
  tmEq m n t
  return k

tyEqS _ _ = mzero

------------------------------
-- Kind equality -------------
------------------------------

-- Algorithmic kind equality.
kEq :: (LFresh m, MonadPlus m, MonadReader SCtx m)
    => Kind -> Kind -> m ()

kEq Type Type = return ()

kEq (KPi bnd1) (KPi bnd2) =
  lunbind bnd1 $ \((x, Annot a), k) ->
  lunbind bnd2 $ \((_, Annot b), l) -> do
    tyEq a b SKType
    withTmBinding x (erase a) $ kEq k l

kEq _ _ = mzero

------------------------------
-- Type checking -------------
------------------------------

-- Compute the type of a term.
tyCheck :: Tm -> TcM Ctx Ty
tyCheck (TmVar x)     = liftM fst $ lookupTm x
tyCheck (TmApp m1 m2) = do
  TyPi bnd <- tyCheck m1
  a2       <- tyCheck m2
  lunbind bnd $ \((x, Annot a2'), a1) -> do
    withErasedCtx $ tyEq a2' a2 SKType
    return $ subst x m2 a1
tyCheck (Lam bnd) =
  lunbind bnd $ \((x, Annot a1), m2) -> do
    Type <- kCheck a1
    a2   <- withTmBinding x a1 $ tyCheck m2
    return $ TyPi (bind (x, Annot a1) a2)

-- Compute the kind of a type.
kCheck :: Ty -> TcM Ctx Kind
kCheck (TyConst a) = lookupTy a
kCheck (TyApp a m) = do
  KPi bnd <- kCheck a
  b       <- tyCheck m
  lunbind bnd $ \((x, Annot b'), k) -> do
    withErasedCtx $ tyEq b' b SKType
    return $ subst x m k
kCheck (TyPi bnd) =
  lunbind bnd $ \((x, Annot a1), a2) -> do
    Type <- kCheck a1
    Type <- withTmBinding x a1 $ kCheck a2
    return Type

-- Check the validity of a kind.
sortCheck :: Kind -> TcM Ctx ()
sortCheck Type      = return ()
sortCheck (KPi bnd) =
  lunbind bnd $ \((x, Annot a), k) -> do
    Type <- kCheck a
    withTmBinding x a $ sortCheck k

------------------------------------------------------------
--  Parser  ------------------------------------------------
------------------------------------------------------------

-- to do:
--   1. parse types
--   2. parse declarations
--   3. handle infix operators + precedence

lexer    = P.makeTokenParser haskellDef

parens   = P.parens     lexer
braces   = P.braces     lexer
brackets = P.brackets   lexer
var      = P.identifier lexer
sym      = P.symbol     lexer
op       = P.reservedOp lexer

parseTm :: Parser Tm
parseTm = parseAtom `chainl1` (pure TmApp)

parseAtom :: Parser Tm
parseAtom = parens parseTm
        <|> TmVar . string2Name <$> var
        <|> Lam <$> (
              bind
                <$> brackets ((,) <$> (string2Name <$> var)
                                  <*> (Annot <$> (sym ":" *> parseTy))
                             )
                <*> parseTm
              )

parseTy :: Parser Ty
parseTy  =
      -- ty ::=

      -- [x:ty] ty
      TyPi <$> (bind
         <$> braces ((,) <$> (string2Name <$> var)
                         <*> (Annot <$> (sym ":" *> parseTy))
                    )
         <*> parseTy)

      -- te -> ty
  <|> try (TyPi <$> (bind
             <$> ((,) (string2Name "_") . Annot <$> parseTyExpr)
             <*> (op "->" *> parseTy)
          ))

      -- te
  <|> parseTyExpr

parseTyExpr :: Parser Ty
  -- te ::= ta [tm ...]
parseTyExpr = foldl TyApp <$> parseTyAtom <*> many parseTm

parseTyAtom :: Parser Ty
parseTyAtom =
      -- ta ::=

      -- (ty)
      parens parseTy

      -- x
  <|> TyConst . string2Name <$> var

