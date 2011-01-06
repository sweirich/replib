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
           , NoMonomorphismRestriction
  #-}

{- TODO:
   1. [X] write term pretty-printer
   2. [ ] update TcM to track context information to make better error messages?
   3. [ ] track down bugs checking gen100.elf
   4. [ ] tune for speed?
-}

module Main where

import Prelude hiding (lookup)

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)
import Text.Parsec.String
import qualified Text.Parsec.Expr as PE

import Text.PrettyPrint (Doc, (<+>), (<>), colon, text, render, empty, integer, nest, vcat, ($+$))
import qualified Text.PrettyPrint as PP

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Identity
import Control.Applicative hiding (many)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (sortBy, groupBy)
import Data.Function (on)
import Data.Ord (comparing)

import System.Environment

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
--   * a term constant declaration (with optional type and definition), or
--   * a fixity/precedence declaration.
data Decl = DeclTy (Name Ty) Kind
          | DeclTm (Name Tm) (Maybe Ty) (Maybe Tm)
          | DeclInfix Op
  deriving Show

data Op = Op Assoc Integer (Name Tm)
  deriving Show

data Assoc = L | R
  deriving Show

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

lookupTm :: Name Tm -> TcM (Context tm ty) tm
lookupTm x = ask >>= \(C tm _) -> embedMaybe ("Not in scope: term variable " ++ show x)
                                  (M.lookup x tm)

lookupTy :: Name Ty -> TcM (Context tm ty) ty
lookupTy x = ask >>= \(C _ ty) -> embedMaybe ("Not in scope: type constant " ++ show x)
                                  (M.lookup x ty)

embedMaybe :: String -> Maybe a -> TcM ctx a
embedMaybe errMsg m = case m of
  Just a  -> return a
  Nothing -> err errMsg

addTrace :: String -> TcM ctx String
addTrace msg = do
  chks  <- getChkContext
  trace <- vcat <$> mapM ppr chks
  return . PP.render $ text msg $+$ trace

embedEither :: (MonadError String m) => Either String a -> m a
embedEither = either throwError return

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

-----------------------
-- Error reporting ----
-----------------------

-- Keep track of what we're in the middle of checking.
data Check = TyCheck Tm
           | KCheck Ty
           | SCheck Kind
           | TmEq Tm Tm STy
           | TyEq Ty Ty SKind
           | KEq Kind Kind
           | DeclCheck Decl

------------------------------
-- Typechecking monad --------
------------------------------

newtype TcM ctx a = TcM { unTcM :: ErrorT String (ReaderT ctx (ReaderT [Check] FreshM)) a }
  deriving (Functor, Applicative, Monad, MonadReader ctx, MonadPlus, MonadError String, LFresh)

getTcMAvoids :: TcM ctx (S.Set AnyName)
getTcMAvoids = TcM . lift . lift . lift $ getAvoids

getChkContext :: TcM ctx [Check]
getChkContext = TcM . lift . lift $ ask

-- | Continue a TcM computation, given a binding context, a checking
--   context, and a set of names to avoid.
contTcM :: TcM ctx a -> ctx -> [Check] -> S.Set AnyName -> Either String a
contTcM (TcM m) c chks nms = flip contFreshM nms . flip runReaderT chks . flip runReaderT c . runErrorT $ m

-- | Run a TcM computation in an empty context.
runTcM :: TcM (Context tm ty) a -> Either String a
runTcM m = contTcM m emptyCtx [] S.empty

-- | Run a subcomputation with an erased context.
withErasedCtx :: TcM SCtx a -> TcM Ctx a
withErasedCtx m = do
  c <- ask
  chks <- getChkContext
  nms <- getTcMAvoids
  embedEither $ contTcM m (erase c) chks nms

-- | Run a subcomputation with another check pushed on the checking
--   context stack.
whileChecking :: Check -> TcM ctx a -> TcM ctx a
whileChecking chk m = do
  c <- ask
  chks <- getChkContext
  nms <- getTcMAvoids
  embedEither $ contTcM m c (chk:chks) nms

ensure errMsg b = if b then return () else err errMsg

err msg = addTrace msg >>= throwError

matchErr :: Show a => a -> a -> String
matchErr x y = "Cannot match " ++ show x ++ " with " ++ show y

unTyPi (TyPi bnd) = return bnd
unTyPi t = err $ "Expected pi type, got " ++ show t ++ " instead"

unKPi (KPi bnd) = return bnd
unKPi t = err $ "Expected pi kind, got " ++ show t ++ " instead"

isType Type = return ()
isType t = err $ "Expected Type, got " ++ show t ++ " instead"

------------------------------
-- Weak head reduction -------
------------------------------

-- TODO: move these to replib
-- instance (Functor m, LFresh m) => LFresh (MaybeT m) where
--   lfresh    = MaybeT . fmap Just . lfresh
--   avoid nms = MaybeT . avoid nms . runMaybeT

instance (Functor m, LFresh m, Error e) => LFresh (ErrorT e m) where
  lfresh    = ErrorT . fmap Right . lfresh
  avoid nms = ErrorT . avoid nms . runErrorT

instance LFresh m => LFresh (ReaderT e m) where
  lfresh    = ReaderT . const . lfresh
  avoid nms = ReaderT . fmap (avoid nms) . runReaderT

-- Reduce a term to weak-head normal form, or return it unchanged if
-- it is not head-reducible.  Works in erased or unerased contexts.
whr :: Tm -> TcM (Context (t, Maybe Tm) ty) Tm
whr (TmVar a) = (do
  (_, Just defn) <- lookupTm a
  whr defn)
  `mplus`
  return (TmVar a)

whr (TmApp (Lam b) m1) =
  lunbind b $ \((x,_),m2) ->
    whr $ subst x m1 m2

whr (TmApp m1 m2) = do
  m1' <- whr m1
  case m1' of
    Lam _ -> whr (TmApp m1' m2)
    _     -> return $ TmApp m1' m2

whr t = return t

------------------------------
-- Term equality -------------
------------------------------

-- Type-directed term equality.  In context Delta, is M <==> N at
-- simple type tau?
tmEq :: Tm -> Tm -> STy -> TcM SCtx ()
tmEq m n t = whileChecking (TmEq m n t) $ tmEqWhr m n t

tmEqWhr :: Tm -> Tm -> STy -> TcM SCtx ()
tmEqWhr m n t = do
  m' <- whr m
  n' <- whr n
  whileChecking (TmEq m' n' t) $ tmEq' m' n' t -- XXX

  -- XXX todo: might be nice to have 'lfresh' and 'lfreshen', the
  -- first NOT taking an argument

  -- XXX todo: need nicer way of doing "string2Name"
-- Type-directed term equality on terms in WHNF
tmEq' :: Tm -> Tm -> STy -> TcM SCtx ()
tmEq' m n (STyArr t1 t2) = do
  x <- lfresh (string2Name "_x")
  withTmBinding x t1 $
    tmEq (TmApp m (TmVar x)) (TmApp n (TmVar x)) t2
tmEq' m n a@(STyConst {}) = do
  a' <- tmEqS m n
  ensure (matchErr a a') $ a == a'

-- Structural term equality.  Check whether two terms in WHNF are
-- structurally equal, and return their "approximate type" if so.
tmEqS :: Tm -> Tm -> TcM SCtx STy

tmEqS (TmVar a) (TmVar b) = do
  ensure (matchErr a b) $ a == b
  (tyA,_) <- lookupTm a  -- XXX
  return tyA

tmEqS (TmApp m1 m2) (TmApp n1 n2) = do
  ty <- tmEqS m1 n1
  case ty of
    STyArr t2 t1 -> do
      tmEq m2 n2 t2
      return t1
    _            -> do
      ty' <- ppr ty
      err $
        "Left-hand side of an application has type " ++ render ty' ++ "; expecting an arrow type"

tmEqS t1 t2 = err "Term mismatch"

------------------------------
-- Type equality -------------
------------------------------

-- Kind-directed type equality.
tyEq :: Ty -> Ty -> SKind -> TcM SCtx ()
tyEq ty1 ty2 k = whileChecking (TyEq ty1 ty2 k) $ tyEq' ty1 ty2 k

tyEq' (TyPi bnd1) (TyPi bnd2) SKType =  -- XXX
  lunbind2 bnd1 bnd2 $ \(Just ((x, Annot a1), a2, (_, Annot b1), b2)) -> do
    tyEq a1 b1 SKType
    withTmBinding x (erase a1) $ tyEq a2 b2 SKType

tyEq' a b SKType = do
  t <- tyEqS a b
  ensure (matchErr t SKType) $ t == SKType

tyEq' a b (SKArr t k) = do
  x <- lfresh (string2Name "_x")
  withTmBinding x t $ tyEq (TyApp a (TmVar x)) (TyApp b (TmVar x)) k

-- Structural type equality.
tyEqS :: Ty -> Ty -> TcM SCtx SKind
tyEqS (TyConst a) (TyConst b) = do
  ensure (matchErr a b) $ a == b
  lookupTy a

tyEqS (TyApp a m) (TyApp b n) = do
  SKArr t k <- tyEqS a b  -- XXX
  tmEq m n t
  return k

tyEqS t1 t2 = err $ "Types are not equal: " ++ show t1 ++ ", " ++ show t2

------------------------------
-- Kind equality -------------
------------------------------

-- Algorithmic kind equality.
kEq :: Kind -> Kind -> TcM SCtx ()

kEq Type Type = return ()

kEq k1@(KPi bnd1) k2@(KPi bnd2) = whileChecking (KEq k1 k2) $
  lunbind bnd1 $ \((x, Annot a), k) ->
  lunbind bnd2 $ \((_, Annot b), l) -> do
    tyEq a b SKType
    withTmBinding x (erase a) $ kEq k l

kEq k1 k2 = err $ "Kinds are not equal: " ++ show k1 ++ ", " ++ show k2

------------------------------
-- Type checking -------------
------------------------------

-- Compute the type of a term.
tyCheck :: Tm -> TcM Ctx Ty
tyCheck tm = whileChecking (TyCheck tm) $ tyCheck' tm

tyCheck' :: Tm -> TcM Ctx Ty
tyCheck' t@(TmVar x)     = liftM fst $ lookupTm x
tyCheck' t@(TmApp m1 m2) = do
  bnd <- unTyPi =<< tyCheck m1
  a2  <- tyCheck m2
  lunbind bnd $ \((x, Annot a2'), a1) -> do
    withErasedCtx $ tyEq a2' a2 SKType
    return $ subst x m2 a1
tyCheck' t@(Lam bnd) =
  lunbind bnd $ \((x, Annot a1), m2) -> do
    isType =<< kCheck a1
    a2   <- withTmBinding x a1 $ tyCheck m2
    return $ TyPi (bind (x, Annot a1) a2)

-- Compute the kind of a type.
kCheck :: Ty -> TcM Ctx Kind
kCheck ty = whileChecking (KCheck ty) $ kCheck' ty

kCheck' :: Ty -> TcM Ctx Kind
kCheck' (TyConst a) = lookupTy a
kCheck' (TyApp a m) = do
  bnd <- unKPi =<< kCheck a
  b   <- tyCheck m
  lunbind bnd $ \((x, Annot b'), k) -> do
    withErasedCtx $ tyEq b' b SKType
    return $ subst x m k
kCheck' (TyPi bnd) =
  lunbind bnd $ \((x, Annot a1), a2) -> do
    isType =<< kCheck a1
    isType =<< (withTmBinding x a1 $ kCheck a2)
    return Type

-- Check the validity of a kind.
sortCheck :: Kind -> TcM Ctx ()
sortCheck k = whileChecking (SCheck k) $ sortCheck' k

sortCheck' :: Kind -> TcM Ctx ()
sortCheck' Type      = return ()
sortCheck' (KPi bnd) =
  lunbind bnd $ \((x, Annot a), k) -> do
    isType =<< kCheck a
    withTmBinding x a $ sortCheck k

------------------------------------------------------------
--  Parser  ------------------------------------------------
------------------------------------------------------------

type OpList = [Op]

mkOp :: Op -> PE.Operator String OpList Identity Tm
mkOp (Op a _ nm) = PE.Infix (TmApp . TmApp (TmVar nm) <$ sym (name2String nm))
                            (assoc a)
  where assoc L = PE.AssocLeft
        assoc R = PE.AssocRight

mkOpTable :: OpList -> PE.OperatorTable String OpList Identity Tm
mkOpTable = map (map mkOp) . groupBy ((==) `on` prec) . sortBy (flip $ comparing prec)
  where prec (Op _ n _) = n

type LFParser = Parsec String OpList

lfParseTest :: Show a => LFParser a -> String -> IO ()
lfParseTest p = print . runParser p [] ""

------------------------------
-- Lexing --------------------
------------------------------

startStuff = letter   <|> oneOf "!#$%&*+/<=>?@\\^|-~"
endStuff   = alphaNum <|> oneOf "!#$%&*+/<=>?@\\^|-~"

reservedNames = ["type", "infix", "right", "left"]
             ++ [":", "=", ".", "->", "%", "{", "}", "(", ")"]


langDef = haskellDef { P.reservedNames   = reservedNames
                     , P.reservedOpNames = reservedNames
                     , P.identStart      = startStuff
                     , P.identLetter     = endStuff
                     , P.opStart         = startStuff
                     , P.opLetter        = endStuff
                     }

lexer    = P.makeTokenParser langDef

parens   = P.parens     lexer
braces   = P.braces     lexer
brackets = P.brackets   lexer
sym      = P.symbol     lexer
op       = P.reservedOp lexer
reserved = P.reserved   lexer
natural  = P.natural    lexer

var      = string2Name <$> P.identifier lexer

------------------------------
-- Terms ---------------------
------------------------------

parseTm :: LFParser Tm
parseTm = parseTmExpr `chainl1` (pure TmApp)

parseTmExpr :: LFParser Tm
parseTmExpr = do
  ops <- getState
  PE.buildExpressionParser (mkOpTable ops) parseAtom

parseAtom :: LFParser Tm
parseAtom = parens parseTm
        <|> TmVar <$> var
        <|> Lam <$> (
              bind
                <$> brackets ((,) <$> var
                                  <*> (Annot <$> (sym ":" *> parseTy))
                             )
                <*> parseTm
              )

------------------------------
-- Types ---------------------
------------------------------

parseTy :: LFParser Ty
parseTy  =
      -- ty ::=

      -- [x:ty] ty
      TyPi <$> (bind
         <$> braces ((,) <$> var
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

parseTyExpr :: LFParser Ty
  -- te ::= ta [tm ...]
parseTyExpr = foldl TyApp <$> parseTyAtom <*> many parseTm

parseTyAtom :: LFParser Ty
parseTyAtom =
      -- ta ::=

      -- (ty)
      parens parseTy

      -- x
  <|> TyConst <$> var

------------------------------
-- Kinds ---------------------
------------------------------

parseKind :: LFParser Kind
parseKind =
      -- k ::=

      -- {x:ty} k
      KPi <$> (bind
       <$> braces ((,) <$> var
                       <*> (Annot <$> (sym ":" *> parseTy))
                  )
       <*> parseKind)

      -- ka -> k
  <|> try (KPi <$> (bind
             <$> ((,) (string2Name "_") . Annot <$> parseTyExpr)
             <*> (op "->" *> parseKind)
          ))

      -- ka
  <|> parseKindAtom

parseKindAtom :: LFParser Kind
parseKindAtom =
      -- ka ::=

      -- (k)
      parens parseKind

      -- Type
  <|> try (Type <$ reserved "type")

------------------------------
-- Declarations --------------
------------------------------

parseDecl :: LFParser Decl
parseDecl = declBody <* sym "."
 where
  declBody =
        DeclInfix <$> (Op <$> (sym "%" *> reserved "infix" *> rl)
                          <*> natural
                          <*> var)

    <|> try (DeclTy <$> var
                    <*> (sym ":" *> parseKind))

    <|> try (DeclTm <$> var
                    <*> (sym ":" *> (Just <$> parseTy))
                    <*> optionMaybe (sym "=" *> parseTm))

    <|>      DeclTm <$> var
                    <*> pure Nothing
                    <*> (sym "=" *> (Just <$> parseTm))
  rl = (L <$ reserved "left") <|> (R <$ reserved "right")

------------------------------
-- Programs ------------------
------------------------------

parseProg :: LFParser Prog
parseProg =
      -- stop at eof
      [] <$ eof

  <|> do d <- parseDecl  -- parse a single decl
         case d of       -- add fixity declarations to the state
           DeclInfix op -> modifyState (op:)
           _ -> return ()

         (d:) <$> parseProg  -- parse the rest of the program

----------------------------------------
-- Pretty-printing ---------------------
----------------------------------------

class Pretty p where
  ppr :: (LFresh m, Functor m) => p -> m Doc

instance Pretty (Name a) where
  ppr = return . text . show

dot = text "."

instance Pretty Decl where
  ppr (DeclTy t k) = do
    t' <- ppr t
    k' <- ppr k
    return $ t' <+> colon <+> k' <> dot
  ppr (DeclTm x mty mdef) = do
    x'   <- ppr x
    tyf  <- case mty of
              Nothing -> return id
              Just ty -> do ty' <- ppr ty
                            return (<+> (colon <+> ty'))
    deff <- case mdef of
              Nothing -> return id
              Just def -> do def' <- ppr def
                             return (<+> (text "=" <+> def'))
    return $ (deff . tyf $ x') <> dot
  ppr (DeclInfix op) = do
    op' <- ppr op
    return $ op' <> dot

instance Pretty Op where
  ppr (Op assoc prec op) = do
    op' <- ppr op
    return $
      text "%infix"
        <+> text (case assoc of L -> "left"; R -> "right")
        <+> integer prec
        <+> op'

instance Pretty Kind where
  ppr Type = return $ text "type"
  ppr (KPi bnd) = lunbind bnd $ \((x, Annot ty), k) -> do
    x'  <- ppr x
    ty' <- ppr ty
    k'  <- ppr k
    if x `S.member` fv k
      then return $ PP.braces (x' <> colon <> ty') <+> k'
      else return $ PP.parens ty' <+> text "->" <+> k'

instance Pretty Ty where
  ppr (TyApp ty tm) = do
    ty' <- ppr ty
    tm' <- ppr tm
    return $ ty' <+> PP.parens tm'
  ppr (TyConst c) = ppr c
  ppr (TyPi bnd) = lunbind bnd $ \((x, Annot ty1), ty2) -> do
    x' <- ppr x
    ty1' <- ppr ty1
    ty2' <- ppr ty2
    if x `S.member` fv ty2
      then return $ PP.braces (x' <> colon <> ty1') <+> ty2'
      else return $ PP.parens ty1' <+> text "->" <+> ty2'

instance Pretty STy where
  ppr sty = ppr (uneraseTy sty)

uneraseTy (STyConst c) = TyConst c
uneraseTy (STyArr t1 t2) = TyPi (bind (string2Name "_", Annot (uneraseTy t1)) (uneraseTy t2))

uneraseK SKType = Type
uneraseK (SKArr sty sk) = KPi (bind (string2Name "_", Annot (uneraseTy sty)) (uneraseK sk))

instance Pretty SKind where
  ppr sk = ppr (uneraseK sk)

instance Pretty Tm where
  ppr (TmVar x) = ppr x
  ppr (TmApp tm1 tm2) = do
    tm1' <- ppr tm1
    tm2' <- ppr tm2
    return $ tm1' <+> PP.parens tm2'
  ppr (Lam bnd) = lunbind bnd $ \((x, Annot ty), tm) -> do
    x' <- ppr x
    ty' <- ppr ty
    tm' <- ppr tm
    return $ PP.brackets (x' <> colon <> ty') <+> tm'

instance Pretty Check where
  ppr (TyCheck tm) =
    (text "While checking the type of:" <+>) <$> ppr tm
  ppr (KCheck ty) =
    (text "While checking the kind of:" <+>) <$> ppr ty
  ppr (SCheck k) =
    (text "While checking the sort of:" <+>) <$> ppr k
  ppr (TmEq m n ty) = do
    m' <- ppr m
    n' <- ppr n
    ty' <- ppr ty
    return $  text "While checking that terms:"
          $+$ nest 4 (m' $+$ n')
          $+$ nest 2 (text "are equal at type")
          $+$ nest 4 ty'
  ppr (TyEq t1 t2 k) = do
    t1' <- ppr t1
    t2' <- ppr t2
    k'  <- ppr k
    return $  text "While checking that types:"
          $+$ nest 4 (t1' $+$ t2')
          $+$ nest 2 (text "are equal at kind")
          $+$ nest 4 k'
  ppr (KEq k1 k2) = do
    k1' <- ppr k1
    k2' <- ppr k2
    return $ text "While checking equality of kinds:"
          $+$ nest 4 (k1' $+$ k2')
  ppr (DeclCheck decl) = do
    d' <- ppr decl
    return $ text "While checking the declaration:" $+$ nest 4 d'

------------------------------
-- Typechecking programs -----
------------------------------

checkProg :: Prog -> TcM Ctx ()
checkProg [] = return ()
checkProg (DeclInfix _ : ds) = checkProg ds
checkProg (d@(DeclTy nm k) : ds) = do
  whileChecking (DeclCheck d) $ sortCheck k
  withTyBinding nm k $ checkProg ds
checkProg ((DeclTm nm Nothing Nothing):_) = do
  throwError $ "Term " ++ show nm
    ++ " has no type or definition! (This shouldn't happen.)"
checkProg (d@(DeclTm nm (Just ty) Nothing) : ds) = do
  whileChecking (DeclCheck d) $ isType =<< kCheck ty
  withTmBinding nm ty $ checkProg ds
checkProg (d@(DeclTm nm Nothing (Just def)) : ds) = do
  ty <- whileChecking (DeclCheck d) $ tyCheck def
  withTmDefn nm (ty, Just def) $ checkProg ds
checkProg (d@(DeclTm nm (Just ty) (Just def)) : ds) = do
  whileChecking (DeclCheck d) $ do
    isType =<< kCheck ty
    ty'  <- tyCheck def
    withErasedCtx $ tyEq ty ty' SKType
  withTmDefn nm (ty, Just def) $ checkProg ds

checkLF :: [FilePath] -> IO ()
checkLF fileNames = do
  files <- mapM readFile fileNames
  case runParser parseProg [] "" (concat files) of
    Left err   -> print err
    Right prog -> do
      -- putStrLn . unlines . map render . runFreshM . mapM ppr $ prog
      putStrLn . either ("Error: "++) (const "OK!") . runTcM . checkProg $ prog

main = do
  fileNames <- getArgs
  checkLF fileNames