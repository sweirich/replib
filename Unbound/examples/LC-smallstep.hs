-- Untyped lambda calculus, with small-step evaluation and an example parser

{-# LANGUAGE PatternGuards
           , MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}
import Control.Applicative
import Control.Arrow
import Control.Monad

import Control.Monad.Trans.Maybe

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

data Term = Var (Name Term)
          | App Term Term
          | Lam (Bind (Name Term) Term)
  deriving Show

$(derive [''Term])

instance Alpha Term
instance Subst Term Term where
  isvar (Var v) = Just (SubstName v)
  isvar _       = Nothing

done :: MonadPlus m => m a
done = mzero

step :: Term -> MaybeT FreshM Term
step (Var _) = done
step (Lam _) = done
step (App (Lam b) t2) = do
  (x,t1) <- unbind b
  return $ subst x t2 t1
step (App t1 t2) =
      App <$> step t1 <*> pure t2
  <|> App <$> pure t1 <*> step t2

tc :: Monad m => (a -> MaybeT m a) -> (a -> m a)
tc f a = do
  ma' <- runMaybeT (f a)
  case ma' of
    Just a' -> tc f a'
    Nothing -> return a

eval :: Term -> Term
eval x = runFreshM (tc step x)

-- Some example terms

lam :: String -> Term -> Term
lam x t = Lam $ bind (string2Name x) t

var :: String -> Term
var = Var . string2Name

idT = lam "y" (var "y")

foo = lam "z" (var "y")

trueT  = lam "x" (lam "y" (var "x"))
falseT = lam "x" (lam "x" (var "x"))

-- A small parser for Terms
lexer = P.makeTokenParser haskellDef
parens   = P.parens lexer
brackets = P.brackets lexer
ident    = P.identifier lexer

parseTerm = parseAtom `chainl1` (pure App)

parseAtom = parens parseTerm
        <|> var <$> ident
        <|> lam <$> (brackets ident) <*> parseTerm

runTerm :: String -> Either ParseError Term
runTerm = (id +++ eval) . parse parseTerm ""

{- example, 2 + 3 = 5:

    *Main> runTerm "([m][n][s][z] m s (n s z)) ([s] [z] s (s z)) ([s][z] s (s (s z))) s z"
    Right (App (Var s) (App (Var s) (App (Var s) (App (Var s) (App (Var s) (Var z))))))

-}