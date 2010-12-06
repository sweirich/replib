{-# LANGUAGE PatternGuards
           , MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}
import Control.Applicative
import Control.Monad.Reader

import Control.Monad.Trans.Maybe

import Text.Parsec hiding ((<|>))
import qualified Text.Parsec.Token as P
import Text.Parsec.Language (haskellDef)

import Generics.RepLib.Bind.LocallyNameless
import Generics.RepLib

data Term = Var (Name Term)
          | App Term Term
          | Lam (Bind (Name Term) Term)
  deriving (Show)

$(derive [''Term])

instance Alpha Term
instance Subst Term Term where
  isvar (Var v) = Just (v, id)
  isvar _       = Nothing

isValue (Lam _)   = True
isValue (App _ _) = False

done :: Monad m => MaybeT m a
done = MaybeT $ return Nothing

instance (Functor m, LFresh m) => LFresh (MaybeT m) where
  lfresh    = MaybeT . fmap Just . lfresh
  avoid nms = MaybeT . avoid nms . runMaybeT

step :: (Functor m, LFresh m) => Term -> MaybeT m Term
step (Var _) = done
step (Lam _) = done
step (App (Lam b) t2)
  | isValue t2 = lunbind b $ \(x,t1) ->
                   return (subst x t2 t1)
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
eval x = runReader (tc step x) (0::Integer)

-- Some example terms

nm = string2Name

idT = Lam (bind (nm "y") (Var (nm "y")))

foo = Lam (bind (nm "z") (Var (nm "y")))

trueT  = Lam (bind (nm "x") (Lam (bind (nm "y") (Var (nm "x")))))
-- falseT = Lam (bind (nm "x") (Lam (bind (nm "x") (Var (nm "x")))))
-- above doesn't work like I would expect!

falseT = Lam (bind (nm "x") (Lam (bind (nm "y") (Var (nm "y")))))

-- A small parser for Terms
lexer = P.makeTokenParser haskellDef

parens = P.parens lexer
var    = P.identifier lexer
op     = P.symbol lexer

parseTerm = parens parseTerm
        <|> (Var . string2Name <$> var)
        <|> Lam <$> (bind <$> (op "\\" *> (string2Name <$> var))
                          <*> (op "." *> parseTerm))

{-

*Main> parseTest parseTerm "\\x.\\x.x"
Lam (<x> Lam (<0@0> Var 0@0))

-}
-- The above is not what I would expect!  What am I doing wrong?