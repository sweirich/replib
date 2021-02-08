{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module Unbound.Nominal.Fresh (
  Fresh(..)

  , FreshM
  , runFreshM

  , FreshMT
  , runFreshMT
) where

import Generics.RepLib
import Unbound.Nominal.Name

import Control.Monad.Reader
import qualified Control.Monad.State as St
import Control.Monad.Identity
import Control.Applicative

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.Writer.Strict as Strict

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.Writer.Class as WC

------------------------------------------
-- Fresh
------------------------------------------

class Monad m => Fresh m where
  -- |Generate a new globally unique name based on the given name.
  fresh :: Rep a => Name a -> m (Name a)

-- |The @FreshM@ monad transformer.
newtype FreshMT m a = FreshMT { unFreshMT :: St.StateT Integer m a }
  deriving (Functor, Applicative, Alternative, Monad, MonadPlus, MonadIO, MonadFix)

runFreshMT :: Monad m => FreshMT m a -> m a
runFreshMT (FreshMT m) = St.evalStateT m 0

runFreshM :: FreshM a -> a
runFreshM = runIdentity . runFreshMT

type FreshM = FreshMT Identity

instance (Monad m) => Fresh (FreshMT m) where
  fresh (Name r (s, _)) = FreshMT $ do
    n <- St.get
    St.put (n+1)
    return $ Name r (s, Just n)

instance Fresh m => Fresh (ContT r m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh

instance Fresh m => Fresh (IdentityT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ListT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (MaybeT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ReaderT r m) where
  fresh = lift . fresh

instance Fresh m => Fresh (Lazy.StateT s m) where
  fresh = lift . fresh

instance Fresh m => Fresh (Strict.StateT s m) where
  fresh = lift . fresh

instance (Monoid w, Fresh m) => Fresh (Lazy.WriterT w m) where
  fresh = lift . fresh

instance (Monoid w, Fresh m) => Fresh (Strict.WriterT w m) where
  fresh = lift . fresh

-- Instances for applying FreshMT to other monads

instance MonadTrans FreshMT where
  lift = FreshMT . lift

instance CC.MonadCont m => CC.MonadCont (FreshMT m) where
  callCC c = FreshMT $ CC.callCC (unFreshMT . (\k -> c (FreshMT . k)))

instance EC.MonadError e m => EC.MonadError e (FreshMT m) where
  throwError = lift . EC.throwError
  catchError m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)

instance StC.MonadState s m => StC.MonadState s (FreshMT m) where
  get = lift StC.get
  put = lift . StC.put

instance RC.MonadReader r m => RC.MonadReader r (FreshMT m) where
  ask   = lift RC.ask
  local f = FreshMT . RC.local f . unFreshMT

instance WC.MonadWriter w m => WC.MonadWriter w (FreshMT m) where
  tell   = lift . WC.tell
  listen = FreshMT . WC.listen . unFreshMT
  pass   = FreshMT . WC.pass . unFreshMT
