{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , OverlappingInstances
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Nominal.LFresh
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  unportable (GHC 7 only)
--
-- The 'Fresh' and 'LFresh' classes, which govern monads with fresh
-- name generation capabilities, and the FreshM(T) and LFreshM(T)
-- monad (transformers) which provide useful default implementations.
----------------------------------------------------------------------

module Unbound.Nominal.LFresh
  ( 
    LFresh(..),

    LFreshM(..), runLFreshM, contLFreshM, getAvoids,
    LFreshMT(..), runLFreshMT, contLFreshMT

  ) where

import Generics.RepLib
import Unbound.Name

import Data.Set (Set)
import qualified Data.Set as S

import Data.Monoid

import Control.Monad.Reader
import qualified Control.Monad.State as St
import Control.Monad.Identity
import Control.Applicative (Applicative)

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Error
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.Writer.Strict as Strict

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.IO.Class as IC

---------------------------------------------------
-- LFresh
---------------------------------------------------

-- | This is the class of monads that support freshness in an
--   (implicit) local scope.  Generated names are fresh for the current
--   local scope, not necessarily globally fresh.
class Monad m => LFresh m where
  -- | Pick a new name that is fresh for the current (implicit) scope.
  lfresh  :: AName a => a -> m a
  -- | Avoid the given names when computing the sub computation
  --   that is, add the given names to the in-scope set.
  push   :: [AnyName] -> m a -> m a
  -- | Remove the most recently added set of names from 
  -- the in-scope set
  pop    :: m a -> m a 
  -- | Is the current name bound ?
  isFree  :: AnyName -> m Bool

-- | The LFresh monad transformer.  Keeps track of a set of names to
-- avoid, and when asked for a fresh one will choose the first numeric
-- prefix of the given name which is currently unused.
newtype LFreshMT m a = LFreshMT { unLFreshMT :: ReaderT ([Set AnyName]) m a }
  deriving (Functor, Applicative, Monad, MonadReader ([Set AnyName]), MonadIO, MonadPlus, MonadFix)

-- | Run an 'LFreshMT' computation in an empty context.
runLFreshMT :: LFreshMT m a -> m a
runLFreshMT m = contLFreshMT m []

-- | Run an 'LFreshMT' computation given a set of names to avoid.
contLFreshMT :: LFreshMT m a -> [Set AnyName] -> m a
contLFreshMT (LFreshMT m) = runReaderT m

-- | Get the set of names currently being avoided.
getAvoids :: Monad m => LFreshMT m ([Set AnyName])
getAvoids = LFreshMT ask

instance Monad m => LFresh (LFreshMT m) where
  lfresh nm = LFreshMT $ do
    let s = name2String nm
    used <- ask
    return $ head (filter (\x -> all (\ y -> not (S.member (AnyName x) y)) used)
                          (map (\j -> renumber j nm) [0..]))
  push names = LFreshMT . local ((:) (S.fromList names)) . unLFreshMT
  pop  = LFreshMT . local tail . unLFreshMT
  isFree n = LFreshMT $ do
    used <- ask
    return $ not (any (S.member n) used)

-- | A convenient monad which is an instance of 'LFresh'.  It keeps
--   track of a set of names to avoid, and when asked for a fresh one
--   will choose the first unused numerical name.
type LFreshM = LFreshMT Identity

-- | Run a LFreshM computation in an empty context.
runLFreshM :: LFreshM a -> a
runLFreshM = runIdentity . runLFreshMT

-- | Run a LFreshM computation given a set of names to avoid.
contLFreshM :: LFreshM a -> [Set AnyName] -> a
contLFreshM m = runIdentity . contLFreshMT m

instance LFresh m => LFresh (ContT r m) where
  lfresh = lift . lfresh
  push  = mapContT . push
  pop  = mapContT pop
  isFree = lift . isFree

instance (Error e, LFresh m) => LFresh (ErrorT e m) where
  lfresh = lift . lfresh
  push  = mapErrorT . push
  pop  = mapErrorT pop
  isFree = lift . isFree

instance LFresh m => LFresh (IdentityT m) where
  lfresh = lift . lfresh
  push  = mapIdentityT . push
  pop  = mapIdentityT pop
  isFree = lift . isFree

instance LFresh m => LFresh (ListT m) where
  lfresh = lift . lfresh
  push  = mapListT . push
  pop  = mapListT pop
  isFree = lift . isFree

instance LFresh m => LFresh (MaybeT m) where
  lfresh = lift . lfresh
  push  = mapMaybeT . push
  pop  = mapMaybeT pop
  isFree = lift . isFree

instance LFresh m => LFresh (ReaderT r m) where
  lfresh = lift . lfresh
  push  = mapReaderT . push
  pop  = mapReaderT pop
  isFree = lift . isFree

instance LFresh m => LFresh (Lazy.StateT s m) where
  lfresh = lift . lfresh
  push  = Lazy.mapStateT . push
  pop  = Lazy.mapStateT pop
  isFree = lift . isFree

instance LFresh m => LFresh (Strict.StateT s m) where
  lfresh = lift . lfresh
  push  = Strict.mapStateT . push
  pop = Strict.mapStateT pop
  isFree = lift . isFree

instance (Monoid w, LFresh m) => LFresh (Lazy.WriterT w m) where
  lfresh = lift . lfresh
  push  = Lazy.mapWriterT . push
  pop = Lazy.mapWriterT pop
  isFree = lift . isFree

instance (Monoid w, LFresh m) => LFresh (Strict.WriterT w m) where
  lfresh = lift . lfresh
  push  = Strict.mapWriterT . push
  pop = Strict.mapWriterT pop
  isFree = lift . isFree

-- Instances for applying LFreshMT to other monads

instance MonadTrans LFreshMT where
  lift = LFreshMT . lift

instance CC.MonadCont m => CC.MonadCont (LFreshMT m) where
  callCC c = LFreshMT $ CC.callCC (unLFreshMT . (\k -> c (LFreshMT . k)))

instance EC.MonadError e m => EC.MonadError e (LFreshMT m) where
  throwError = lift . EC.throwError
  catchError m h = LFreshMT $ EC.catchError (unLFreshMT m) (unLFreshMT . h)

instance StC.MonadState s m => StC.MonadState s (LFreshMT m) where
  get = lift StC.get
  put = lift . StC.put

instance RC.MonadReader r m => RC.MonadReader r (LFreshMT m) where
  ask   = lift RC.ask
  local f = LFreshMT . mapReaderT (RC.local f) . unLFreshMT