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
-- Module      :  Unbound.Fresh
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

module Unbound.Fresh
  ( -- * The 'Fresh' class

    Fresh(..),

    FreshM(..), runFreshM, contFreshM,
    FreshMT(..), runFreshMT, contFreshMT,

    -- * The 'LFresh' class

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

------------------------------------------------------------
-- Fresh
------------------------------------------------------------

-- | The @Fresh@ type class governs monads which can generate new
--   globally unique 'Name's based on a given 'Name'.
class Monad m => Fresh m where

  -- | Generate a new globally unique name based on the given one.
  fresh :: AName a => a -> m a

-- | The @FreshM@ monad transformer.  Keeps track of the lowest index
--   still globally unused, and increments the index every time it is
--   asked for a fresh name.
newtype FreshMT m a = FreshMT { unFreshMT :: St.StateT Integer m a }
  deriving (Functor, Applicative, Monad, MonadPlus, MonadIO, MonadFix)

-- | Run a 'FreshMT' computation (with the global index starting at zero).
runFreshMT :: Monad m => FreshMT m a -> m a
runFreshMT m = contFreshMT m 0

-- | Run a 'FreshMT' computation given a starting index for fresh name
--   generation.
contFreshMT :: Monad m => FreshMT m a -> Integer -> m a
contFreshMT (FreshMT m) = St.evalStateT m

instance Monad m => Fresh (FreshMT m) where
  fresh nm = FreshMT $ do 
     n <- St.get
     St.put (n+1)
     return $ renumber n nm

-- | A convenient monad which is an instance of 'Fresh'.  It keeps
--   track of a global index used for generating fresh names, which is
--   incremented every time 'fresh' is called.
type FreshM = FreshMT Identity

-- | Run a FreshM computation (with the global index starting at zero).
runFreshM :: FreshM a -> a
runFreshM = runIdentity . runFreshMT

-- | Run a FreshM computation given a starting index.
contFreshM :: FreshM a -> Integer -> a
contFreshM m = runIdentity . contFreshMT m

-- Instances for applying monad transformers to Fresh monads

instance Fresh m => Fresh (ContT r m) where
  fresh = lift . fresh

instance (Error e, Fresh m) => Fresh (ErrorT e m) where
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

---------------------------------------------------
-- LFresh
---------------------------------------------------

-- | This is the class of monads that support freshness in an
--   (implicit) local scope.  Generated names are fresh for the
--   current local scope, not necessarily globally fresh.

class Monad m => LFresh m where
  -- | Pick a new name that is fresh for the current (implicit) scope.
  lfresh  :: AName a => a -> m a

  -- | Avoid the given names when freshening in the subcomputation,
  --   that is, add the given names to the in-scope set.
  avoid   :: [AnyName] -> m a -> m a

  -- | Is the current name currently in the local scope?
  inScope :: AName a => a -> m Bool

  -- | Pop the outermost scope of names
  shift   :: m a -> m a

-- | The LFresh monad transformer.  Keeps track of a set of names to
-- avoid, and when asked for a fresh one will choose the first numeric
-- prefix of the given name which is currently unused.
newtype LFreshMT m a = LFreshMT { unLFreshMT :: ReaderT ([Set AnyName]) m a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadPlus, MonadFix)

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
    used <- ask
    return $ head (filter (\x -> not (any (S.member (AnyName x)) used))
                          (map (\j -> renumber j nm) [0..]))
  avoid names = LFreshMT . local (\ s -> (S.fromList names) : s) . unLFreshMT

  inScope nm = LFreshMT $ do 
       used <- ask     
       return (any (S.member (AnyName nm)) used)

  shift = LFreshMT . local ( \ ( x : s ) -> s ) . unLFreshMT
       
  
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
  avoid  = mapContT . avoid
  inScope = lift . inScope
  shift  = mapContT shift

instance (Error e, LFresh m) => LFresh (ErrorT e m) where
  lfresh = lift . lfresh
  avoid  = mapErrorT . avoid
  inScope = lift . inScope
  shift  = mapErrorT shift

instance LFresh m => LFresh (IdentityT m) where
  lfresh = lift . lfresh
  avoid  = mapIdentityT . avoid
  inScope = lift . inScope
  shift  = mapIdentityT shift

instance LFresh m => LFresh (ListT m) where
  lfresh = lift . lfresh
  avoid  = mapListT . avoid
  inScope = lift . inScope
  shift = mapListT shift

instance LFresh m => LFresh (MaybeT m) where
  lfresh = lift . lfresh
  avoid  = mapMaybeT . avoid
  inScope = lift . inScope
  shift = mapMaybeT shift

instance LFresh m => LFresh (ReaderT r m) where
  lfresh = lift . lfresh
  avoid  = mapReaderT . avoid
  inScope = lift . inScope
  shift = mapReaderT shift 

instance LFresh m => LFresh (Lazy.StateT s m) where
  lfresh = lift . lfresh
  avoid  = Lazy.mapStateT . avoid
  inScope = lift . inScope
  shift = Lazy.mapStateT shift

instance LFresh m => LFresh (Strict.StateT s m) where
  lfresh = lift . lfresh
  avoid  = Strict.mapStateT . avoid
  inScope = lift . inScope
  shift = Strict.mapStateT shift

instance (Monoid w, LFresh m) => LFresh (Lazy.WriterT w m) where
  lfresh = lift . lfresh
  avoid  = Lazy.mapWriterT . avoid
  inScope = lift . inScope
  shift = Lazy.mapWriterT shift

instance (Monoid w, LFresh m) => LFresh (Strict.WriterT w m) where
  lfresh = lift . lfresh
  avoid  = Strict.mapWriterT . avoid
  inScope = lift . inScope
  shift = Strict.mapWriterT shift

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
