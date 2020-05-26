{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , EmptyDataDecls
  #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless.Types
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  GHC only
--
-- Special type combinators for specifying binding structure.
----------------------------------------------------------------------

module Unbound.LocallyNameless.Types
       ( GenBind(..), Bind, SetBind, SetPlusBind
       , Rebind(..)
       , Rec(..)
       , TRec(..)
       , Embed(..)
       , Shift(..)
       , module Unbound.LocallyNameless.Name

       -- * Pay no attention to the man behind the curtain

       -- | These type representation objects are exported so they can be
       --   referenced by auto-generated code.  Please pretend they do not
       --   exist.

       , rGenBind, rRebind, rEmbed, rRec, rShift
       ) where

import Generics.RepLib
import Unbound.LocallyNameless.Name

import Data.Binary
import Control.Applicative (pure, (<$>), (<*>))

import qualified Control.DeepSeq as DS

------------------------------------------------------------
-- Basic types
------------------------------------------------------------
-- Note: can't use DataKinds here because RepLib does not support
-- representations of them.

-- | Type level flag for binder that allows permutation
data RelaxedOrder
-- | Type level flag for binder that does not allow permutation
data StrictOrder

-- | Type level flag for binder that allows extra unused variables
data RelaxedCard
-- | Type level flag for binder that does not allow weakening
data StrictCard

--------------------------------------------------  
-- Bind
--------------------------------------------------

-- | Generic binding combinator for a pattern @p@ within a term @t@.
-- Flexible over the order and cardinality of the variables bound
-- in the pattern
data GenBind order card p t = B p t

  
-- | The most fundamental combinator for expressing binding structure
--   is 'Bind'.  The /term type/ @Bind p t@ represents a pattern @p@
--   paired with a term @t@, where names in @p@ are bound within @t@.
--
--   Like 'Name', 'Bind' is also abstract. You can create bindings
--   using 'bind' and take them apart with 'unbind' and friends.
type Bind p t        = GenBind StrictOrder StrictCard p t



-- | A variant of 'Bind' where alpha-equivalence allows multiple
-- variables bound in the same pattern to be reordered
type SetBind p t     = GenBind RelaxedOrder StrictCard p t
-- | A variant of 'Bind' where alpha-equivalence allows multiple
-- variables bound in the same pattern to be reordered, and
-- allows the binding of unused variables
-- For example,  \{ a b c } . a b `aeq` \ { b a } . a b
type SetPlusBind p t = GenBind RelaxedOrder RelaxedCard p t

instance (Show a, Show b) => Show (GenBind order card a b) where
  showsPrec p (B a b) = showParen (p>0)
      (showString "bind " . showsPrec 11 a . showString " " . showsPrec 11 b)

instance (DS.NFData p, DS.NFData t) => DS.NFData (GenBind order card p t) where
  rnf (B p t) = DS.rnf p `seq` DS.rnf t

--------------------------------------------------
-- Rebind
--------------------------------------------------

-- | @Rebind@ allows for /nested/ bindings.  If @p1@ and @p2@ are
--   pattern types, then @Rebind p1 p2@ is also a pattern type,
--   similar to the pattern type @(p1,p2)@ except that @p1@
--   /scopes over/ @p2@.  That is, names within terms embedded in @p2@
--   may refer to binders in @p1@.
data Rebind p1 p2 = R p1 p2

instance (Show a, Show b) => Show (Rebind a b) where
  showsPrec p (R a b) = showParen (p>0)
      (showString "rebind " . showsPrec 11 a . showsPrec 11 b)

instance (DS.NFData p, DS.NFData t) => DS.NFData (Rebind p t) where
  rnf (R p t) = DS.rnf p `seq` DS.rnf t


-- Rec
--------------------------------------------------

-- | If @p@ is a pattern type, then @Rec p@ is also a pattern type,
-- which is /recursive/ in the sense that @p@ may bind names in terms
-- embedded within itself.  Useful for encoding e.g. lectrec and
-- Agda's dot notation.
data Rec p = Rec p

instance Show a => Show (Rec a) where
  showsPrec _ (Rec a) = showString "[" . showsPrec 0 a . showString "]"

instance (DS.NFData p) => DS.NFData (Rec p) where
  rnf (Rec p) = DS.rnf p


-- TRec
--------------------------------------------------

-- | @TRec@ is a standalone variant of 'Rec': the only difference is
--   that whereas @'Rec' p@ is a pattern type, @TRec p@
--   is a /term type/.  It is isomorphic to @'Bind' ('Rec' p) ()@.
--
--   Note that @TRec@ corresponds to Pottier's /abstraction/ construct
--   from alpha-Caml.  In this context, @'Embed' t@ corresponds to
--   alpha-Caml's @inner t@, and @'Shift' ('Embed' t)@ corresponds to
--   alpha-Caml's @outer t@.
newtype TRec p = TRec (Bind (Rec p) ())

instance Show a => Show (TRec a) where
  showsPrec _ (TRec (B (Rec p) ())) = showString "[" . showsPrec 0 p . showString "]"

instance (DS.NFData p) => DS.NFData (TRec p) where
  rnf (TRec p) = DS.rnf p


-- Embed
--------------------------------------------------

-- | @Embed@ allows for terms to be /embedded/ within patterns.  Such
--   embedded terms do not bind names along with the rest of the
--   pattern.  For examples, see the tutorial or examples directories.
--
--   If @t@ is a /term type/, then @Embed t@ is a /pattern type/.
--
--   @Embed@ is not abstract since it involves no binding, and hence
--   it is safe to manipulate directly.  To create and destruct
--   @Embed@ terms, you may use the @Embed@ constructor directly.
--   (You may also use the functions 'embed' and 'unembed', which
--   additionally can construct or destruct any number of enclosing
--   'Shift's at the same time.)
newtype Embed t = Embed t deriving Eq

instance Show a => Show (Embed a) where
  showsPrec _ (Embed a) = showString "{" . showsPrec 0 a . showString "}"

instance (DS.NFData p) => DS.NFData (Embed p) where
  rnf (Embed p) = DS.rnf p


-- Shift
--------------------------------------------------

-- | Shift the scope of an embedded term one level outwards.
newtype Shift p = Shift p deriving Eq

instance Show a => Show (Shift a) where
  showsPrec _ (Shift a) = showString "{" . showsPrec 0 a . showString "}"

instance (DS.NFData p) => DS.NFData (Shift p) where
  rnf (Shift p) = DS.rnf p


-- Pay no attention...

$(derive [''GenBind, ''Embed, ''Rebind, ''Rec, ''Shift])

$(derive [''RelaxedOrder, ''StrictOrder, ''RelaxedCard, ''StrictCard])


-- Data.Binary instances for Name and Bind
----------------------------------------------------

instance Rep a => Binary (Name a) where
  put (Nm _ s i) = do put (0 :: Word8)
                      put s
                      put i
  put (Bn _ i j)   = do put (1 :: Word8)
                        put i
                        put j
  
  get = do tag <- getWord8
           case tag of
              0 -> Nm <$> pure rep <*> get <*> get
              1 -> Bn <$> pure rep <*> get <*> get

instance (Binary p, Binary t) => Binary (GenBind order card p t) where
  put (B p t) = do put p ; put t
  get = B <$> get <*> get

instance (Binary p1, Binary p2) => Binary (Rebind p1 p2) where
  put (R p1 p2) = do put p1 ; put p2
  get = R <$> get <*> get
  
instance (Binary p) => Binary (Embed p) where
  put (Embed p) = put p
  get = Embed <$> get
