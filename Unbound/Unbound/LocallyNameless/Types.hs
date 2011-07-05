{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
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
       ( Bind(..)
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

       , rBind, rRebind, rEmbed, rRec, rShift
       ) where

import Generics.RepLib
import Unbound.LocallyNameless.Name

------------------------------------------------------------
-- Basic types
------------------------------------------------------------

-- Bind
--------------------------------------------------

-- | The most fundamental combinator for expressing binding structure
--   is 'Bind'.  The /term type/ @Bind p t@ represents a pattern @p@
--   paired with a term @t@, where names in @p@ are bound within @t@.
--
--   Like 'Name', 'Bind' is also abstract. You can create bindings
--   using 'bind' and take them apart with 'unbind' and friends.
data Bind p t = B p t

instance (Show a, Show b) => Show (Bind a b) where
  showsPrec p (B a b) = showParen (p>0)
      (showString "<" . showsPrec p a . showString "> " . showsPrec 0 b)

-- XXX todo: make sure everything has write Read and Eq instances?

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
      (showString "<<" . showsPrec p a . showString ">> " . showsPrec 0 b)

-- Rec
--------------------------------------------------

-- | If @p@ is a pattern type, then @Rec p@ is also a pattern type,
-- which is /recursive/ in the sense that @p@ may bind names in terms
-- embedded within itself.  Useful for encoding e.g. lectrec and
-- Agda's dot notation.
data Rec p = Rec p

instance Show a => Show (Rec a) where
  showsPrec _ (Rec a) = showString "[" . showsPrec 0 a . showString "]"

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

-- Shift
--------------------------------------------------

-- | Shift the scope of an embedded term one level outwards.
newtype Shift p = Shift p deriving Eq

instance Show a => Show (Shift a) where
  showsPrec _ (Shift a) = showString "{" . showsPrec 0 a . showString "}"

-- Pay no attention...

$(derive [''Bind, ''Embed, ''Rebind, ''Rec, ''Shift])

