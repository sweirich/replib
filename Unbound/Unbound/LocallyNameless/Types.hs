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
       -- $paynoattention
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
--   is 'Bind'.  The type @Bind p t@ represents a pattern @p@ paired
--   with a term @t@, where names in @p@ are bound within @t@.
--
--   Like 'Name', 'Bind' is also abstract. You can create bindings
--   using 'Unbound.LocallyNameless.bind' and take them apart with
--   'unbind' and friends.
data Bind p t = B p t

instance (Show a, Show b) => Show (Bind a b) where
  showsPrec p (B a b) = showParen (p>0)
      (showString "<" . showsPrec p a . showString "> " . showsPrec 0 b)

-- XXX todo: make sure everything has write Read and Eq instances?

-- Rebind
--------------------------------------------------

-- | 'Rebind' supports \"telescopes\" --- that is, patterns where
--   bound variables appear in multiple subterms.
data Rebind p1 p2 = R p1 p2

instance (Show a, Show b) => Show (Rebind a b) where
  showsPrec p (R a b) = showParen (p>0)
      (showString "<<" . showsPrec p a . showString ">> " . showsPrec 0 b)

-- Rec
--------------------------------------------------

-- | 'Rec' supports recursive patterns --- that is, patterns where
-- any variables anywhere in the pattern are bound in the pattern
-- itself.  Useful for lectrec (and Agda's dot notation).
data Rec p = Rec p

instance Show a => Show (Rec a) where
  showsPrec _ (Rec a) = showString "[" . showsPrec 0 a . showString "]"

-- TRec
--------------------------------------------------

-- | 'TRec' is a standalone variant of 'Rec' -- that is, if @p@ is a
--   pattern type then @TRec p@ is a term type.  It is isomorphic to
--   @Bind (Rec p) ()@.

newtype TRec p = TRec (Bind (Rec p) ())

instance Show a => Show (TRec a) where
  showsPrec _ (TRec (B (Rec p) ())) = showString "[" . showsPrec 0 p . showString "]"


-- Embed
--------------------------------------------------

-- XXX improve this doc
-- | An annotation is a \"hole\" in a pattern where variables can be
--   used, but not bound. For example, patterns may include type
--   annotations, and those annotations can reference variables
--   without binding them.  Annotations do nothing special when they
--   appear elsewhere in terms.
newtype Embed t = Embed t deriving Eq

instance Show a => Show (Embed a) where
  showsPrec p (Embed a) = showString "{" . showsPrec 0 a . showString "}"

-- Shift
--------------------------------------------------

-- | Shift the scope of an embedded term one level outwards.
newtype Shift p = Shift p deriving Eq

instance Show a => Show (Shift a) where
  showsPrec p (Shift a) = showString "{" . showsPrec 0 a . showString "}"

-- $paynoattention
-- These type representation objects are exported so they can be
-- referenced by auto-generated code.  Please pretend they do not
-- exist.

$(derive [''Bind, ''Embed, ''Rebind, ''Rec, ''Shift])

