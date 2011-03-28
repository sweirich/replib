----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Nominal
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  non-portable (-XKitchenSink)
--
-- Generic implementation of name binding functions, based on the library
-- RepLib. This version uses a nominal representation of binding structure.
--
-- DISCLAIMER: this module probably contains bugs and may be
-- slower than "Unbound.LocallyNameless".  At this point
-- we recommend it only for the curious or intrepid.
--
-- Datatypes with binding defined using the 'Name' and 'Bind' types.
-- Important classes are
--     'Alpha' -- the class of types that include binders.
-- These classes are generic, and default implementations exist for all
-- representable types. This file also defines a third generic class,
--     'Subst' -- for subtitution functions.
--
--------------------------------------------------------------------------
module Unbound.Nominal
  (-- * Basic types
    Name,  AnyName(..), Bind, Embed(..), Rebind, Rec, Shift,

    -- ** Utilities
    integer2Name, string2Name, name2Integer, name2String, makeName,
    name1,name2,name3,name4,name5,name6,name7,name8,name9,name10,
    translate,

    -- * The 'Alpha' class
    Alpha(..),
    swaps, -- is a bit wonky
    match,
    binders, patfv, fv,
    aeq,

    -- * Binding operations
    bind, unsafeUnbind,

    -- * The 'Fresh' class
    Fresh(..), freshen,
    unbind, unbind2, unbind3,

    -- * The 'LFresh' class
    HasNext(..), LFresh(..),
    lfreshen,
    lunbind, lunbind2, lunbind3,

    -- * Rebinding operations
    rebind, reopen,

    -- * Rec operations
    rec, unrec,

    -- * Substitution
    Subst(..),

   -- * Advanced
   AlphaCtx, matchR1,

   -- * Pay no attention to the man behind the curtain

   -- | These type representation objects are exported so they can be
   --   referenced by auto-generated code.  Please pretend they do not
   --   exist.
   rName, rBind, rRebind, rEmbed, rRec, rShift) where

import Unbound.Nominal.Name
import Unbound.Nominal.Internal
