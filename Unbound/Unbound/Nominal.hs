----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Nominal
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  non-portable (-XKitchenSink)
--
-- A generic implementation of standard functions dealing with names
-- and binding structure (alpha equivalence, free variable
-- calculation, capture-avoiding substitution, name permutation, ...)
-- using a nominal representation.
--
-- DISCLAIMER: this module almost certainly contains bugs and may be
-- slower than "Unbound.LocallyNameless".  The documentation is also
-- sparse and likely out of date.  At this point we recommend it only
-- for the curious or intrepid.  We are actively working on bringing
-- it up to speed as a viable alternative to
-- "Unbound.LocallyNameless".
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
