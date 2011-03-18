
----------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib.Bind.LocallyNameless
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  non-portable (-XKitchenSink)
--
-- A generic implementation of name binding functions using a locally
-- nameless representation.  Datatypes with binding can be defined
-- using the 'Name' and 'Bind' types.  Expressive patterns for binding
-- come from the 'Annot' and 'Rebind' types.
--
-- Important classes are:
--
--   * 'Alpha' -- the class of types and patterns that include binders,
--
--   * 'Subst' -- for subtitution functions.
--
-- Name generation is controlled via monads which implement the
-- 'Fresh' and 'LFresh' classes.
----------------------------------------------------------------------

module Generics.RepLib.Bind.LocallyNameless
  ( -- * Basic types
    Name, AnyName(..), Bind, Annot(..), Rebind, Rec, Outer(..),

    -- ** Utilities
    integer2Name, string2Name, s2n, makeName,
    name2Integer, name2String, anyName2Integer, anyName2String,
    name1,name2,name3,name4,name5,name6,name7,name8,name9,name10,
    translate,

    -- * The 'Alpha' class
    Alpha(..),
    swaps, swapsAnnots, swapsBinders,
    match, matchAnnots, matchBinders,
    fv, fvAny, patfv, binders,
    aeq, aeqBinders,
    acompare,

    -- * Binding operations
    bind, unsafeUnbind,

    -- * The 'Fresh' class
    Fresh(..), freshen,
    unbind, unbind2, unbind3,

    FreshM, runFreshM,
    FreshMT, runFreshMT,

    -- * The 'LFresh' class
    LFresh(..),
    lfreshen,
    lunbind, lunbind2, lunbind3,

    LFreshM, runLFreshM, getAvoids,
    LFreshMT, runLFreshMT,

    -- * Rebinding operations
    rebind, unrebind,

    -- * Rec operations
    rec, unrec,

    -- * Substitution
    Subst(..),SubstName(..),

   -- * Advanced
   AlphaCtx, matchR1,

   -- * Pay no attention to the man behind the curtain
   -- $paynoattention
   rName, rBind, rRebind, rAnnot, rRec, rOuter
) where

import Generics.RepLib.Bind.LocallyNameless.Name
import Generics.RepLib.Bind.LocallyNameless.Fresh
import Generics.RepLib.Bind.LocallyNameless.Internal
import Generics.RepLib.Bind.LocallyNameless.Types

-- $paynoattention
-- These type representation objects are exported so they can be
-- referenced by auto-generated code.  Please pretend they do not
-- exist.