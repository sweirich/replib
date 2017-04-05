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
-- for the curious or intrepid.
--
--------------------------------------------------------------------------
module Unbound.Nominal
  ( -- * Names
    Name, AnyName(..),

    -- ** Constructing and destructing free names
    string2Name, s2n,

    -- ** Dealing with name sorts
    toSortedName,

    -- ** Bind
    Bind,

    -- *** Bind constructors
    bind,

    -- *** Bind destructors
    unbind,

    -- ** Embed
    Embed,
    embed, unembed,

    -- ** Rebind
    Rebind,
    rebind, unrebind,

    -- ** Rec
    Rec,
    rec, unrec,

    -- ** Alpha-equivalence
    aeq,

    -- ** Variable calculations
    fv,

    -- | Capture-avoiding substitution
    Subst(..), SubstName(..), subst,

    -- ** Permutations
    Perm,

    -- *** Working with permutations
    single, compose, apply, support, isid, join, empty, restrict, mkPerm,

    -- *** Permuting terms
    swapall,

    -- ** Global freshness
    freshen,

    -- *** The @Fresh@ class
    Fresh(..),

    -- *** The @FreshM@ monad
    FreshM, runFreshM,
    FreshMT, runFreshMT,

    -- * The @Alpha@ class,
    Alpha(..),

    -- * Pay no attention to the man behind the curtain

    -- | These type representation objects are exported so they can be
    --   referenced by auto-generated code.  Please pretend they do not
    --   exist.
    rName, rBind, rRebind, rEmbed, rRec) where

import Unbound.Nominal.Name
import Unbound.Nominal.Alpha
import Unbound.Nominal.Fresh
import Unbound.Nominal.Ops
import Unbound.Nominal.Subst
import Unbound.Nominal.Types
import Unbound.Util
import Unbound.PermM
