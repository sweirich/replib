
----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  GHC only (-XKitchenSink)
--
-- A generic implementation of standard functions dealing with names
-- and binding structure (alpha equivalence, free variable
-- calculation, capture-avoiding substitution, name permutation, ...)
-- using a locally nameless representation. (See "Unbound.Nominal" for
-- a nominal implementation of the same interface.)
--
-- Ten-second tutorial: use the type combinators 'Bind', 'Embed',
-- 'Rebind', 'Rec', 'TRec', and 'Shift' to specify the binding
-- structure of your data types.  Then use Template Haskell to derive
-- generic representations for your types:
--
-- > $(derive [''Your, ''Types, ''Here])
--
-- Finally, declare 'Alpha' and 'Subst' instances for your types.
-- Then you can go to town using all the generically-derived
-- operations like 'aeq', 'fv', 'subst', and so on.
--
-- For more information, see the more in-depth literate Haskell
-- tutorial in the @tutorial@ directory (which can be obtained as part
-- of the library source package: @cabal unpack unbound@).
--
-- See also: Stephanie Weirich, Brent Yorgey, and Tim Sheard.
-- /Binders Unbound/. Submitted to ICFP
-- 2011. <http://www.cis.upenn.edu/~byorgey/papers/binders-unbound.pdf>.
----------------------------------------------------------------------

module Unbound.LocallyNameless
  ( -- * Names
    Name, AnyName(..),

    integer2Name, string2Name, s2n, makeName,
    name2Integer, name2String, anyName2Integer, anyName2String,
    translate,

    -- * Type combinators for specifying binding structure
    Bind, Embed(..), Rebind, Rec, TRec, Shift(..),

    -- * The 'Alpha' class
    Alpha(..),
    swaps, swapsEmbeds, swapsBinders,
    aeq, aeqBinders,
    acompare,

    -- * Variable calculations
    Collection(..), Multiset(..),
    fv, fvAny, patfv, patfvAny, binders, bindersAny,

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
    trec, untrec, luntrec,

    -- XXX export embed, unembed, shift, unshift.
    -- XXX should embed/unembed work for Shifts as well?

    -- * Substitution
    Subst(..), SubstName(..),

    -- * Pay no attention to the man behind the curtain
    -- $paynoattention
    rName, rBind, rRebind, rEmbed, rRec, rShift
) where

import Unbound.LocallyNameless.Name
import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Subst
import Unbound.LocallyNameless.Ops
import Unbound.Util

-- $paynoattention
-- These type representation objects are exported so they can be
-- referenced by auto-generated code.  Please pretend they do not
-- exist.