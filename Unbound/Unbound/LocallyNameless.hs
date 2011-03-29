
----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless
-- License     :  BSD-like (see LICENSE)
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
-- Normal users of this library should only need to import this module
-- (or "Unbound.Nominal").  In particular, this module is careful to
-- export only an abstract interface with various safety guarantees.
-- Power users who wish to have access to the internals of the library
-- (at the risk of shooting oneself in the foot) can directly import
-- the various implementation modules such as
-- "Unbound.LocallyNameless.Name" and so on.
--
-- /Ten-second tutorial/: use the type combinators 'Bind', 'Embed',
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
-- of the library source package: @cabal unpack unbound@) and the
-- examples in the @example@ directory.
--
-- See also: Stephanie Weirich, Brent Yorgey, and Tim Sheard.
-- /Binders Unbound/. Submitted, March 2011. <http://www.cis.upenn.edu/~byorgey/papers/binders-unbound.pdf>.
----------------------------------------------------------------------

module Unbound.LocallyNameless
  ( -- * Names
    Name, AnyName(..),

    -- ** Constructing and destructing free names
    integer2Name, string2Name, s2n, makeName,
    name2Integer, name2String, anyName2Integer, anyName2String,
    -- ** Dealing with name sorts
    translate, toSortedName,

    -- * Type combinators for specifying binding structure
    --
    -- | 'Bind', 'Embed', 'Rebind', 'Rec', 'TRec', and 'Shift' are
    --   special types provided by Unbound for use in specifying the
    --   binding structure of your data types.
    --
    --   An important distinction to keep in mind is the difference
    --   between /term types/ and /pattern types/.
    --
    --   * /Term types/ are normal types whose values represent data in
    --     your program.  Any 'Name's occurring in term types are
    --     either free variables, or /references/ to binders.
    --
    --   * /Pattern types/ are types which may be used on the left
    --     hand side of a 'Bind'.  They /bind/ names, that is, any
    --     'Name's occurring in pattern types are /binding sites/ to
    --     which other names may refer.
    --
    --   'Name' may be used as both a term type (where it represents a
    --   free variable/reference) and a pattern type (where it
    --   represents a binding site).
    --
    --   Any first-order algebraic data type (/i.e./ one containing no
    --   functions) which contains only term types may be used as a
    --   term type, and likewise for algebraic data types containing
    --   only pattern types. For example,
    --
    --   > (Name, [Name])
    --
    --   may be used as either a term type or a pattern type. On the
    --   other hand,
    --
    --   > (Bind Name Name, Name)
    --
    --   may only be used as a term type, since @Bind Name Name@ is a
    --   term type and not a pattern type.
    --
    --   We adopt the convention that the type variable @t@ stands for
    --   term types, and the type variable @p@ stands for pattern
    --   types.  It would be nicer if we could actually use Haskell's
    --   type system to enforce the distinction, but for various
    --   technical reasons (involving the RepLib generic programming
    --   framework which is used in the implementation), we cannot.
    --   Or at least, we are not sufficiently clever to see how.

    -- ** Bind

    Bind,

    -- *** Bind constructor
    bind,

    -- *** Bind destructors

    -- | Directly pattern-matching on 'Bind' values is not allowed,
    --   but there are quite a few different ways to safely \"open\" a
    --   binding.  (If you want direct, unsafe access to the
    --   components of a binding --- e.g. to write a function to
    --   compute the size of terms that ignores all names --- you can
    --   directly import "Unbound.LocallyNameless.Ops" and use the
    --   'unsafeUnbind' function.)
    unbind,
    lunbind,

    -- *** Simultaneous unbinding

    -- | Sometimes one may wish to open several bindings using /same/
    --   names for their binding variables --- for example, when
    --   checking equality of terms involving binders, so that the
    --   free variables in the bodies will match appropriately during
    --   recursive calls.  Opening two bindings simultaneously is
    --   accomplished with 'unbind2' (which picks globally fresh
    --   names) and 'lunbind2' (which picks /locally/ fresh names, see
    --   the 'LFresh' documentation for more information).  'unbind3'
    --   and 'lunbind3' open three bindings simultaneously.  In
    --   principle, of course, @unbindN@ and @lunbindN@ can be easily
    --   implemented for any @N@; please let the maintainers know if
    --   for some reason you would like an N > 3.
    unbind2, unbind3,
    lunbind2, lunbind3,

    -- ** Embed

    Embed(..),

    embed, unembed,

    -- ** Rebind

    Rebind,

    rebind, unrebind,

    -- ** Rec
    Rec,
    rec, unrec,

    -- ** TRec
    TRec,
    trec, untrec, luntrec,

    -- ** Shift
    Shift(..),

    -- * Generically derived operations

    -- | This section lists a number of operations which are derived
    --   generically for any types whose binding structure is
    --   specified via the type combinators described in the previous
    --   section.

    -- ** Alpha-equivalence
    aeq, aeqBinders,
    acompare,

    -- ** Variable calculations

    -- | Functions for computing the free variables or binding
    --   variables of a term or pattern.  Note that all these
    --   functions may return an arbitrary /collection/, which
    --   includes lists, sets, and multisets.
    fv, fvAny, patfv, patfvAny, binders, bindersAny,

    -- *** Collections
    Collection(..), Multiset(..),

    -- ** Substitution

    -- | Capture-avoiding substitution.
    Subst(..), SubstName(..),

    -- ** Permutations

    Perm,

    -- *** Working with permutations
    single, compose, apply, support, isid, join, empty, restrict, mkPerm,

    -- *** Permuting terms
    swaps, swapsEmbeds, swapsBinders,

    -- * Freshness

    -- | When opening a term-level binding ('Bind' or 'TRec'), fresh
    --   names must be generated for the binders of its pattern.
    --   Fresh names can be generated according to one of two
    --   strategies: names can be /globally/ fresh (not conflicting
    --   with any other generated names, ever; see 'Fresh') or
    --   /locally/ fresh (not conflicting only with a specific set of
    --   \"currently in-scope\" names; see 'LFresh').  Generating
    --   globally fresh names is simpler and suffices for many
    --   applications.  Generating locally fresh names tends to be
    --   useful when the names are for human consumption, e.g. when
    --   implementing a pretty-printer.

    -- ** Global freshness
    freshen,

    -- *** The @Fresh@ class
    Fresh(..),

    -- *** The @FreshM@ monad

    -- | The @FreshM@ monad provides a concrete implementation of the
    --   'Fresh' type class.  The @FreshMT@ monad transformer variant
    --   can be freely combined with other standard monads and monad
    --   transformers from the @transformers@ library.

    FreshM, runFreshM,
    FreshMT, runFreshMT,

    -- ** Local freshness
    lfreshen,

    -- *** The @LFresh@ class
    LFresh(..),

    -- *** The @LFreshM@ monad

    -- | The @LFreshM@ monad provides a concrete implementation of the
    --   'LFresh' type class.  The @LFreshMT@ monad transformer variant
    --   can be freely combined with other standard monads and monad
    --   transformers from the @transformers@ library.

    LFreshM, runLFreshM, getAvoids,
    LFreshMT, runLFreshMT,

    -- * The @Alpha@ class
    Alpha(..),

    -- * Re-exported RepLib API for convenience

    module Generics.RepLib,

    -- * Pay no attention to the man behind the curtain

    -- | These type representation objects are exported so they can be
    --   referenced by auto-generated code.  Please pretend they do not
    --   exist.
    rName, rBind, rRebind, rEmbed, rRec, rShift
) where

import Unbound.LocallyNameless.Name
import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Subst
import Unbound.LocallyNameless.Ops
import Unbound.Util
import Unbound.PermM

import Generics.RepLib