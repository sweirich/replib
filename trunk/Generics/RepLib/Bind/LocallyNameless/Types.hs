{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
  #-}

module Generics.RepLib.Bind.LocallyNameless.Types
       ( Bind(..)
       , Rebind(..)
       , Rec(..)
       , TRec(..)
       , Annot(..)
       , Outer(..)
       , module Generics.RepLib.Bind.LocallyNameless.Name

       -- * Pay no attention to the man behind the curtain
       -- $paynoattention
       , rBind, rRebind, rAnnot, rRec, rOuter
       ) where

import Generics.RepLib
import Generics.RepLib.Bind.LocallyNameless.Name

------------------------------------------------------------
-- Basic types
------------------------------------------------------------

-- Bind
--------------------------------------------------

-- | The type of a binding.  We can 'Bind' an @a@ object in a @b@
--   object if we can create \"fresh\" @a@ objects, and @a@ objects
--   can occur unbound in @b@ objects. Often @a@ is 'Name' but that
--   need not be the case.
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


-- Annot
--------------------------------------------------

-- | An annotation is a \"hole\" in a pattern where variables can be
--   used, but not bound. For example, patterns may include type
--   annotations, and those annotations can reference variables
--   without binding them.  Annotations do nothing special when they
--   appear elsewhere in terms.
newtype Annot t = Annot t deriving Eq

instance Show a => Show (Annot a) where
  showsPrec p (Annot a) = showString "{" . showsPrec 0 a . showString "}"

-- Outer
--------------------------------------------------

-- | An outer can shift an annotation \"hole\" to refer to higher context.
newtype Outer p = Outer p deriving Eq

instance Show a => Show (Outer a) where
  showsPrec p (Outer a) = showString "{" . showsPrec 0 a . showString "}"

-- $paynoattention
-- These type representation objects are exported so they can be
-- referenced by auto-generated code.  Please pretend they do not
-- exist.

$(derive [''Bind, ''Annot, ''Rebind, ''Rec, ''Outer])

