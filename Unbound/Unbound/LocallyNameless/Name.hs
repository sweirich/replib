{-# LANGUAGE RankNTypes
           , TemplateHaskell
           , GADTs
           , UndecidableInstances
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , ScopedTypeVariables
  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless.Name
-- License     :  BSD-like (see LICENSE)
-- Maintainer  :  Brent Yorgey <byorgey@cis.upenn.edu>
-- Portability :  GHC only
--
-- An implementation of names in a locally nameless representation.
----------------------------------------------------------------------

module Unbound.LocallyNameless.Name
       ( -- * Name types

         Name(..)
       , AnyName(..)

         -- * Constructing and destructing free names

       , integer2Name, string2Name, s2n, makeName

       , name2Integer, name2String
       , anyName2Integer, anyName2String

         -- * Sorts

       , toSortedName, translate, getR

         -- * Utility

       , isBound, isFree

         -- * Representations
         -- | Automatically generated representation objects.

       , rR, rR1
       , rName, rName1
       , rAnyName, rAnyName1
       ) where

import Generics.RepLib

$(derive_abstract [''R])
-- The above only works with GHC 7.

-- | 'Name's are things that get bound.  This type is intentionally
--   abstract; to create a 'Name' you can use 'string2Name' or
--   'integer2Name'. The type parameter is a tag, or /sort/, which
--   tells us what sorts of things this name may stand for. The sort
--   must be a /representable/ type, /i.e./ an instance of the 'Rep'
--   type class from the @RepLib@ generic programming framework.
--
--   To hide the sort of a name, use 'AnyName'.
data Name a
  = Nm (R a) (String, Integer)   -- free names
  | Bn (R a) Integer Integer     -- bound names / binding level + pattern index
   deriving (Eq, Ord)

$(derive [''Name])

-- | A name with a hidden (existentially quantified) sort.  To hide
--   the sort of a name, use the 'AnyName' constructor directly; to
--   extract a name with a hidden sort, use 'toSortedName'.
data AnyName = forall a. Rep a => AnyName (Name a)

-- | Test whether a name is a bound variable (i.e. a reference to some
--   binding site, represented as a de Bruijn index).  Normal users of
--   the library should not need this function, as it is impossible to
--   encounter a bound name when using the abstract interface provided
--   by "Unbound.LocallyNameless".
isBound :: Name a -> Bool
isBound (Nm _ _) = False
isBound (Bn _ _ _) = True

-- | Test whether a name is a free variable. Normal users of the
--   library should not need this function, as all the names
--   encountered will be free variables when using the abstract
--   interface provided by "Unbound.LocallyNameless".
isFree :: Name a -> Bool
isFree (Nm _ _) = True
isFree (Bn _ _ _) = False

-- AnyName has an existential in it, so we cannot create a complete
-- representation for it, unfortunately.

$(derive_abstract [''AnyName])

instance Show AnyName where
  show (AnyName n1) = show n1

instance Eq AnyName where
   (AnyName n1) == (AnyName n2) =
      case gcastR (getR n1) (getR n2) n1 of
           Just n1' -> n1' == n2
           Nothing  -> False

instance Ord AnyName where
   compare (AnyName n1) (AnyName n2) =
       case compareR (getR n1) (getR n2) of
         EQ  -> case gcastR (getR n1) (getR n2) n1 of
           Just n1' -> compare n1' n2
           Nothing  -> error "Panic: equal types are not equal in Ord AnyName instance!"
         ord -> ord

------------------------------------------------------------
-- Utilities
------------------------------------------------------------

--instance Read Name where
--  read s = error "FIXME"

instance Show (Name a) where
  show (Nm _ ("",n)) = "_" ++ (show n)
  show (Nm _ (x,0))  = x
  show (Nm _ (x,n))  = x ++ (show n)
  show (Bn _ x y)    =  show x ++ "@" ++ show y

-- | Get the integer index of a 'Name'.
name2Integer :: Name a -> Integer
name2Integer (Nm _ (_,x)) = x
name2Integer (Bn _ _ _)   = error "Internal Error: cannot call name2Integer for bound names"

-- | Get the string part of a 'Name'.
name2String :: Name a -> String
name2String (Nm _ (s,_)) = s
name2String (Bn _ _ _)   = error "Internal Error: cannot call name2Integer for bound names"

-- | Get the integer index of an 'AnyName'.
anyName2Integer :: AnyName -> Integer
anyName2Integer (AnyName nm) = name2Integer nm

-- | Get the string part of an 'AnyName'.
anyName2String :: AnyName -> String
anyName2String (AnyName nm) = name2String nm

-- | Cast a name with an existentially hidden sort to an explicitly
--   sorted name.
toSortedName :: Rep a => AnyName -> Maybe (Name a)
toSortedName (AnyName n) = gcastR (getR n) rep n

-- | Create a free 'Name' from an 'Integer'.
integer2Name :: Rep a => Integer -> Name a
integer2Name n = makeName "" n

-- | Create a free 'Name' from a 'String'.
string2Name :: Rep a => String -> Name a
string2Name s = makeName s 0

-- | Convenient synonym for 'string2Name'.
s2n :: Rep a => String -> Name a
s2n = string2Name

-- | Create a free 'Name' from a @String@ and an @Integer@ index.
makeName :: Rep a => String -> Integer -> Name a
makeName s i = Nm rep (s,i)

-- | Determine the sort of a 'Name'.
getR :: Name a -> R a
getR (Nm r _)   = r
getR (Bn r _ _) = r

-- | Change the sort of a name.
translate :: (Rep b) => Name a -> Name b
translate (Nm _ x) = Nm rep x
translate (Bn _ x y) = Bn rep x y
