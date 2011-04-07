{-# LANGUAGE RankNTypes
           , TemplateHaskell
           , GADTs
           , FlexibleInstances
           , MultiParamTypeClasses
           , ScopedTypeVariables
           , FlexibleContexts
           , UndecidableInstances
  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Unbound.Nominal.Name
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  XXX
--
-- XXX write me
----------------------------------------------------------------------

module Unbound.Nominal.Name where
-- XXX todo make explicit export list

import Generics.RepLib
import Unbound.Name 

-- | 'Name's are things that get bound.  This type is intentionally
--   abstract; to create a 'Name' you can use 'string2Name' or
--   'integer2Name'. The type parameter is a tag, or /sort/, which tells
--   us what sorts of things this name may stand for. The sort must
--   be an instance of the 'Rep' type class.
data Name a
  = Nm (R a) (String, Integer)   -- free names
   deriving (Eq, Ord)

$(derive [''Name])

instance Rep a => AName (Name a) where
    name2Integer = nomName2Integer
    name2String  = nomName2String
    renumber j (Nm r (s,i)) = (Nm r (s,j))

-- | Create a free 'Name' from an 'Integer'.
integer2Name :: Rep a => Integer -> Name a
integer2Name n = makeName "" n

-- | Create a free 'Name' from a 'String'.
string2Name :: Rep a => String -> Name a
string2Name s = makeName s 0

-- | Convenient synonym for 'string2Name'.
s2n :: Rep a => String -> Name a
s2n = string2Name


------------------------------------------------------------
-- Utilities
------------------------------------------------------------

-- some convenient names for testing
name1, name2, name3, name4, name5, name6, name7, name8, name9, name10, name11
  :: Rep a => Name a
name1 = integer2Name 1
name2 = integer2Name 2
name3 = integer2Name 3
name4 = integer2Name 4
name5 = integer2Name 5
name6 = integer2Name 6
name7 = integer2Name 7
name8 = integer2Name 8
name9 = integer2Name 9
name10 = integer2Name 10
name11 = integer2Name 11

--instance Read Name where
--  read s = error "FIXME"

instance Show (Name a) where
  show (Nm _ ("",n)) = "_" ++ (show n)
  show (Nm _ (x,0))  = x
  show (Nm _ (x,n))  = x ++ (show n)

-- | Get the integer index of a 'Name'.
nomName2Integer :: Name a -> Integer
nomName2Integer (Nm _ (_,x)) = x

-- | Get the string part of a 'Name'.
nomName2String :: Name a -> String
nomName2String (Nm _ (s,_)) = s


-- | Create a 'Name' from a @String@ and an @Integer@ index.
makeName :: Rep a => String -> Integer -> Name a
makeName s i = Nm rep (s,i)

-- | Change the sort of a name
translate :: (Rep b) => Name a -> Name b
translate (Nm _ x) = Nm rep x

