{-# LANGUAGE RankNTypes
           , TemplateHaskell
           , GADTs
           , FlexibleInstances
           , MultiParamTypeClasses
  #-}
----------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib.Bind.Nominal.Name
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
-- Stability   :  experimental
-- Portability :  XXX
--
-- XXX write me
----------------------------------------------------------------------

module Generics.RepLib.Bind.Nominal.Name where
-- XXX todo make explicit export list

import Generics.RepLib

-- | 'Name's are things that get bound.  This type is intentionally
--   abstract; to create a 'Name' you can use 'string2Name' or
--   'integer2Name'. The type parameter is a tag, or /sort/, which tells
--   us what sorts of things this name may stand for. The sort must
--   be an instance of the 'Rep' type class.
data Name a
  = Nm (R a) (String, Integer)   -- free names
   deriving (Eq, Ord)

-- | A name with a hidden (existentially quantified) sort.
data AnyName = forall a. Rep a => AnyName (Name a)

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
name2Integer :: Name a -> Integer
name2Integer (Nm _ (_,x)) = x


-- | Get the string part of a 'Name'.
name2String :: Name a -> String
name2String (Nm _ (s,_)) = s


-- | Get the integer index of an 'AnyName'.
anyName2Integer :: AnyName -> Integer
anyName2Integer (AnyName nm) = name2Integer nm

-- | Get the string part of an 'AnyName'.
anyName2String :: AnyName -> String
anyName2String (AnyName nm) = name2String nm

toSortedName :: Rep a => AnyName -> Maybe (Name a)
toSortedName (AnyName n) = gcastR (getR n) rep n

-- | Create a 'Name' from an 'Integer'.
integer2Name :: Rep a => Integer -> Name a
integer2Name n = makeName "" n

-- | Create a 'Name' from a 'String'.
string2Name :: Rep a => String -> Name a
string2Name s = makeName s 0

-- | Convenient synonym for 'string2Name'.
s2n :: Rep a => String -> Name a
s2n = string2Name

-- | Create a 'Name' from a @String@ and an @Integer@ index.
makeName :: Rep a => String -> Integer -> Name a
makeName s i = Nm rep (s,i)

-- | Determine the sort of a 'Name'.
getR :: Name a -> R a
getR (Nm r _)   = r


-- | Change the sort of a name
translate :: (Rep b) => Name a -> Name b
translate (Nm _ x) = Nm rep x

