{-# LANGUAGE RankNTypes
           , FlexibleContexts
           , GADTs
           , TypeFamilies
           , TemplateHaskell
           , FlexibleInstances
           , MultiParamTypeClasses
           , ScopedTypeVariables
  #-}

-- A specification of names so that different implementations
-- can use the same monads for name generation, permutation, etc.
-- Also, in the future, we can also experiment with interned
-- strings for names (requires monadic string2Name and name2String
-- operations).

module Unbound.Name where
-- XXX todo make explicit export list

import Generics.RepLib

$(derive_abstract [''R])
-- The above only works with GHC 7.

------------------------------------------------------------
-- Name class
------------------------------------------------------------

class (Ord n, Show n, Rep n) => AName n where
  renumber     :: Integer -> n -> n   

getR :: AName n => n -> R n
getR x = rep

------------------------------------------------------------
-- Abstract Names
------------------------------------------------------------

-- | A name with a hidden (existentially quantified) sort.  To hide
--   the sort of a name, use the 'AnyName' constructor directly; to
--   extract a name with a hidden sort, use 'toSortedName'.
data AnyName where 
     AnyName :: forall n. (AName n) => n -> AnyName

$(derive_abstract [''AnyName])

instance Eq (AnyName) where
     (AnyName n1) == (AnyName n2) = 
         case cast n1 of
           Just n1' -> n1' == n2
           Nothing  -> case cast n1 of 
              Just (n1' :: AnyName) -> n1' == (AnyName n2)
              Nothing -> case cast n2 of 
                 Just (n2' :: AnyName) -> (AnyName n1) == n2'
                 Nothing -> False

instance Ord (AnyName) where
   compare (AnyName n1) (AnyName n2) =
       case compareR (getR n1) (getR n2) of
         EQ  -> case cast n1 of

           Just n1' -> compare n1' n2
           Nothing  -> error "Panic: equal types are not equal in Ord AnyName instance!"
         ord -> ord

instance Show (AnyName) where
  show (AnyName n1) = show n1

instance AName AnyName where
--  name2Integer (AnyName n) = name2Integer n
--  name2String  (AnyName n) = name2String  n
  renumber i   (AnyName n) = AnyName (renumber i n)

-- | Cast a name with an existentially hidden sort to an explicitly
--   sorted name.
toSortedName :: AName a => AnyName -> Maybe a
toSortedName (AnyName n) = castR (getR n) rep n

-- | Get the integer index of an 'AnyName'.
-- anyName2Integer :: AnyName -> Integer
-- anyName2Integer (AnyName nm) = name2Integer nm

-- | Get the string part of an 'AnyName'.
-- anyName2String :: AnyName -> String
-- anyName2String (AnyName nm) = name2String nm