{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             TemplateHaskell, UndecidableInstances #-}
module Lib
     where

import Unbound.LocallyNameless

data Term = Word Word
  deriving Show

$(derive_abstract [''Word]) -- No type structure information available
$(derive [''Term])
instance Alpha Word
instance Alpha Term

t1 :: Term
t1 = Word 5

wrong :: Bool
wrong = t1 `aeq` t1 -- should throw an error as Word is "abstract"

