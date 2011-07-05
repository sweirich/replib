{-# LANGUAGE TemplateHaskell
           , UndecidableInstances
           , TypeOperators
           , GADTs
           , FlexibleInstances
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , KindSignatures
 #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Vec
-- Copyright   :  (c) the Unbound team (see LICENSE)
-- License     :  BSD-like (see LICENSE)
--
-- Maintainer  :  byorgey@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
-----------------------------------------------------------------------------

import Unbound.LocallyNameless hiding (Nil)
import Data.Type.Equality

data Z
data S n

data Vec :: * -> * -> * where
  Nil  :: Vec Z a
  Cons :: a -> Vec n a -> Vec (S n) a

$(derive [''Vec])