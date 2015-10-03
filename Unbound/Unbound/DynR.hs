{-# LANGUAGE GADTs, ScopedTypeVariables
  #-}

module Unbound.DynR (Dyn, toDyn, fromDyn, fromDynR) where

import Generics.RepLib

data Dyn where 
  Dyn :: Rep a => a -> Dyn
                
toDyn :: Rep a => a -> Dyn 
toDyn = Dyn 

-- TODO: implement with an unsafeCoerce
-- toDynR :: R a -> a -> Dyn
-- toDynR = undefined

fromDyn :: forall a. Rep a => Dyn -> Maybe a 
fromDyn (Dyn x) = cast x

fromDynR :: forall a. R a -> Dyn -> Maybe a
fromDynR r1 (Dyn x) = castR rep r1 x
