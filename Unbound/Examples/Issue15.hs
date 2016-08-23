{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, MultiParamTypeClasses, StandaloneDeriving
 #-}

module Issue15 where

import Generics.RepLib
import qualified Unbound.LocallyNameless as LN

data Foo = Foo (LN.Name Foo)

$(derive [''Foo])
