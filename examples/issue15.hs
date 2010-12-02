{-# LANGUAGE TemplateHaskell, UndecidableInstances, ExistentialQuantification,
    TypeOperators, GADTs, TypeSynonymInstances, FlexibleInstances,
    ScopedTypeVariables, MultiParamTypeClasses, StandaloneDeriving
 #-}

module Issue15 where

import Data.RepLib
import qualified Data.RepLib.Bind.LocallyNameless as LN

data Foo = Foo (LN.Name Foo)

$(derive [''Foo])  
