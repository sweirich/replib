{-# LANGUAGE TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , MultiParamTypeClasses
           , EmptyDataDecls
  #-}

module Unbound.Nominal.Types where

import Generics.RepLib
import Unbound.Nominal.Name

data Bind p t = Bind p t
  deriving (Show)

data Rec p = Rec p
  deriving (Show)

newtype Embed t = Embed t
  deriving (Show)

data Rebind p1 p2 = Rebind p1 p2

$(derive [''Bind, ''Embed, ''Rec, ''Rebind])
