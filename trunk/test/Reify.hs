{-# LANGUAGE TemplateHaskell #-}

module Reify where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

doReify :: Name -> Q [Dec]
doReify n = do
  info <- reify n
  -- let s = show $
  --         case info of
  --           TyConI dec ->
  --             case dec of
  --               (DataD _ _ _ cs _) ->
  --                 map conA cs
  let s = show info
  [d| str = $(lift s) |]

conA (NormalC c xs)         = (c, length xs)
conA (RecC c xs)            = (c, length xs)
conA (InfixC _ c _)         = (c, 2)
