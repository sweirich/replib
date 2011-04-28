{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses
  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  RepLib.PreludeReps
-- License     :  BSD
--
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
-- Representations for Prelude types, necessary to (automatically) derive
-- representations of user defined types.
-----------------------------------------------------------------------------
module Generics.RepLib.PreludeReps where

import Generics.RepLib.R
import Generics.RepLib.R1
import Generics.RepLib.Derive
import Language.Haskell.TH

$(derive [''Bool,
          ''Maybe,
          ''Either,
          ''Ordering,
          tupleTypeName 3,
          tupleTypeName 4,
          tupleTypeName 5,
          tupleTypeName 6,
          tupleTypeName 7])


