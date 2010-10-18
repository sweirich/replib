{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables,
    FlexibleInstances, MultiParamTypeClasses
  #-} 
-----------------------------------------------------------------------------
-- |
-- Module      :  RepLib.PreludeReps
-- Copyright   :  (c) The University of Pennsylvania, 2006
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- 
-- Automatically derive representations for prelude types
--
-----------------------------------------------------------------------------
module Data.RepLib.PreludeReps where

import Data.RepLib.R
import Data.RepLib.R1
import Data.RepLib.Derive
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


