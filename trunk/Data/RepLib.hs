-- OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances 
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-} 

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib
-- Copyright   :  (c) The University of Pennsylvania, 2006
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
--
-----------------------------------------------------------------------------

-- Toplevel module to import all others.

module Data.RepLib (

 module Data.RepLib.R,   
 module Data.RepLib.R1,	
 module Data.RepLib.Lib,
 module Data.RepLib.PreludeReps,
 module Data.RepLib.PreludeLib,
 module Data.RepLib.RepAux,
 module Data.RepLib.Derive,
 module Data.RepLib.SYB.Aliases, 
 module Data.RepLib.SYB.Schemes

) where

import Data.RepLib.R
import Data.RepLib.R1
import Data.RepLib.PreludeReps
import Data.RepLib.Lib
import Data.RepLib.PreludeLib
import Data.RepLib.RepAux
import Data.RepLib.Derive
import Data.RepLib.SYB.Aliases
import Data.RepLib.SYB.Schemes

-----------------------------------------------------------------------------

