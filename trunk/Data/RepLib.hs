-- OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances 
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-} 

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.RepLib
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
--
--
-----------------------------------------------------------------------------

--  Toplevel module to import all others
module Data.RepLib (
 -- * Basic infrastructure
 -- ** Basic Representations of types
 module Data.RepLib.R,   
 -- ** Parameterized Representations of types
 module Data.RepLib.R1,
 -- ** Representations of Prelude Types	
 module Data.RepLib.PreludeReps,
 -- ** Template Haskell for deriving representations
 module Data.RepLib.Derive,
 -- * Libraries for defining Generic Operations
 -- ** Library code for defining generic operations
 module Data.RepLib.RepAux,
 -- ** Scrap your boilerplate operations
 module Data.RepLib.SYB.Aliases, 
 module Data.RepLib.SYB.Schemes,
 -- * Generic Utilities and Applications
 -- ** Library of generic operations
 module Data.RepLib.Lib,
 -- ** Derivable type classes written as generic operations
 module Data.RepLib.PreludeLib
) where


import Data.RepLib.R
import Data.RepLib.R1
import Data.RepLib.PreludeReps
import Data.RepLib.Derive
import Data.RepLib.RepAux
import Data.RepLib.SYB.Aliases
import Data.RepLib.SYB.Schemes
import Data.RepLib.Lib
import Data.RepLib.PreludeLib
-----------------------------------------------------------------------------

