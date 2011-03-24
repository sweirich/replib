-- OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances
{-# LANGUAGE TemplateHaskell, UndecidableInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Generics.RepLib
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
module Generics.RepLib (
 -- * Basic infrastructure
 -- ** Basic Representations of types
 module Generics.RepLib.R,
 -- ** Parameterized Representations of types
 module Generics.RepLib.R1,
 -- ** Representations of Prelude Types
 module Generics.RepLib.PreludeReps,
 -- ** Template Haskell for deriving representations
 module Generics.RepLib.Derive,
 -- * Libraries for defining Generic Operations
 -- ** Library code for defining generic operations
 module Generics.RepLib.RepAux,
 -- ** Scrap your boilerplate operations
 module Generics.RepLib.SYB.Aliases,
 module Generics.RepLib.SYB.Schemes,
 -- * Generic Utilities and Applications
 -- ** Library of generic operations
 module Generics.RepLib.Lib,
 -- ** Derivable type classes written as generic operations
 module Generics.RepLib.PreludeLib
) where


import Generics.RepLib.R
import Generics.RepLib.R1
import Generics.RepLib.PreludeReps
import Generics.RepLib.Derive
import Generics.RepLib.RepAux
import Generics.RepLib.SYB.Aliases
import Generics.RepLib.SYB.Schemes
import Generics.RepLib.Lib
import Generics.RepLib.PreludeLib
-----------------------------------------------------------------------------

