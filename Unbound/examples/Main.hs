-- OPTIONS -fglasgow-exts -fth -fallow-undecidable-instances 
{-# LANGUAGE TemplateHaskell, UndecidableInstances, ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses  #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) The University of Pennsylvania, 2006
-- License     :  BSD
-- 
-- Maintainer  :  sweirich@cis.upenn.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Testsuite
--
-----------------------------------------------------------------------------

module Main where

import qualified Examples.Basic as Basic
import qualified Examples.LC as LC
import qualified Examples.STLC as STLC
-- import qualified Examples.Abstract as Abstract


main = do
     Basic.main
     LC.main
     STLC.main
     -- Abstract.main
     -- F.main
     print "Tests completed"
     
