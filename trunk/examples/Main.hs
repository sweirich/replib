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

import qualified Basic
import qualified LC
import qualified STLC
import qualified Abstract


main = do
     Basic.main
     LC.main
     STLC.main
     Abstract.main
     print "Tests completed"
     
