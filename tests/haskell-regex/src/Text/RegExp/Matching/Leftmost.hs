-- |
-- Module      : Text.RegExp.Matching.Leftmost
-- Copyright   : Thomas Wilke, Frank Huch, and Sebastian Fischer
-- License     : BSD3
-- Maintainer  : Sebastian Fischer <mailto:sebf@informatik.uni-kiel.de>
-- Stability   : experimental
-- 
-- This module implements leftmost matching based on weighted regular
-- expressions. It should be imported qualified as the interface
-- resembles that provided by other matching modules.
-- 
module Text.RegExp.Matching.Leftmost (

  matching, 

  Matching, matchingIndex,

  Leftmost, getLeftmost

  ) where

import Text.RegExp
import Text.RegExp.Matching.Leftmost.Type

-- |
-- A 'Matching' records the leftmost start index of a matching subword.
-- 
data Matching = Matching {
 
  -- | Start index of the matching subword in the queried word.
  matchingIndex :: !Int
 
  }
 deriving Eq

instance Show Matching
 where
  showsPrec _ m = showString "<index:" . shows (matchingIndex m)
                . showString ">"

-- |
-- Returns the leftmost of all non-empty matchings for a regular
-- expression in a given word. If the empty word is the only matching
-- its position is zero.
-- 
matching :: RegExp c -> [c] -> Maybe Matching
matching r = getLeftmost . partialMatch r . zip [(0::Int)..]

getLeftmost :: Leftmost -> Maybe Matching
getLeftmost Zero          =  Nothing
getLeftmost One           =  Just $ Matching 0 
getLeftmost (Leftmost x)  =  Just $ Matching x
