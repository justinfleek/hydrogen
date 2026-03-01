-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // table // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Helpers — Utility functions for table rendering.
-- |
-- | ## Overview
-- |
-- | This module provides low-level helper functions:
-- | - Array min/max operations
-- | - Number formatting
-- | - Foreign imports for Int/Number conversions

module Hydrogen.Element.Compound.Widget.Table.Helpers
  ( -- * Array Operations
    arrayMin
  , arrayMax
  
  -- * Formatting
  , formatNumber
  
  -- * Conversions
  , toNumber
  , mod
  ) where

import Prelude
  ( show
  , (<)
  , (>)
  , (/)
  , (-)
  )

import Data.Array (foldl)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // array operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum value from array.
arrayMin :: Array Number -> Number
arrayMin arr = foldl min' (1.0 / 0.0) arr
  where
    min' a b = if a < b then a else b

-- | Get maximum value from array.
arrayMax :: Array Number -> Number
arrayMax arr = foldl max' (negate (1.0 / 0.0)) arr
  where
    max' a b = if a > b then a else b
    negate n = 0.0 - n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // formatting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format number for display.
formatNumber :: Number -> String
formatNumber n = show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
foreign import toNumber :: Int -> Number

-- | Integer modulo.
foreign import mod :: Int -> Int -> Int
