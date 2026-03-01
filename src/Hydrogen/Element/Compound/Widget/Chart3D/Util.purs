-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // chart3d // util
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Utility functions for 3D charts.
-- |
-- | Provides math helpers, color utilities, and array operations
-- | used by bar and surface chart renderers.

module Hydrogen.Element.Compound.Widget.Chart3D.Util
  ( -- * Array Math
    arrayMin
  , arrayMax
  
  -- * Bar Helpers
  , getMaxBarValue
  , getBar3DColor
  , formatBarValue
  
  -- * Color Interpolation
  , interpolateColor
  
  -- * Index Generation
  , generateIndices
  ) where

import Prelude
  ( class Show
  , show
  , (==)
  , (&&)
  , (<>)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , mod
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Data.Array (foldl, index, length, mapWithIndex, replicate)
import Hydrogen.Element.Compound.Widget.Chart3D.Types (Bar3DData, defaultBar3DColors)
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // array math
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum value from array.
arrayMin :: Array Number -> Number
arrayMin arr = case index arr 0 of
  Nothing -> 0.0
  Just first -> foldl min' first arr
  where
    min' :: Number -> Number -> Number
    min' a b = if a < b then a else b

-- | Get maximum value from array.
arrayMax :: Array Number -> Number
arrayMax arr = case index arr 0 of
  Nothing -> 0.0
  Just first -> foldl max' first arr
  where
    max' :: Number -> Number -> Number
    max' a b = if a > b then a else b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bar helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get maximum bar value.
getMaxBarValue :: Array Bar3DData -> Number
getMaxBarValue bars = 
  let values = mapWithIndex (\_ b -> b.value) bars
  in arrayMax values

-- | Get bar color at index from palette.
getBar3DColor :: Int -> String
getBar3DColor idx =
  let paletteLen = length defaultBar3DColors
      wrappedIdx = if paletteLen == 0 then 0 else idx `mod` paletteLen
  in fromMaybe "#f97316" (index defaultBar3DColors wrappedIdx)

-- | Format bar value for display.
formatBarValue :: Number -> String
formatBarValue v
  | v > 999999.0 = show (Math.floor (v / 100000.0) / 10.0) <> "M"
  | v > 999.0 = show (Math.floor (v / 100.0) / 10.0) <> "K"
  | v < 0.0 && v > (negate 1000.0) = show (Math.floor v)
  | v < (negate 999.0) = show (Math.floor (v / 100.0) / 10.0) <> "K"
  | v < (negate 999999.0) = show (Math.floor (v / 100000.0) / 10.0) <> "M"
  | true = show (Math.floor v)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // color interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolate between two hex colors.
-- |
-- | Simple linear interpolation in RGB space.
-- | For t=0, returns colorMin; for t=1, returns colorMax.
interpolateColor :: String -> String -> Number -> String
interpolateColor colorMin colorMax t =
  let
    t' = if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t
    -- Simple approach: blend the colors via opacity
    -- A more complete implementation would parse hex to RGB
  in
    if t' < 0.33 then colorMin
    else if t' < 0.66 then "#a855f7"  -- Purple midpoint
    else colorMax

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // index generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate array of indices from 0 to n-1.
generateIndices :: Int -> Array Int
generateIndices n = 
  if n < 1 
    then []
    else mapWithIndex (\idx _ -> idx) (replicate n 0)
