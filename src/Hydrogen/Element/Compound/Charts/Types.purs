-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // compound // charts // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Types — Shared types and utilities for chart components.

module Hydrogen.Element.Compound.Charts.Types
  ( -- * Color Scale
    ColorScale(Sequential, Diverging, Categorical)
  , valueToColor
  
  -- * Math Utilities
  , min
  , max
  ) where

import Prelude
  ( class Eq
  , show
  , (<>)
  , (<)
  , (>)
  , (-)
  , (*)
  )

import Data.Int as Int
import Data.Array as Array
import Data.Maybe (fromMaybe)
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // color scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color scale type
data ColorScale
  = Sequential    -- Low to high (blue to red)
  | Diverging     -- Negative to positive (red-white-blue)
  | Categorical   -- Discrete colors

derive instance eqColorScale :: Eq ColorScale

-- | Map value to color based on scale
valueToColor :: ColorScale -> Number -> String
valueToColor Sequential v =
  -- Blue (low) to Red (high)
  let
    r = Int.floor (v * 239.0)
    g = Int.floor ((1.0 - v) * 68.0)
    b = Int.floor ((1.0 - v) * 255.0)
  in
    "rgb(" <> show r <> "," <> show g <> "," <> show b <> ")"
valueToColor Diverging v =
  -- Red (negative) to White (zero) to Blue (positive)
  if v < 0.5
    then
      let intensity = Int.floor ((0.5 - v) * 2.0 * 255.0)
      in "rgb(255," <> show (255 - intensity) <> "," <> show (255 - intensity) <> ")"
    else
      let intensity = Int.floor ((v - 0.5) * 2.0 * 255.0)
      in "rgb(" <> show (255 - intensity) <> "," <> show (255 - intensity) <> ",255)"
valueToColor Categorical v =
  let
    colors = ["#3b82f6", "#22c55e", "#eab308", "#ef4444", "#8b5cf6", "#ec4899", "#06b6d4"]
    idx = Int.floor (v * 6.0)
  in
    fromMaybe "#3b82f6" (Array.index colors idx)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // math utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Min of two numbers
min :: Number -> Number -> Number
min a b = if a < b then a else b

-- | Max of two numbers
max :: Number -> Number -> Number
max a b = if a > b then a else b
