-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--        // hydrogen // schema // motion // professional // propertyvalue // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Property Value — RGBA color type for motion graphics properties.
-- |
-- | Motion graphics tools use 0-1 floating point for colors internally. This module defines
-- | the ColorValue type used for Fill Color, Stroke Color, etc.

module Hydrogen.Schema.Motion.Professional.PropertyValue.Color
  ( ColorValue
  , colorValue
  , colorValueRGB
  , colorValueR
  , colorValueG
  , colorValueB
  , colorValueA
  , colorValueToArray
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color value - RGBA in 0-1 range.
-- |
-- | AE uses 0-1 floating point for colors internally.
-- | This maps to Fill Color, Stroke Color, etc.
newtype ColorValue = ColorValue { r :: Number, g :: Number, b :: Number, a :: Number }

derive instance eqColorValue :: Eq ColorValue
derive instance ordColorValue :: Ord ColorValue

instance showColorValue :: Show ColorValue where
  show (ColorValue c) = 
    "[" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ", " <> show c.a <> "]"

colorValue :: Number -> Number -> Number -> Number -> ColorValue
colorValue r g b a = ColorValue 
  { r: clampNumber 0.0 1.0 r
  , g: clampNumber 0.0 1.0 g
  , b: clampNumber 0.0 1.0 b
  , a: clampNumber 0.0 1.0 a
  }

colorValueRGB :: Number -> Number -> Number -> ColorValue
colorValueRGB r g b = colorValue r g b 1.0

colorValueR :: ColorValue -> Number
colorValueR (ColorValue c) = c.r

colorValueG :: ColorValue -> Number
colorValueG (ColorValue c) = c.g

colorValueB :: ColorValue -> Number
colorValueB (ColorValue c) = c.b

colorValueA :: ColorValue -> Number
colorValueA (ColorValue c) = c.a

colorValueToArray :: ColorValue -> Array Number
colorValueToArray (ColorValue c) = [c.r, c.g, c.b, c.a]
