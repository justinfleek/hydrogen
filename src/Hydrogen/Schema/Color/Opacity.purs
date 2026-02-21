-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // opacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Opacity - alpha transparency value.
-- |
-- | A floating-point value from 0.0 to 1.0:
-- | - **0.0**: Fully transparent (invisible)
-- | - **0.5**: Half transparent
-- | - **1.0**: Fully opaque (solid)
-- |
-- | Used in RGBA, HSLA, and other color spaces with alpha channels.
-- | Also known as alpha or transparency.

module Hydrogen.Schema.Color.Opacity
  ( Opacity
  , opacity
  , unsafeOpacity
  , unwrap
  , scale
  , invert
  , multiply
  , blend
  , bounds
  , fromPercent
  , toPercent
  , fromChannel
  , toChannel
  , isTransparent
  , isOpaque
  , isSemiTransparent
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // opacity
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Opacity value (0.0-1.0)
-- |
-- | Represents alpha transparency in color values. 0.0 is fully transparent,
-- | 1.0 is fully opaque. This is the standard representation used in CSS,
-- | Canvas, WebGL, and most graphics APIs.
newtype Opacity = Opacity Number

derive instance eqOpacity :: Eq Opacity
derive instance ordOpacity :: Ord Opacity

instance showOpacity :: Show Opacity where
  show (Opacity o) = show o

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an opacity value, clamping to 0.0-1.0
-- |
-- | Values outside the valid range are clamped:
-- | ```purescript
-- | opacity 0.5   -- Opacity 0.5
-- | opacity 1.5   -- Opacity 1.0 (clamped)
-- | opacity (-0.2) -- Opacity 0.0 (clamped)
-- | ```
opacity :: Number -> Opacity
opacity n = Opacity (Bounded.clampNumber 0.0 1.0 n)

-- | Create an opacity value without clamping
-- |
-- | Use only when you know the value is valid (0.0-1.0).
-- | Invalid values will break invariants.
unsafeOpacity :: Number -> Opacity
unsafeOpacity = Opacity

-- | Create opacity from percentage (0-100)
-- |
-- | Useful for user interfaces that display alpha as percentages.
-- | ```purescript
-- | fromPercent 50.0  -- Opacity 0.5
-- | fromPercent 100.0 -- Opacity 1.0
-- | ```
fromPercent :: Number -> Opacity
fromPercent p = opacity (p / 100.0)

-- | Create opacity from 8-bit channel value (0-255)
-- |
-- | Useful for converting RGBA8 formats where alpha is stored as a byte.
-- | ```purescript
-- | fromChannel 0    -- Opacity 0.0
-- | fromChannel 128  -- Opacity 0.502
-- | fromChannel 255  -- Opacity 1.0
-- | ```
fromChannel :: Int -> Opacity
fromChannel c = opacity (Int.toNumber (Bounded.clampInt 0 255 c) / 255.0)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scale opacity by a factor
-- |
-- | Useful for fading effects:
-- | ```purescript
-- | scale 0.5 (opacity 0.8)  -- Opacity 0.4
-- | scale 2.0 (opacity 0.3)  -- Opacity 0.6
-- | ```
scale :: Number -> Opacity -> Opacity
scale factor (Opacity o) = opacity (o * factor)

-- | Invert opacity (1.0 - value)
-- |
-- | Converts transparency to opacity and vice versa:
-- | ```purescript
-- | invert (opacity 0.3)  -- Opacity 0.7
-- | invert (opacity 1.0)  -- Opacity 0.0
-- | ```
invert :: Opacity -> Opacity
invert (Opacity o) = Opacity (1.0 - o)

-- | Multiply two opacity values
-- |
-- | Models layering of transparent surfaces. Result is always more transparent
-- | than either input (unless one is fully opaque):
-- | ```purescript
-- | multiply (opacity 0.5) (opacity 0.5)  -- Opacity 0.25
-- | multiply (opacity 0.8) (opacity 0.9)  -- Opacity 0.72
-- | ```
multiply :: Opacity -> Opacity -> Opacity
multiply (Opacity a) (Opacity b) = Opacity (a * b)

-- | Blend two opacity values with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation between two alpha values:
-- | ```purescript
-- | blend 0.0 (opacity 0.2) (opacity 0.8)  -- Opacity 0.2
-- | blend 0.5 (opacity 0.2) (opacity 0.8)  -- Opacity 0.5
-- | blend 1.0 (opacity 0.2) (opacity 0.8)  -- Opacity 0.8
-- | ```
blend :: Number -> Opacity -> Opacity -> Opacity
blend weight (Opacity a) (Opacity b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
  in Opacity (a * (1.0 - w) + b * w)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value (0.0-1.0)
unwrap :: Opacity -> Number
unwrap (Opacity o) = o

-- | Convert to percentage (0.0-100.0)
-- |
-- | Useful for displaying alpha values in UIs:
-- | ```purescript
-- | toPercent (opacity 0.5)  -- 50.0
-- | toPercent (opacity 1.0)  -- 100.0
-- | ```
toPercent :: Opacity -> Number
toPercent (Opacity o) = o * 100.0

-- | Convert to 8-bit channel value (0-255)
-- |
-- | Useful for serializing to RGBA8 formats:
-- | ```purescript
-- | toChannel (opacity 0.0)  -- 0
-- | toChannel (opacity 0.5)  -- 128
-- | toChannel (opacity 1.0)  -- 255
-- | ```
toChannel :: Opacity -> Int
toChannel (Opacity o) = Int.round (o * 255.0)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // predicates
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if fully transparent (alpha = 0.0)
-- |
-- | Useful for optimization - fully transparent layers don't need rendering:
-- | ```purescript
-- | isTransparent (opacity 0.0)   -- true
-- | isTransparent (opacity 0.001) -- false
-- | ```
isTransparent :: Opacity -> Boolean
isTransparent (Opacity o) = o == 0.0

-- | Check if fully opaque (alpha = 1.0)
-- |
-- | Useful for optimization - fully opaque layers can occlude layers behind:
-- | ```purescript
-- | isOpaque (opacity 1.0)   -- true
-- | isOpaque (opacity 0.999) -- false
-- | ```
isOpaque :: Opacity -> Boolean
isOpaque (Opacity o) = o == 1.0

-- | Check if semi-transparent (0.0 < alpha < 1.0)
-- |
-- | Detects cases requiring alpha blending:
-- | ```purescript
-- | isSemiTransparent (opacity 0.5)  -- true
-- | isSemiTransparent (opacity 0.0)  -- false
-- | isSemiTransparent (opacity 1.0)  -- false
-- | ```
isSemiTransparent :: Opacity -> Boolean
isSemiTransparent (Opacity o) = o > 0.0 && o < 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // metadata
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "opacity" "alpha transparency"
