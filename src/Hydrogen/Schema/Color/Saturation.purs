-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // color // saturation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Saturation - color intensity/purity.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: Grayscale (no color)
-- | - **50%**: Muted, desaturated
-- | - **100%**: Fully saturated, vivid
-- |
-- | In HSL color space, saturation describes how much gray is mixed in.
-- | At 0% saturation, the hue is irrelevant - you get pure gray.

module Hydrogen.Schema.Color.Saturation
  ( Saturation
  , saturation
  , unsafeSaturation
  , unwrap
  , scale
  , increase
  , decrease
  , isGrayscale
  , isVivid
  , bounds
  , toNumber
  , toUnitInterval
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // saturation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Saturation value as percentage (0-100)
-- |
-- | Represents color purity/intensity. 0% is grayscale, 100% is fully vivid.
newtype Saturation = Saturation Int

derive instance eqSaturation :: Eq Saturation
derive instance ordSaturation :: Ord Saturation

instance showSaturation :: Show Saturation where
  show (Saturation s) = show s <> "%"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a saturation, clamping to 0-100
saturation :: Int -> Saturation
saturation n = Saturation (Bounded.clampInt 0 100 n)

-- | Create a saturation without clamping
-- |
-- | Use only when you know the value is valid.
unsafeSaturation :: Int -> Saturation
unsafeSaturation = Saturation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scale saturation by a factor (0.0 to 2.0 typical)
scale :: Number -> Saturation -> Saturation
scale factor (Saturation s) = 
  saturation (Int.round (Int.toNumber s * factor))

-- | Increase saturation by percentage points
increase :: Int -> Saturation -> Saturation
increase amount (Saturation s) = saturation (s + amount)

-- | Decrease saturation by percentage points
decrease :: Int -> Saturation -> Saturation
decrease amount (Saturation s) = saturation (s - amount)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // predicates
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if saturation is effectively grayscale (< 5%)
isGrayscale :: Saturation -> Boolean
isGrayscale (Saturation s) = s < 5

-- | Check if saturation is vivid (> 80%)
isVivid :: Saturation -> Boolean
isVivid (Saturation s) = s > 80

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Saturation -> Int
unwrap (Saturation s) = s

-- | Convert to Number for calculations
toNumber :: Saturation -> Number
toNumber (Saturation s) = Int.toNumber s

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Saturation -> Number
toUnitInterval (Saturation s) = Int.toNumber s / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "saturation" "Color intensity as percentage"
