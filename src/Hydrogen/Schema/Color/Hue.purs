-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // color // hue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hue - position on the color wheel.
-- |
-- | Measured in degrees from 0 to 359:
-- | - **0°/360°**: Red
-- | - **60°**: Yellow  
-- | - **120°**: Green
-- | - **180°**: Cyan
-- | - **240°**: Blue
-- | - **300°**: Magenta
-- |
-- | Hue is cyclic - values outside 0-359 wrap around.

module Hydrogen.Schema.Color.Hue
  ( Hue
  , hue
  , hueWrap
  , unwrap
  , rotate
  , complement
  , bounds
  , toNumber
  ) where

import Prelude

import Data.Int (toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // hue
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hue value in degrees (0-359)
-- |
-- | Represents position on the color wheel. Red at 0°, cycling through
-- | yellow, green, cyan, blue, magenta, and back to red at 360°.
newtype Hue = Hue Int

derive instance eqHue :: Eq Hue
derive instance ordHue :: Ord Hue

instance showHue :: Show Hue where
  show (Hue h) = show h <> "°"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a hue, clamping to 0-359
hue :: Int -> Hue
hue n = Hue (Bounded.clampInt 0 359 n)

-- | Create a hue, wrapping values outside 0-359
-- |
-- | This is often what you want for rotations:
-- | - `hueWrap 370` = `hue 10`
-- | - `hueWrap (-30)` = `hue 330`
hueWrap :: Int -> Hue
hueWrap n = Hue (mod' n 360)
  where
  mod' a b = ((a `mod` b) + b) `mod` b

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees (wraps around)
rotate :: Int -> Hue -> Hue
rotate degrees' (Hue h) = hueWrap (h + degrees')

-- | Get complementary hue (opposite on color wheel)
complement :: Hue -> Hue
complement = rotate 180

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Hue -> Int
unwrap (Hue h) = h

-- | Convert to Number for calculations
toNumber :: Hue -> Number
toNumber (Hue h) = Int.toNumber h

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 359 "hue" "Color wheel position in degrees"
