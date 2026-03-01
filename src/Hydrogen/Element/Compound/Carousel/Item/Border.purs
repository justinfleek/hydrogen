-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // carousel // item border
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Item Border — Visual border effects for carousel items.
-- |
-- | ## Design Philosophy
-- |
-- | Borders define visual effects applied to item edges:
-- | - Solid color borders with configurable width
-- | - Gradient stroke borders (linear or conic)
-- | - Glowing/neon borders with blur
-- | - Animated borders (dash march, pulse, rainbow)
-- |
-- | ## Dependencies
-- |
-- | Pure module with no external dependencies.

module Hydrogen.Element.Compound.Carousel.Item.Border
  ( ItemBorder
      ( BorderNone
      , BorderSolid
      , BorderGradientLinear
      , BorderGradientConic
      , BorderGlow
      , BorderDashed
      , BorderAnimatedDash
      , BorderPulse
      , BorderRainbow
      )
  , itemBorder
  , noItemBorder
  , solidBorder
  , glowingBorder
  , glowingBorderWith
  , gradientBorder
  , gradientBorderWith
  , animatedDashBorder
  , animatedDashBorderWith
  , dashedBorder
  , pulseBorder
  , rainbowBorder
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border configuration for an item.
-- |
-- | Defines visual border effects applied to item edges:
-- | - Solid color borders with configurable width
-- | - Gradient stroke borders (linear or conic)
-- | - Glowing/neon borders with blur
-- | - Animated borders (dash march, pulse, rainbow)
-- |
-- | ## Border Width
-- |
-- | Width is in pixels, clamped to 0.0-20.0 range.
-- |
-- | ## Animation
-- |
-- | Animated borders have timing parameters:
-- | - speed: Animation cycle duration in ms
-- | - direction: Forward, reverse, or alternate
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple 2px solid border
-- | simple = solidBorder 2.0 "#3B82F6"
-- |
-- | -- Neon glow effect
-- | neon = glowingBorder 3.0 "#00FF00" 10.0
-- |
-- | -- Animated gradient
-- | rainbow = rainbowBorder 2.0 2000.0
-- | ```
data ItemBorder
  = BorderNone                                    -- ^ No border
  | BorderSolid Number String                     -- ^ width, color (hex)
  | BorderGradientLinear Number String String Number
      -- ^ width, startColor, endColor, angle (degrees)
  | BorderGradientConic Number (Array String)     -- ^ width, colors array
  | BorderGlow Number String Number               -- ^ width, color, blur radius
  | BorderDashed Number String Number Number      -- ^ width, color, dashLength, gapLength
  | BorderAnimatedDash Number String Number       -- ^ width, color, speed (ms per cycle)
  | BorderPulse Number String Number Number       -- ^ width, color, minOpacity, speed
  | BorderRainbow Number Number                   -- ^ width, speed (ms per cycle)

derive instance eqItemBorder :: Eq ItemBorder

instance showItemBorder :: Show ItemBorder where
  show BorderNone = "none"
  show (BorderSolid w _) = "solid:" <> show w <> "px"
  show (BorderGradientLinear w _ _ _) = "gradient-linear:" <> show w <> "px"
  show (BorderGradientConic w _) = "gradient-conic:" <> show w <> "px"
  show (BorderGlow w _ _) = "glow:" <> show w <> "px"
  show (BorderDashed w _ _ _) = "dashed:" <> show w <> "px"
  show (BorderAnimatedDash w _ _) = "animated-dash:" <> show w <> "px"
  show (BorderPulse w _ _ _) = "pulse:" <> show w <> "px"
  show (BorderRainbow w _) = "rainbow:" <> show w <> "px"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create solid border
itemBorder :: Number -> String -> ItemBorder
itemBorder width color = BorderSolid (clampWidth width) color
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w

-- | No border
noItemBorder :: ItemBorder
noItemBorder = BorderNone

-- | Simple solid border
solidBorder :: Number -> String -> ItemBorder
solidBorder = itemBorder

-- | Glowing border effect (neon style)
-- |
-- | - width: Border line width
-- | - color: Glow color (hex)
-- | - blur: Blur radius for glow effect
glowingBorder :: ItemBorder
glowingBorder = BorderGlow 2.0 "#3B82F6" 8.0

-- | Glowing border with custom parameters
glowingBorderWith :: Number -> String -> Number -> ItemBorder
glowingBorderWith width color blur = BorderGlow 
  (clampWidth width) 
  color 
  (clampBlur blur)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampBlur b
      | b < 0.0 = 0.0
      | b > 50.0 = 50.0
      | otherwise = b

-- | Gradient stroke border (linear)
gradientBorder :: ItemBorder
gradientBorder = BorderGradientLinear 2.0 "#3B82F6" "#8B5CF6" 45.0

-- | Gradient border with custom colors and angle
gradientBorderWith :: Number -> String -> String -> Number -> ItemBorder
gradientBorderWith width startColor endColor angle = 
  BorderGradientLinear (clampWidth width) startColor endColor (clampAngle angle)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampAngle a
      | a < 0.0 = 0.0
      | a > 360.0 = 360.0
      | otherwise = a

-- | Animated dash border (marching ants)
animatedDashBorder :: ItemBorder
animatedDashBorder = BorderAnimatedDash 2.0 "#3B82F6" 1000.0

-- | Animated dash border with custom parameters
animatedDashBorderWith :: Number -> String -> Number -> ItemBorder
animatedDashBorderWith width color speed = 
  BorderAnimatedDash (clampWidth width) color (clampSpeed speed)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampSpeed s
      | s < 100.0 = 100.0
      | s > 10000.0 = 10000.0
      | otherwise = s

-- | Dashed border (static)
dashedBorder :: Number -> String -> Number -> Number -> ItemBorder
dashedBorder width color dashLen gapLen = 
  BorderDashed (clampWidth width) color (clampDash dashLen) (clampDash gapLen)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampDash d
      | d < 1.0 = 1.0
      | d > 50.0 = 50.0
      | otherwise = d

-- | Pulsing border (opacity animation)
pulseBorder :: Number -> String -> ItemBorder
pulseBorder width color = BorderPulse width color 0.3 1000.0

-- | Rainbow animated border
rainbowBorder :: Number -> Number -> ItemBorder
rainbowBorder width speed = BorderRainbow (clampWidth width) (clampSpeed speed)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampSpeed s
      | s < 500.0 = 500.0
      | s > 10000.0 = 10000.0
      | otherwise = s
