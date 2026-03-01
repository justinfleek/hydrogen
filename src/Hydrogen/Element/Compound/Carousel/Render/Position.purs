-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // element // carousel // render // position
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Position — Mathematical position calculations for animations.
-- |
-- | ## Design Philosophy
-- |
-- | Position functions provide mathematical utilities for computing slide
-- | positions in various coordinate systems. These are pure functions that
-- | can be composed for complex animations.
-- |
-- | ## Position Types
-- |
-- | - wavePosition: Oscillating sine wave motion
-- | - circularPosition: Points on a circle (for carousel layouts)
-- | - easeOutPosition: Deceleration curves
-- |
-- | ## Dependencies
-- |
-- | - Render.Layout (sin, cos, abs)
-- | - Render.Effects (pow)

module Hydrogen.Element.Compound.Carousel.Render.Position
  ( -- * Wave Motion
    wavePosition
  
  -- * Circular Motion
  , circularPosition
  
  -- * Easing
  , easeOutPosition
  
  -- * Distance
  , positionDistance
  
  -- * Utility
  , defaultCase
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (*)
  , (-)
  , (+)
  , (>)
  , (<)
  , otherwise
  )

import Hydrogen.Element.Compound.Carousel.Render.Layout (sin, cos, abs)
import Hydrogen.Element.Compound.Carousel.Render.Effects (pow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // wave motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate a wave-based position offset for smooth oscillating effects
-- | Uses sine wave for natural motion. Returns offset in range [-amplitude, amplitude]
-- |
-- | Parameters:
-- | - progress: Current animation progress (0.0 to 1.0)
-- | - amplitude: Maximum displacement
-- | - frequency: Number of oscillations per unit progress
wavePosition :: Number -> Number -> Number -> Number
wavePosition progress amplitude frequency =
  let angle = progress * frequency * 2.0 * pi
  in amplitude * sin angle
  where
    pi = 3.14159265358979

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // circular motion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate position on a circle given angle and radius
-- | Returns {x, y} coordinates for circular carousel layouts
-- |
-- | Parameters:
-- | - angle: Angle in radians (0 = right, pi/2 = top)
-- | - radius: Distance from center
circularPosition :: Number -> Number -> { x :: Number, y :: Number }
circularPosition angle radius =
  { x: radius * cos angle
  , y: radius * sin angle
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply ease-out curve to a progress value using power function
-- | Higher power = more dramatic ease-out (starts fast, ends slow)
-- |
-- | Parameters:
-- | - progress: Input progress (0.0 to 1.0, clamped)
-- | - power: Exponent for the curve (2.0 = quadratic, 3.0 = cubic)
-- |
-- | Formula: 1 - (1 - p)^power
easeOutPosition :: Number -> Number -> Number
easeOutPosition progress power =
  let 
    -- Clamp progress to [0, 1]
    p = if progress < 0.0 then 0.0
        else if progress > 1.0 then 1.0
        else progress
    -- Ease-out: 1 - (1 - p)^power
    inverted = 1.0 - p
    eased = 1.0 - pow inverted power
  in eased

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate absolute distance for position comparisons
-- | Used in visibility and effect calculations
positionDistance :: Number -> Number -> Number
positionDistance a b = abs (a - b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default case helper for guard expressions
-- | Used in pattern guards as the final fallback
-- |
-- | Example:
-- | ```
-- | result = foo
-- |   | condition1 = value1
-- |   | condition2 = value2
-- |   | defaultCase true = fallback
-- | ```
defaultCase :: forall a. a -> a
defaultCase x = if otherwise then x else x
