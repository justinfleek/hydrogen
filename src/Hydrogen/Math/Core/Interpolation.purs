-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // math // core // interpolation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interpolation functions and angle conversion utilities.
-- |
-- | ## Interpolation
-- |
-- | Linear, inverse linear, remap, and smoothstep variants.
-- |
-- | ## Angle Conversion
-- |
-- | Utilities for converting between degrees and radians.

module Hydrogen.Math.Core.Interpolation
  ( -- * Linear Interpolation
    lerp
  , inverseLerp
  , remap
  
  -- * Smooth Interpolation
  , smoothstep
  , smootherstep
  
  -- * Angle Conversion
  , degreesToRadians
  , radiansToDegrees
  ) where

import Prelude

import Hydrogen.Math.Core.Constants (pi)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Local min/max to avoid circular dependency
min :: Number -> Number -> Number
min a b = if a <= b then a else b

max :: Number -> Number -> Number
max a b = if a >= b then a else b

-- | Clamp value to range [minVal, maxVal]
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal x = min maxVal (max minVal x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // linear interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation: lerp a b t = a + (b - a) * t
-- | When t=0 returns a, when t=1 returns b
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Inverse of lerp: find t such that lerp a b t = v
inverseLerp :: Number -> Number -> Number -> Number
inverseLerp a b v = (v - a) / (b - a)

-- | Remap value from one range to another
remap :: Number -> Number -> Number -> Number -> Number -> Number
remap inMin inMax outMin outMax v =
  let t = inverseLerp inMin inMax v
  in lerp outMin outMax t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // smooth interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smoothstep: cubic Hermite interpolation with zero derivatives at edges
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x =
  let t = clamp 0.0 1.0 ((x - edge0) / (edge1 - edge0))
  in t * t * (3.0 - 2.0 * t)

-- | Smootherstep: Ken Perlin's improved smoothstep
-- | Has zero 1st and 2nd derivatives at edges
smootherstep :: Number -> Number -> Number -> Number
smootherstep edge0 edge1 x =
  let t = clamp 0.0 1.0 ((x - edge0) / (edge1 - edge0))
  in t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // angle conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Convert radians to degrees
radiansToDegrees :: Number -> Number
radiansToDegrees rad = rad * 180.0 / pi
