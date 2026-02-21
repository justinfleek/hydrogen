-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // math
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core mathematical functions.
-- |
-- | This module provides pure mathematical operations via FFI to JavaScript's
-- | Math object. These are the foundational operations that Color, Dimension,
-- | and other Schema pillars depend on.
-- |
-- | ## Verification Notes
-- |
-- | The following operations may benefit from Lean4 formal verification:
-- | - Color space conversions (affects accessibility compliance)
-- | - Unit conversions (affects physical accuracy)
-- | - Interpolation functions (affects animation correctness)
-- |
-- | The following are unlikely to need verification:
-- | - CSS output formatting
-- | - Blend modes (creative, not safety-critical)

module Hydrogen.Math.Core
  ( -- * Constants
    pi
  , e
  , tau
  , sqrt2
  , sqrt1_2
  , ln2
  , ln10
  , log2e
  , log10e
  
  -- * Powers & Roots
  , pow
  , sqrt
  , cbrt
  , hypot
  , hypot3
  
  -- * Trigonometry
  , sin
  , cos
  , tan
  , asin
  , acos
  , atan
  , atan2
  , sinh
  , cosh
  , tanh
  , asinh
  , acosh
  , atanh
  
  -- * Exponential
  , exp
  , expm1
  , log
  , log10
  , log2
  , log1p
  
  -- * Rounding
  , floor
  , ceil
  , round
  , trunc
  , fround
  
  -- * Misc
  , abs
  , sign
  , min
  , max
  , minArray
  , maxArray
  , clamp
  
  -- * Special Values
  , isNaN
  , isFinite
  , isInteger
  , infinity
  , negativeInfinity
  
  -- * Interpolation
  , lerp
  , inverseLerp
  , remap
  , smoothstep
  , smootherstep
  
  -- * Angle Conversion
  , degreesToRadians
  , radiansToDegrees
  ) where

import Prelude hiding (min, max)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Pi (ratio of circumference to diameter)
foreign import pi :: Number

-- | Euler's number
foreign import e :: Number

-- | Tau (2 * pi, full circle in radians)
foreign import tau :: Number

-- | Square root of 2
foreign import sqrt2 :: Number

-- | Square root of 1/2
foreign import sqrt1_2 :: Number

-- | Natural logarithm of 2
foreign import ln2 :: Number

-- | Natural logarithm of 10
foreign import ln10 :: Number

-- | Base-2 logarithm of e
foreign import log2e :: Number

-- | Base-10 logarithm of e
foreign import log10e :: Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // powers & roots
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Raise to a power: pow base exponent = base ^ exponent
foreign import pow :: Number -> Number -> Number

-- | Square root
foreign import sqrt :: Number -> Number

-- | Cube root
foreign import cbrt :: Number -> Number

-- | Hypotenuse of 2D vector: sqrt(x^2 + y^2)
foreign import hypot :: Number -> Number -> Number

-- | Hypotenuse of 3D vector: sqrt(x^2 + y^2 + z^2)
foreign import hypot3 :: Number -> Number -> Number -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // trigonometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sine (input in radians)
foreign import sin :: Number -> Number

-- | Cosine (input in radians)
foreign import cos :: Number -> Number

-- | Tangent (input in radians)
foreign import tan :: Number -> Number

-- | Arcsine (output in radians, domain [-1, 1])
foreign import asin :: Number -> Number

-- | Arccosine (output in radians, domain [-1, 1])
foreign import acos :: Number -> Number

-- | Arctangent (output in radians)
foreign import atan :: Number -> Number

-- | Two-argument arctangent: atan2 y x (output in radians)
foreign import atan2 :: Number -> Number -> Number

-- | Hyperbolic sine
foreign import sinh :: Number -> Number

-- | Hyperbolic cosine
foreign import cosh :: Number -> Number

-- | Hyperbolic tangent
foreign import tanh :: Number -> Number

-- | Inverse hyperbolic sine
foreign import asinh :: Number -> Number

-- | Inverse hyperbolic cosine (domain [1, infinity])
foreign import acosh :: Number -> Number

-- | Inverse hyperbolic tangent (domain (-1, 1))
foreign import atanh :: Number -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // exponential
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Exponential: e^x
foreign import exp :: Number -> Number

-- | exp(x) - 1 (more precise for small x)
foreign import expm1 :: Number -> Number

-- | Natural logarithm (base e)
foreign import log :: Number -> Number

-- | Base-10 logarithm
foreign import log10 :: Number -> Number

-- | Base-2 logarithm
foreign import log2 :: Number -> Number

-- | log(1 + x) (more precise for small x)
foreign import log1p :: Number -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // rounding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Round down to nearest integer
foreign import floor :: Number -> Number

-- | Round up to nearest integer
foreign import ceil :: Number -> Number

-- | Round to nearest integer (half away from zero)
foreign import round :: Number -> Number

-- | Truncate toward zero
foreign import trunc :: Number -> Number

-- | Round to nearest 32-bit float
foreign import fround :: Number -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // misc
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Absolute value
foreign import abs :: Number -> Number

-- | Sign: -1, 0, or 1
foreign import sign :: Number -> Number

-- | Minimum of two values
foreign import min :: Number -> Number -> Number

-- | Maximum of two values
foreign import max :: Number -> Number -> Number

-- | Minimum of an array
foreign import minArray :: Array Number -> Number

-- | Maximum of an array
foreign import maxArray :: Array Number -> Number

-- | Clamp value to range [min, max]
foreign import clamp :: Number -> Number -> Number -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // special values
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if value is NaN
foreign import isNaN :: Number -> Boolean

-- | Check if value is finite (not infinite, not NaN)
foreign import isFinite :: Number -> Boolean

-- | Check if value is an integer
foreign import isInteger :: Number -> Boolean

-- | Positive infinity
foreign import infinity :: Number

-- | Negative infinity
foreign import negativeInfinity :: Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation: lerp a b t = a + (b - a) * t
-- | When t=0 returns a, when t=1 returns b
foreign import lerp :: Number -> Number -> Number -> Number

-- | Inverse of lerp: find t such that lerp a b t = v
foreign import inverseLerp :: Number -> Number -> Number -> Number

-- | Remap value from one range to another
-- | remap inMin inMax outMin outMax value
foreign import remap :: Number -> Number -> Number -> Number -> Number -> Number

-- | Smoothstep: cubic Hermite interpolation with zero derivatives at edges
-- | smoothstep edge0 edge1 x
foreign import smoothstep :: Number -> Number -> Number -> Number

-- | Smootherstep: Ken Perlin's improved smoothstep with zero 1st and 2nd derivatives
-- | smootherstep edge0 edge1 x
foreign import smootherstep :: Number -> Number -> Number -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // angle conversion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Convert radians to degrees
radiansToDegrees :: Number -> Number
radiansToDegrees rad = rad * 180.0 / pi
