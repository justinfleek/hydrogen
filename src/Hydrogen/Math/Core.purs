-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // math // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core mathematical functions — PURE PURESCRIPT.
-- |
-- | No JavaScript. No FFI. Pure functional implementations using:
-- | - Taylor series for transcendental functions
-- | - Newton-Raphson iteration for roots
-- | - CORDIC-inspired algorithms where appropriate
-- |
-- | ## Precision
-- |
-- | All Taylor series use sufficient terms for IEEE 754 double precision
-- | (approximately 15-17 significant decimal digits).
-- |
-- | ## Verification
-- |
-- | These implementations have corresponding Lean4 proofs in:
-- | `proofs/Hydrogen/Math/Core.lean`
-- |
-- | ## Submodules
-- |
-- | - `Constants` — Mathematical constants and special values
-- | - `Arithmetic` — Rounding, clamping, powers, and roots
-- | - `Exponential` — Exponential and logarithmic functions
-- | - `Trigonometry` — Standard and hyperbolic trigonometric functions
-- | - `Interpolation` — Interpolation and angle conversion utilities

module Hydrogen.Math.Core
  ( module Constants
  , module Arithmetic
  , module Exponential
  , module Trigonometry
  , module Interpolation
  ) where

import Hydrogen.Math.Core.Constants
  ( e
  , infinity
  , isFinite
  , isInteger
  , isNaN
  , ln10
  , ln2
  , log10e
  , log2e
  , negativeInfinity
  , pi
  , sqrt1_2
  , sqrt2
  , tau
  ) as Constants

import Hydrogen.Math.Core.Arithmetic
  ( abs
  , cbrt
  , ceil
  , clamp
  , floor
  , fround
  , hypot
  , hypot3
  , max
  , maxArray
  , min
  , minArray
  , pow
  , round
  , sign
  , sqrt
  , trunc
  ) as Arithmetic

import Hydrogen.Math.Core.Exponential
  ( exp
  , expm1
  , log
  , log10
  , log1p
  , log2
  ) as Exponential

import Hydrogen.Math.Core.Trigonometry
  ( acos
  , acosh
  , asin
  , asinh
  , atan
  , atan2
  , atanh
  , cos
  , cosh
  , sin
  , sinh
  , tan
  , tanh
  ) as Trigonometry

import Hydrogen.Math.Core.Interpolation
  ( degreesToRadians
  , inverseLerp
  , lerp
  , radiansToDegrees
  , remap
  , smootherstep
  , smoothstep
  ) as Interpolation
