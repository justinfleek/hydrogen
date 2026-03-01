-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brush // velocity // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Velocity Types — Transfer curves for velocity dynamics.
-- |
-- | ## Design Philosophy
-- |
-- | Velocity curves define how raw stroke speed maps to brush parameter
-- | modulation. Different curves produce different expressive feels:
-- | linear for technical work, soft for natural media, firm for bold strokes.
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Velocity.Types
  ( -- * VelocityCurve ADT
    VelocityCurve
      ( VelocityLinear
      , VelocitySCurve
      , VelocitySoft
      , VelocityFirm
      , VelocityExponential
      , VelocityLogarithmic
      )
  , allVelocityCurves
  , velocityCurveDescription
  , velocityCurveFormula
  , velocityCurveMaxSensitivity
  , velocityCurveDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // velocity curve
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transfer function mapping raw velocity to effective velocity.
-- |
-- | The curve determines how stroke speed translates to parameter changes.
-- | Input is normalized velocity (0-1), output is effective velocity (0-1).
data VelocityCurve
  = VelocityLinear
    -- ^ Direct 1:1 mapping. y = x
  | VelocitySoft
    -- ^ Sensitive to slow movements. y = x^0.5
  | VelocityFirm
    -- ^ Requires fast movement for effect. y = x^2
  | VelocitySCurve
    -- ^ Smooth middle range. y = 3x^2 - 2x^3
  | VelocityLogarithmic
    -- ^ Quick ramp, then plateau. y = log(1+9x)/log(10)
  | VelocityExponential
    -- ^ Slow start, rapid end. y = (e^x - 1)/(e - 1)

derive instance eqVelocityCurve :: Eq VelocityCurve
derive instance ordVelocityCurve :: Ord VelocityCurve

instance showVelocityCurve :: Show VelocityCurve where
  show VelocityLinear = "(VelocityCurve Linear)"
  show VelocitySoft = "(VelocityCurve Soft)"
  show VelocityFirm = "(VelocityCurve Firm)"
  show VelocitySCurve = "(VelocityCurve SCurve)"
  show VelocityLogarithmic = "(VelocityCurve Logarithmic)"
  show VelocityExponential = "(VelocityCurve Exponential)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // enumeration
-- ═════════════════════════════════════════════════════════════════════════════

-- | All velocity curve variants for iteration.
allVelocityCurves :: Array VelocityCurve
allVelocityCurves =
  [ VelocityLinear
  , VelocitySoft
  , VelocityFirm
  , VelocitySCurve
  , VelocityLogarithmic
  , VelocityExponential
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // descriptions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable description of velocity curve behavior.
velocityCurveDescription :: VelocityCurve -> String
velocityCurveDescription VelocityLinear =
  "Direct 1:1 mapping, technical drawing"
velocityCurveDescription VelocitySoft =
  "Sensitive to slow movements, sketching"
velocityCurveDescription VelocityFirm =
  "Requires fast movement, bold strokes"
velocityCurveDescription VelocitySCurve =
  "Smooth middle range, natural feel"
velocityCurveDescription VelocityLogarithmic =
  "Quick ramp then plateau, responsive start"
velocityCurveDescription VelocityExponential =
  "Slow start rapid end, building momentum"

-- | Mathematical formula for velocity curve.
velocityCurveFormula :: VelocityCurve -> String
velocityCurveFormula VelocityLinear = "y = x"
velocityCurveFormula VelocitySoft = "y = x^0.5"
velocityCurveFormula VelocityFirm = "y = x^2"
velocityCurveFormula VelocitySCurve = "y = 3x^2 - 2x^3"
velocityCurveFormula VelocityLogarithmic = "y = log(1+9x)/log(10)"
velocityCurveFormula VelocityExponential = "y = (e^x - 1)/(e - 1)"

-- | Maximum sensitivity (derivative bound) for each velocity curve.
-- |
-- | This bounds how rapidly the effective velocity changes with input.
-- | Important for:
-- | - Smooth stroke rendering (prevents jumpy velocity response)
-- | - Predictable behavior at velocity extremes
-- | - Consistent feel across stroke speeds
-- |
-- | | Curve       | Derivative           | Max on [0,1] or [ε,1] |
-- | |-------------|----------------------|------------------------|
-- | | Linear      | 1                    | 1.0                    |
-- | | Soft        | 1/(2√v)             | 8.0 (at v = 1/256)     |
-- | | Firm        | 2v                   | 2.0                    |
-- | | SCurve      | 6v - 6v²            | 1.5 (at v = 0.5)       |
-- | | Logarithmic | 9/((1+9v)·ln(10))   | 3.91 (at v = 0)        |
-- | | Exponential | e^v/(e-1)           | 1.58 (at v = 1)        |
velocityCurveMaxSensitivity :: VelocityCurve -> Number
velocityCurveMaxSensitivity VelocityLinear = 1.0
velocityCurveMaxSensitivity VelocitySoft = 8.0
velocityCurveMaxSensitivity VelocityFirm = 2.0
velocityCurveMaxSensitivity VelocitySCurve = 1.5
velocityCurveMaxSensitivity VelocityLogarithmic = 3.91
velocityCurveMaxSensitivity VelocityExponential = 1.58

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debug info string for velocity curve.
velocityCurveDebugInfo :: VelocityCurve -> String
velocityCurveDebugInfo curve =
  show curve <> " formula:" <> velocityCurveFormula curve
    <> " maxSensitivity:" <> show (velocityCurveMaxSensitivity curve)
