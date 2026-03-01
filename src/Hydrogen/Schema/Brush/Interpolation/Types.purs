-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // brush // interpolation // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interpolation Types — ADTs for stroke interpolation and dab spacing.
-- |
-- | ## Design Philosophy
-- |
-- | Stroke interpolation transforms discrete input points into smooth brush
-- | strokes. The interpolation method determines curve quality, while spacing
-- | mode controls how dabs are placed along the interpolated path.
-- |
-- | ## Interpolation Method
-- |
-- | Curve algorithm for smoothing input points:
-- |
-- | - **Linear**: Straight lines, fastest but angular
-- | - **Catmull**: Catmull-Rom spline, smooth and natural
-- | - **Bezier**: Cubic Bezier, precise control
-- | - **BSpline**: B-spline, smoother than Catmull
-- | - **Hermite**: Hermite spline with velocity tangents
-- |
-- | ## Spacing Mode
-- |
-- | How dabs are distributed along the stroke:
-- |
-- | - **AbsolutePixels**: Fixed pixel distance (e.g., 5px)
-- | - **PercentOfDiameter**: Relative to brush size (e.g., 25%)
-- | - **Adaptive**: Adjusts based on velocity
-- | - **AutoDensity**: Algorithm-determined optimal spacing
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Brush.Interpolation.Types
  ( -- * InterpolationMethod ADT
    InterpolationMethod
      ( Linear
      , Catmull
      , Bezier
      , BSpline
      , Hermite
      )
  , allInterpolationMethods
  , interpolationMethodDescription
  , isSmoothMethod
  , isSplineMethod
  
  -- * SpacingMode ADT
  , SpacingMode
      ( AbsolutePixels
      , PercentOfDiameter
      , Adaptive
      , AutoDensity
      )
  , allSpacingModes
  , spacingModeDescription
  , isRelativeSpacing
  , isDynamicSpacing
  
  -- * Debug & Serialization Helpers
  , interpolationMethodDebugInfo
  , interpolationMethodToId
  , sameInterpolationMethodKind
  , spacingModeDebugInfo
  , spacingModeToId
  , sameSpacingModeKind
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (==)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // interpolation method
-- ═════════════════════════════════════════════════════════════════════════════

-- | Curve algorithm for interpolating input points.
-- |
-- | Different methods produce different stroke characteristics,
-- | trading off between speed, smoothness, and control.
data InterpolationMethod
  = Linear    -- ^ Straight lines between points (fastest, angular)
  | Catmull   -- ^ Catmull-Rom spline (smooth, natural feel)
  | Bezier    -- ^ Cubic Bezier curves (precise control)
  | BSpline   -- ^ B-spline (smoothest, may not pass through points)
  | Hermite   -- ^ Hermite spline (uses velocity for tangents)

derive instance eqInterpolationMethod :: Eq InterpolationMethod
derive instance ordInterpolationMethod :: Ord InterpolationMethod

instance showInterpolationMethod :: Show InterpolationMethod where
  show Linear = "(InterpolationMethod Linear)"
  show Catmull = "(InterpolationMethod Catmull)"
  show Bezier = "(InterpolationMethod Bezier)"
  show BSpline = "(InterpolationMethod BSpline)"
  show Hermite = "(InterpolationMethod Hermite)"

-- | All interpolation method variants.
allInterpolationMethods :: Array InterpolationMethod
allInterpolationMethods =
  [ Linear
  , Catmull
  , Bezier
  , BSpline
  , Hermite
  ]

-- | Human-readable description of each interpolation method.
interpolationMethodDescription :: InterpolationMethod -> String
interpolationMethodDescription Linear =
  "Straight lines between points, fastest but angular"
interpolationMethodDescription Catmull =
  "Catmull-Rom spline, smooth curves passing through points"
interpolationMethodDescription Bezier =
  "Cubic Bezier curves with precise control"
interpolationMethodDescription BSpline =
  "B-spline, smoothest curves but may not pass through points"
interpolationMethodDescription Hermite =
  "Hermite spline using velocity for smooth tangents"

-- | Check if method produces smooth curves (not linear).
isSmoothMethod :: InterpolationMethod -> Boolean
isSmoothMethod Linear = false
isSmoothMethod _ = true

-- | Check if method is a spline algorithm.
isSplineMethod :: InterpolationMethod -> Boolean
isSplineMethod Catmull = true
isSplineMethod BSpline = true
isSplineMethod Hermite = true
isSplineMethod _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spacing mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How dabs are distributed along the interpolated stroke.
-- |
-- | Controls the density and placement of brush stamps.
data SpacingMode
  = AbsolutePixels     -- ^ Fixed pixel distance between dabs
  | PercentOfDiameter  -- ^ Distance as percentage of brush diameter
  | Adaptive           -- ^ Adjusts spacing based on velocity
  | AutoDensity        -- ^ Algorithm determines optimal spacing

derive instance eqSpacingMode :: Eq SpacingMode
derive instance ordSpacingMode :: Ord SpacingMode

instance showSpacingMode :: Show SpacingMode where
  show AbsolutePixels = "(SpacingMode AbsolutePixels)"
  show PercentOfDiameter = "(SpacingMode PercentOfDiameter)"
  show Adaptive = "(SpacingMode Adaptive)"
  show AutoDensity = "(SpacingMode AutoDensity)"

-- | All spacing mode variants.
allSpacingModes :: Array SpacingMode
allSpacingModes =
  [ AbsolutePixels
  , PercentOfDiameter
  , Adaptive
  , AutoDensity
  ]

-- | Human-readable description of each spacing mode.
spacingModeDescription :: SpacingMode -> String
spacingModeDescription AbsolutePixels =
  "Fixed pixel distance between dabs (e.g., 5px)"
spacingModeDescription PercentOfDiameter =
  "Distance as percentage of brush size (e.g., 25%)"
spacingModeDescription Adaptive =
  "Spacing adjusts based on stroke velocity"
spacingModeDescription AutoDensity =
  "Algorithm determines optimal dab density"

-- | Check if spacing is relative to brush size.
isRelativeSpacing :: SpacingMode -> Boolean
isRelativeSpacing PercentOfDiameter = true
isRelativeSpacing _ = false

-- | Check if spacing changes dynamically.
isDynamicSpacing :: SpacingMode -> Boolean
isDynamicSpacing Adaptive = true
isDynamicSpacing AutoDensity = true
isDynamicSpacing _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // debug helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for interpolation method.
interpolationMethodDebugInfo :: InterpolationMethod -> String
interpolationMethodDebugInfo method =
  "InterpolationMethod: " <> interpolationMethodToId method <>
  " — " <> interpolationMethodDescription method

-- | Convert interpolation method to string ID.
interpolationMethodToId :: InterpolationMethod -> String
interpolationMethodToId Linear = "linear"
interpolationMethodToId Catmull = "catmull"
interpolationMethodToId Bezier = "bezier"
interpolationMethodToId BSpline = "b-spline"
interpolationMethodToId Hermite = "hermite"

-- | Check if two methods are the same kind.
sameInterpolationMethodKind :: InterpolationMethod -> InterpolationMethod -> Boolean
sameInterpolationMethodKind a b = interpolationMethodToId a == interpolationMethodToId b

-- | Generate debug info for spacing mode.
spacingModeDebugInfo :: SpacingMode -> String
spacingModeDebugInfo mode =
  "SpacingMode: " <> spacingModeToId mode <>
  " — " <> spacingModeDescription mode

-- | Convert spacing mode to string ID.
spacingModeToId :: SpacingMode -> String
spacingModeToId AbsolutePixels = "pixels"
spacingModeToId PercentOfDiameter = "percent"
spacingModeToId Adaptive = "adaptive"
spacingModeToId AutoDensity = "auto"

-- | Check if two spacing modes are the same kind.
sameSpacingModeKind :: SpacingMode -> SpacingMode -> Boolean
sameSpacingModeKind a b = spacingModeToId a == spacingModeToId b
