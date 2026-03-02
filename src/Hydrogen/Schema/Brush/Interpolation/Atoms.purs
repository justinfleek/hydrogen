-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // brush // interpolation // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interpolation Atoms — Bounded numeric parameters for stroke interpolation.
-- |
-- | ## Design Philosophy
-- |
-- | Stroke interpolation transforms discrete input points into smooth brush
-- | strokes. These atoms control curve resolution, dab spacing, and input
-- | smoothing for latency vs. precision tradeoffs.
-- |
-- | ## Key Properties
-- |
-- | - **InterpolationQuality**: Curve subdivision level (1-10)
-- | - **SpacingPixels**: Absolute pixel distance between dabs (1-1000)
-- | - **SpacingPercent**: Dab spacing as percent of brush diameter (1-1000)
-- | - **PositionSmoothing**: Input position smoothing amount (0-1)
-- | - **PressureSmoothing**: Input pressure smoothing amount (0-1)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Interpolation.Atoms
  ( -- * InterpolationQuality (1 to 10)
    InterpolationQuality(InterpolationQuality)
  , interpolationQuality
  , interpolationQualityBounds
  , unwrapInterpolationQuality
  , lowQuality
  , mediumQuality
  , highQuality
  , maxQuality
  , interpolationQualityDebugInfo
  
  -- * SpacingPixels (1 to 1000)
  , SpacingPixels(SpacingPixels)
  , spacingPixels
  , spacingPixelsBounds
  , unwrapSpacingPixels
  , tightSpacingPixels
  , normalSpacingPixels
  , wideSpacingPixels
  , spacingPixelsDebugInfo
  
  -- * SpacingPercent (1 to 1000)
  , SpacingPercent(SpacingPercent)
  , spacingPercent
  , spacingPercentBounds
  , unwrapSpacingPercent
  , tightSpacingPercent
  , normalSpacingPercent
  , wideSpacingPercent
  , spacingPercentDebugInfo
  
  -- * PositionSmoothing (0 to 1)
  , PositionSmoothing(PositionSmoothing)
  , positionSmoothing
  , positionSmoothingBounds
  , unwrapPositionSmoothing
  , noPositionSmoothing
  , lightPositionSmoothing
  , heavyPositionSmoothing
  , positionSmoothingDebugInfo
  
  -- * PressureSmoothing (0 to 1)
  , PressureSmoothing(PressureSmoothing)
  , pressureSmoothing
  , pressureSmoothingBounds
  , unwrapPressureSmoothing
  , noPressureSmoothing
  , lightPressureSmoothing
  , heavyPressureSmoothing
  , pressureSmoothingDebugInfo
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

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // interpolation quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interpolation quality level (1 to 10).
-- |
-- | Controls curve subdivision for spline interpolation. Higher values
-- | produce smoother curves but require more computation.
-- |
-- | ## Quality Levels
-- |
-- | - 1: No subdivision, fast preview
-- | - 3: Low subdivision, real-time sketching
-- | - 5: Medium, general painting
-- | - 8: High, detailed illustration
-- | - 10: Maximum, export quality
newtype InterpolationQuality = InterpolationQuality Int

derive instance eqInterpolationQuality :: Eq InterpolationQuality
derive instance ordInterpolationQuality :: Ord InterpolationQuality

instance showInterpolationQuality :: Show InterpolationQuality where
  show (InterpolationQuality q) = "(InterpolationQuality " <> show q <> ")"

-- | Bounded specification for InterpolationQuality.
interpolationQualityBounds :: Bounded.IntBounds
interpolationQualityBounds = Bounded.intBounds 1 10 Bounded.Clamps
  "interpolationQuality" "Curve subdivision level (1=fast, 10=smooth)"

-- | Create an InterpolationQuality value (clamped to 1-10).
interpolationQuality :: Int -> InterpolationQuality
interpolationQuality n = InterpolationQuality (Bounded.clampInt 1 10 n)

-- | Extract the raw InterpolationQuality value.
unwrapInterpolationQuality :: InterpolationQuality -> Int
unwrapInterpolationQuality (InterpolationQuality q) = q

-- | Low quality (1) — fast preview, no subdivision.
lowQuality :: InterpolationQuality
lowQuality = InterpolationQuality 1

-- | Medium quality (5) — balanced for general painting.
mediumQuality :: InterpolationQuality
mediumQuality = InterpolationQuality 5

-- | High quality (8) — detailed illustration.
highQuality :: InterpolationQuality
highQuality = InterpolationQuality 8

-- | Maximum quality (10) — export-grade smoothness.
maxQuality :: InterpolationQuality
maxQuality = InterpolationQuality 10

-- | Debug info string for InterpolationQuality.
interpolationQualityDebugInfo :: InterpolationQuality -> String
interpolationQualityDebugInfo q = 
  show q <> " subdivisions:" <> show (unwrapInterpolationQuality q)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // spacing pixels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing between dabs in pixels (1 to 1000).
-- |
-- | Absolute pixel distance between brush stamps along the stroke path.
-- | Used when SpacingMode is AbsolutePixels.
-- |
-- | ## Spacing Effects
-- |
-- | - 1-5px: Continuous stroke, no gaps
-- | - 5-20px: Visible but overlapping dabs
-- | - 20-100px: Spaced stamps, spray effect
-- | - 100+px: Scattered placement
newtype SpacingPixels = SpacingPixels Number

derive instance eqSpacingPixels :: Eq SpacingPixels
derive instance ordSpacingPixels :: Ord SpacingPixels

instance showSpacingPixels :: Show SpacingPixels where
  show (SpacingPixels s) = "(SpacingPixels " <> show s <> "px)"

-- | Bounded specification for SpacingPixels.
spacingPixelsBounds :: Bounded.NumberBounds
spacingPixelsBounds = Bounded.numberBounds 1.0 1000.0 Bounded.Clamps
  "spacingPixels" "Absolute dab spacing in pixels (1-1000)"

-- | Create a SpacingPixels value (clamped to 1-1000).
spacingPixels :: Number -> SpacingPixels
spacingPixels n = SpacingPixels (Bounded.clampNumber 1.0 1000.0 n)

-- | Extract the raw SpacingPixels value.
unwrapSpacingPixels :: SpacingPixels -> Number
unwrapSpacingPixels (SpacingPixels s) = s

-- | Tight spacing (5px) — continuous smooth strokes.
tightSpacingPixels :: SpacingPixels
tightSpacingPixels = SpacingPixels 5.0

-- | Normal spacing (25px) — balanced coverage.
normalSpacingPixels :: SpacingPixels
normalSpacingPixels = SpacingPixels 25.0

-- | Wide spacing (100px) — visible individual dabs.
wideSpacingPixels :: SpacingPixels
wideSpacingPixels = SpacingPixels 100.0

-- | Debug info string for SpacingPixels.
spacingPixelsDebugInfo :: SpacingPixels -> String
spacingPixelsDebugInfo s = show s <> " distance:" <> show (unwrapSpacingPixels s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // spacing percent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing between dabs as percent of brush diameter (1 to 1000).
-- |
-- | Relative spacing that scales with brush size. Used when SpacingMode
-- | is PercentOfDiameter.
-- |
-- | ## Spacing Effects
-- |
-- | - 1-10%: Heavy overlap, continuous coverage
-- | - 25%: Standard brush behavior (industry default)
-- | - 50-100%: Light overlap, visible texture
-- | - 100%+: Gaps between dabs
newtype SpacingPercent = SpacingPercent Number

derive instance eqSpacingPercent :: Eq SpacingPercent
derive instance ordSpacingPercent :: Ord SpacingPercent

instance showSpacingPercent :: Show SpacingPercent where
  show (SpacingPercent s) = "(SpacingPercent " <> show s <> "%)"

-- | Bounded specification for SpacingPercent.
spacingPercentBounds :: Bounded.NumberBounds
spacingPercentBounds = Bounded.numberBounds 1.0 1000.0 Bounded.Clamps
  "spacingPercent" "Dab spacing as percent of diameter (1-1000)"

-- | Create a SpacingPercent value (clamped to 1-1000).
spacingPercent :: Number -> SpacingPercent
spacingPercent n = SpacingPercent (Bounded.clampNumber 1.0 1000.0 n)

-- | Extract the raw SpacingPercent value.
unwrapSpacingPercent :: SpacingPercent -> Number
unwrapSpacingPercent (SpacingPercent s) = s

-- | Tight spacing (5%) — heavy overlap, airbrush style.
tightSpacingPercent :: SpacingPercent
tightSpacingPercent = SpacingPercent 5.0

-- | Normal spacing (25%) — standard brush behavior.
normalSpacingPercent :: SpacingPercent
normalSpacingPercent = SpacingPercent 25.0

-- | Wide spacing (100%) — no overlap, visible dabs.
wideSpacingPercent :: SpacingPercent
wideSpacingPercent = SpacingPercent 100.0

-- | Debug info string for SpacingPercent.
spacingPercentDebugInfo :: SpacingPercent -> String
spacingPercentDebugInfo s = show s <> " ratio:" <> show (unwrapSpacingPercent s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // position smoothing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position input smoothing amount (0 to 1).
-- |
-- | Controls how much to smooth the input cursor position. Higher values
-- | reduce jitter but increase latency.
-- |
-- | ## Smoothing Effects
-- |
-- | - 0.0: Raw input, no smoothing, lowest latency
-- | - 0.3: Light smoothing, natural feel
-- | - 0.6: Moderate smoothing, cleaner curves
-- | - 1.0: Maximum smoothing, very deliberate strokes
newtype PositionSmoothing = PositionSmoothing Number

derive instance eqPositionSmoothing :: Eq PositionSmoothing
derive instance ordPositionSmoothing :: Ord PositionSmoothing

instance showPositionSmoothing :: Show PositionSmoothing where
  show (PositionSmoothing s) = "(PositionSmoothing " <> show s <> ")"

-- | Bounded specification for PositionSmoothing.
positionSmoothingBounds :: Bounded.NumberBounds
positionSmoothingBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "positionSmoothing" "Position input smoothing amount (0=raw, 1=max)"

-- | Create a PositionSmoothing value (clamped to 0-1).
positionSmoothing :: Number -> PositionSmoothing
positionSmoothing n = PositionSmoothing (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw PositionSmoothing value.
unwrapPositionSmoothing :: PositionSmoothing -> Number
unwrapPositionSmoothing (PositionSmoothing s) = s

-- | No position smoothing (0) — raw input.
noPositionSmoothing :: PositionSmoothing
noPositionSmoothing = PositionSmoothing 0.0

-- | Light position smoothing (0.3) — natural feel.
lightPositionSmoothing :: PositionSmoothing
lightPositionSmoothing = PositionSmoothing 0.3

-- | Heavy position smoothing (0.8) — deliberate strokes.
heavyPositionSmoothing :: PositionSmoothing
heavyPositionSmoothing = PositionSmoothing 0.8

-- | Debug info string for PositionSmoothing.
positionSmoothingDebugInfo :: PositionSmoothing -> String
positionSmoothingDebugInfo s = show s <> " amount:" <> show (unwrapPositionSmoothing s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // pressure smoothing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pressure input smoothing amount (0 to 1).
-- |
-- | Controls how much to smooth the input pressure. Higher values reduce
-- | pressure jitter but delay brush size/opacity response.
-- |
-- | ## Smoothing Effects
-- |
-- | - 0.0: Raw pressure, immediate response
-- | - 0.3: Light smoothing, reduces micro-jitter
-- | - 0.6: Moderate smoothing, consistent pressure feel
-- | - 1.0: Maximum smoothing, very gradual pressure changes
newtype PressureSmoothing = PressureSmoothing Number

derive instance eqPressureSmoothing :: Eq PressureSmoothing
derive instance ordPressureSmoothing :: Ord PressureSmoothing

instance showPressureSmoothing :: Show PressureSmoothing where
  show (PressureSmoothing s) = "(PressureSmoothing " <> show s <> ")"

-- | Bounded specification for PressureSmoothing.
pressureSmoothingBounds :: Bounded.NumberBounds
pressureSmoothingBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "pressureSmoothing" "Pressure input smoothing amount (0=raw, 1=max)"

-- | Create a PressureSmoothing value (clamped to 0-1).
pressureSmoothing :: Number -> PressureSmoothing
pressureSmoothing n = PressureSmoothing (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw PressureSmoothing value.
unwrapPressureSmoothing :: PressureSmoothing -> Number
unwrapPressureSmoothing (PressureSmoothing s) = s

-- | No pressure smoothing (0) — raw pressure input.
noPressureSmoothing :: PressureSmoothing
noPressureSmoothing = PressureSmoothing 0.0

-- | Light pressure smoothing (0.3) — reduces micro-jitter.
lightPressureSmoothing :: PressureSmoothing
lightPressureSmoothing = PressureSmoothing 0.3

-- | Heavy pressure smoothing (0.8) — consistent pressure feel.
heavyPressureSmoothing :: PressureSmoothing
heavyPressureSmoothing = PressureSmoothing 0.8

-- | Debug info string for PressureSmoothing.
pressureSmoothingDebugInfo :: PressureSmoothing -> String
pressureSmoothingDebugInfo s = show s <> " amount:" <> show (unwrapPressureSmoothing s)
