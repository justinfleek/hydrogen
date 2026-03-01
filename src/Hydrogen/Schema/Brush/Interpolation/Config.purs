-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // brush // interpolation // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interpolation Configuration — How input points become smooth strokes.
-- |
-- | ## Design Philosophy
-- |
-- | InterpolationConfig brings together curve algorithm, spacing, quality,
-- | and smoothing parameters into a cohesive configuration for stroke
-- | rendering. Different presets balance latency vs. precision.
-- |
-- | ## Key Properties
-- |
-- | - **method**: Curve algorithm (Linear, Catmull, Bezier, BSpline, Hermite)
-- | - **quality**: Subdivision level (1-10)
-- | - **spacingMode**: How dabs are distributed
-- | - **spacingPixels**: Absolute spacing when mode is AbsolutePixels
-- | - **spacingPercent**: Relative spacing when mode is PercentOfDiameter
-- | - **velocityAdjustedSpacing**: Faster strokes = more spacing
-- | - **positionSmoothing**: Input position smoothing (0-1)
-- | - **pressureSmoothing**: Input pressure smoothing (0-1)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Interpolation.Types
-- | - Interpolation.Atoms

module Hydrogen.Schema.Brush.Interpolation.Config
  ( -- * InterpolationConfig Record
    InterpolationConfig
  , defaultInterpolationConfig
  , interpolationConfigDebugInfo
  
  -- * Presets
  , fastSketch
  , smoothPainting
  , precisionDrawing
  , realTimePreview
  , exportQuality
  
  -- * Queries
  , usesSmoothMethod
  , usesDynamicSpacing
  , hasInputSmoothing
  , isHighQuality
  , isLowLatency
  
  -- * Debug Utilities
  , showWithConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (&&)
  , (||)
  , (==)
  , (>=)
  , (<=)
  )

import Hydrogen.Schema.Brush.Interpolation.Types
  ( InterpolationMethod
      ( Linear
      , Catmull
      , BSpline
      )
  , SpacingMode
      ( PercentOfDiameter
      , Adaptive
      , AutoDensity
      )
  , isSmoothMethod
  , isDynamicSpacing
  , interpolationMethodToId
  , spacingModeToId
  )

import Hydrogen.Schema.Brush.Interpolation.Atoms
  ( InterpolationQuality
  , SpacingPixels
  , SpacingPercent
  , PositionSmoothing
  , PressureSmoothing
  , interpolationQuality
  , spacingPixels
  , spacingPercent
  , positionSmoothing
  , pressureSmoothing
  , unwrapInterpolationQuality
  , unwrapSpacingPixels
  , unwrapSpacingPercent
  , unwrapPositionSmoothing
  , unwrapPressureSmoothing
  , lowQuality
  , mediumQuality
  , highQuality
  , maxQuality
  , tightSpacingPixels
  , normalSpacingPixels
  , tightSpacingPercent
  , normalSpacingPercent
  , noPositionSmoothing
  , lightPositionSmoothing
  , heavyPositionSmoothing
  , noPressureSmoothing
  , lightPressureSmoothing
  , heavyPressureSmoothing
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // interpolation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for stroke interpolation.
-- |
-- | ## Field Descriptions
-- |
-- | - `method`: Curve algorithm for smoothing input points
-- | - `quality`: Subdivision level (1=fast, 10=smooth)
-- | - `spacingMode`: How dabs are distributed along the stroke
-- | - `spacingPixels`: Absolute pixel spacing (when mode is AbsolutePixels)
-- | - `spacingPercent`: Percent of diameter spacing (when mode is PercentOfDiameter)
-- | - `velocityAdjustedSpacing`: When true, faster strokes get wider spacing
-- | - `positionSmoothing`: Smooth input position (0=raw, 1=max)
-- | - `pressureSmoothing`: Smooth input pressure (0=raw, 1=max)
type InterpolationConfig =
  { method :: InterpolationMethod
  , quality :: InterpolationQuality
  , spacingMode :: SpacingMode
  , spacingPixels :: SpacingPixels
  , spacingPercent :: SpacingPercent
  , velocityAdjustedSpacing :: Boolean
  , positionSmoothing :: PositionSmoothing
  , pressureSmoothing :: PressureSmoothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // default
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default interpolation configuration: Catmull-Rom, medium quality, 25% spacing.
-- |
-- | Balanced settings suitable for general digital painting.
-- | Uses percent spacing so dab density scales with brush size.
defaultInterpolationConfig :: InterpolationConfig
defaultInterpolationConfig =
  { method: Catmull
  , quality: mediumQuality
  , spacingMode: PercentOfDiameter
  , spacingPixels: normalSpacingPixels
  , spacingPercent: normalSpacingPercent
  , velocityAdjustedSpacing: false
  , positionSmoothing: lightPositionSmoothing
  , pressureSmoothing: lightPressureSmoothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fast sketch: Linear interpolation, low quality, minimal smoothing.
-- |
-- | Optimized for lowest latency during quick sketching.
-- | Raw, immediate response at the cost of smoothness.
fastSketch :: InterpolationConfig
fastSketch =
  { method: Linear
  , quality: lowQuality
  , spacingMode: PercentOfDiameter
  , spacingPixels: normalSpacingPixels
  , spacingPercent: normalSpacingPercent
  , velocityAdjustedSpacing: true
  , positionSmoothing: noPositionSmoothing
  , pressureSmoothing: noPressureSmoothing
  }

-- | Smooth painting: Catmull-Rom, high quality, moderate smoothing.
-- |
-- | Balanced for comfortable painting with clean curves.
-- | Good for digital illustration and general artwork.
smoothPainting :: InterpolationConfig
smoothPainting =
  { method: Catmull
  , quality: highQuality
  , spacingMode: PercentOfDiameter
  , spacingPixels: tightSpacingPixels
  , spacingPercent: tightSpacingPercent
  , velocityAdjustedSpacing: false
  , positionSmoothing: lightPositionSmoothing
  , pressureSmoothing: lightPressureSmoothing
  }

-- | Precision drawing: B-spline, high quality, heavy smoothing.
-- |
-- | Optimized for technical illustration and precise linework.
-- | Higher latency but very clean, controlled strokes.
precisionDrawing :: InterpolationConfig
precisionDrawing =
  { method: BSpline
  , quality: highQuality
  , spacingMode: Adaptive
  , spacingPixels: tightSpacingPixels
  , spacingPercent: spacingPercent 10.0
  , velocityAdjustedSpacing: false
  , positionSmoothing: heavyPositionSmoothing
  , pressureSmoothing: heavyPressureSmoothing
  }

-- | Real-time preview: Linear, lowest quality, no smoothing.
-- |
-- | Maximum performance for live preview during parameter adjustment.
-- | Not suitable for final rendering.
realTimePreview :: InterpolationConfig
realTimePreview =
  { method: Linear
  , quality: interpolationQuality 1
  , spacingMode: AutoDensity
  , spacingPixels: spacingPixels 50.0
  , spacingPercent: spacingPercent 50.0
  , velocityAdjustedSpacing: true
  , positionSmoothing: noPositionSmoothing
  , pressureSmoothing: noPressureSmoothing
  }

-- | Export quality: B-spline, maximum quality, full smoothing.
-- |
-- | Highest quality for final output rendering.
-- | Not suitable for real-time use.
exportQuality :: InterpolationConfig
exportQuality =
  { method: BSpline
  , quality: maxQuality
  , spacingMode: PercentOfDiameter
  , spacingPixels: spacingPixels 2.0
  , spacingPercent: spacingPercent 5.0
  , velocityAdjustedSpacing: false
  , positionSmoothing: heavyPositionSmoothing
  , pressureSmoothing: heavyPressureSmoothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if config uses a smooth (non-linear) interpolation method.
usesSmoothMethod :: InterpolationConfig -> Boolean
usesSmoothMethod c = isSmoothMethod c.method

-- | Check if config uses dynamic spacing (Adaptive or AutoDensity).
usesDynamicSpacing :: InterpolationConfig -> Boolean
usesDynamicSpacing c = isDynamicSpacing c.spacingMode

-- | Check if config has any input smoothing enabled.
hasInputSmoothing :: InterpolationConfig -> Boolean
hasInputSmoothing c =
  unwrapPositionSmoothing c.positionSmoothing >= 0.1 ||
  unwrapPressureSmoothing c.pressureSmoothing >= 0.1

-- | Check if config is high quality (quality >= 7).
isHighQuality :: InterpolationConfig -> Boolean
isHighQuality c = unwrapInterpolationQuality c.quality >= 7

-- | Check if config is optimized for low latency.
-- |
-- | Low latency = linear method + low quality + no smoothing.
isLowLatency :: InterpolationConfig -> Boolean
isLowLatency c =
  interpolationMethodToId c.method == "linear" &&
  unwrapInterpolationQuality c.quality <= 3 &&
  unwrapPositionSmoothing c.positionSmoothing <= 0.1 &&
  unwrapPressureSmoothing c.pressureSmoothing <= 0.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // debug utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info string for InterpolationConfig.
interpolationConfigDebugInfo :: InterpolationConfig -> String
interpolationConfigDebugInfo c =
  "(InterpolationConfig { " <>
  "method: " <> interpolationMethodToId c.method <> ", " <>
  "quality: " <> show (unwrapInterpolationQuality c.quality) <> ", " <>
  "spacing: " <> spacingModeToId c.spacingMode <> " " <>
    show (unwrapSpacingPercent c.spacingPercent) <> "%, " <>
  "velocityAdjust: " <> showBool c.velocityAdjustedSpacing <> ", " <>
  "posSmooth: " <> show (unwrapPositionSmoothing c.positionSmoothing) <> ", " <>
  "presSmooth: " <> show (unwrapPressureSmoothing c.pressureSmoothing) <>
  " })"
  where
    showBool :: Boolean -> String
    showBool b = if b then "on" else "off"

-- | Combine a label with its interpolation config debug info.
showWithConfig :: String -> InterpolationConfig -> String
showWithConfig label config =
  label <> ": " <> interpolationConfigDebugInfo config
