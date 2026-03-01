-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // brush // interpolation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Interpolation — Stroke interpolation and dab spacing.
-- |
-- | ## Design Philosophy
-- |
-- | Stroke interpolation transforms discrete input points into smooth brush
-- | strokes. This module provides curve algorithms, spacing modes, quality
-- | settings, and smoothing parameters for stroke rendering.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: InterpolationMethod and SpacingMode ADTs
-- | - **Atoms**: Bounded interpolation parameters (quality, spacing, smoothing)
-- | - **Config**: InterpolationConfig record and presets
-- |
-- | ## Dependencies
-- |
-- | - Interpolation.Types
-- | - Interpolation.Atoms
-- | - Interpolation.Config

module Hydrogen.Schema.Brush.Interpolation
  ( module Types
  , module Atoms
  , module Config
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Interpolation.Types
  ( InterpolationMethod
      ( Linear
      , Catmull
      , Bezier
      , BSpline
      , Hermite
      )
  , SpacingMode
      ( AbsolutePixels
      , PercentOfDiameter
      , Adaptive
      , AutoDensity
      )
  , allInterpolationMethods
  , allSpacingModes
  , interpolationMethodDebugInfo
  , interpolationMethodDescription
  , interpolationMethodToId
  , isDynamicSpacing
  , isRelativeSpacing
  , isSmoothMethod
  , isSplineMethod
  , sameInterpolationMethodKind
  , sameSpacingModeKind
  , spacingModeDebugInfo
  , spacingModeDescription
  , spacingModeToId
  ) as Types

import Hydrogen.Schema.Brush.Interpolation.Atoms
  ( InterpolationQuality(..)
  , PositionSmoothing(..)
  , PressureSmoothing(..)
  , SpacingPercent(..)
  , SpacingPixels(..)
  , heavyPositionSmoothing
  , heavyPressureSmoothing
  , highQuality
  , interpolationQuality
  , interpolationQualityBounds
  , interpolationQualityDebugInfo
  , lightPositionSmoothing
  , lightPressureSmoothing
  , lowQuality
  , maxQuality
  , mediumQuality
  , noPositionSmoothing
  , noPressureSmoothing
  , normalSpacingPercent
  , normalSpacingPixels
  , positionSmoothing
  , positionSmoothingBounds
  , positionSmoothingDebugInfo
  , pressureSmoothing
  , pressureSmoothingBounds
  , pressureSmoothingDebugInfo
  , spacingPercent
  , spacingPercentBounds
  , spacingPercentDebugInfo
  , spacingPixels
  , spacingPixelsBounds
  , spacingPixelsDebugInfo
  , tightSpacingPercent
  , tightSpacingPixels
  , unwrapInterpolationQuality
  , unwrapPositionSmoothing
  , unwrapPressureSmoothing
  , unwrapSpacingPercent
  , unwrapSpacingPixels
  , wideSpacingPercent
  , wideSpacingPixels
  ) as Atoms

import Hydrogen.Schema.Brush.Interpolation.Config
  ( InterpolationConfig
  , defaultInterpolationConfig
  , exportQuality
  , fastSketch
  , hasInputSmoothing
  , interpolationConfigDebugInfo
  , isHighQuality
  , isLowLatency
  , precisionDrawing
  , realTimePreview
  , showWithConfig
  , smoothPainting
  , usesDynamicSpacing
  , usesSmoothMethod
  ) as Config
