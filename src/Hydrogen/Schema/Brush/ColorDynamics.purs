-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brush // colordynamics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Dynamics — How brush color changes during strokes.
-- |
-- | ## Overview
-- |
-- | Color dynamics control the behavior of color as the brush moves. Unlike
-- | a static color selector, color dynamics enable expressive, varied marks
-- | that evoke traditional media where pigment naturally varies.
-- |
-- | ## The Problem with Static Color
-- |
-- | In physical painting, color is never truly static. Pigment concentration
-- | varies along a stroke. Wet paint mixes with existing paint. The brush
-- | picks up color from the canvas. A single brushstroke through two colors
-- | creates a natural gradient.
-- |
-- | Digital tools that apply flat color feel mechanical. Color dynamics
-- | restore the natural variation that makes marks feel alive.
-- |
-- | ## Key Systems
-- |
-- | **Color Source** — Where does color come from?
-- | - Foreground/Background for solid or interpolated colors
-- | - Gradient for spectral rainbow effects
-- | - ColorSet for impressionist palette sampling
-- | - Canvas for wet-in-wet paint pickup
-- |
-- | **HSB Jitter** — Random per-dab variation in Hue, Saturation, Brightness.
-- | Creates the broken color effect of impressionist painting.
-- |
-- | **FG/BG Control** — What drives the position between foreground and
-- | background colors? Pressure creates expressive gradients. Stroke distance
-- | creates linear fades. Random creates chaotic variation.
-- |
-- | **Canvas Mixing** — How much existing canvas color mixes into the brush?
-- | 0% = pure color. 100% = pure wet blending.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: ColorSource, ColorApplication, ColorControl ADTs
-- | - **Atoms**: Bounded numeric parameters (jitters, purity, mixing)
-- | - **Config**: ColorDynamicsConfig record with presets and queries
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Brush.ColorDynamics
-- |   ( ForegroundBackground, ControlPressure, twoToneConfig, hasColorJitter )
-- |
-- | -- Create a two-tone brush controlled by pressure
-- | myConfig = twoToneConfig
-- | hasDynamics = hasColorJitter myConfig  -- false (no HSB jitter)
-- | ```
-- |
-- | ## Relationship to Other Modules
-- |
-- | - **Transfer**: Opacity/flow affect final color appearance
-- | - **Scatter**: Color jitter combines with scatter jitter
-- | - **Wet Media**: Canvas mixing integrates with wet media simulation
-- | - **Color Pillar**: Uses Color pillar atoms for actual color values
-- |
-- | ## Dependencies
-- |
-- | - ColorDynamics.Types
-- | - ColorDynamics.Atoms
-- | - ColorDynamics.Config

module Hydrogen.Schema.Brush.ColorDynamics
  ( -- * Re-exports from ColorDynamics.Types
    module TypesExports
    
    -- * Re-exports from ColorDynamics.Atoms
  , module AtomsExports
    
    -- * Re-exports from ColorDynamics.Mapping
  , module MappingExports
    
    -- * Re-exports from ColorDynamics.Config
  , module ConfigExports
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.ColorDynamics.Types
  ( -- ColorSource ADT
    ColorSource
      ( ForegroundColor
      , BackgroundColor
      , ForegroundBackground
      , GradientSource
      , ColorSetSource
      , CanvasPickup
      , ImageSource
      )
  , allColorSources
  , colorSourceDescription
  , isForegroundBased
  , isGradientBased
  , requiresExternalSource
  
  -- ColorApplication ADT
  , ColorApplication
      ( PerStroke
      , PerDab
      , Continuous
      )
  , allColorApplications
  , colorApplicationDescription
  , isPerDab
  
  -- ColorControl ADT
  , ColorControl
      ( ControlOff
      , ControlPressure
      , ControlTilt
      , ControlVelocity
      , ControlStylusWheel
      , ControlStrokeDistance
      , ControlStrokeTime
      , ControlRandom
      )
  , allColorControls
  , colorControlDescription
  , isInputBased
  , isComputedControl
  ) as TypesExports

import Hydrogen.Schema.Brush.ColorDynamics.Atoms
  ( -- HueJitter (0 to 100)
    HueJitter(HueJitter)
  , hueJitter
  , hueJitterBounds
  , unwrapHueJitter
  , noHueJitter
  , subtleHueJitter
  , moderateHueJitter
  , fullHueJitter
  , hueJitterDebugInfo
  
  -- SaturationJitter (0 to 100)
  , SaturationJitter(SaturationJitter)
  , saturationJitter
  , saturationJitterBounds
  , unwrapSaturationJitter
  , noSaturationJitter
  , subtleSaturationJitter
  , moderateSaturationJitter
  , fullSaturationJitter
  , saturationJitterDebugInfo
  
  -- BrightnessJitter (0 to 100)
  , BrightnessJitter(BrightnessJitter)
  , brightnessJitter
  , brightnessJitterBounds
  , unwrapBrightnessJitter
  , noBrightnessJitter
  , subtleBrightnessJitter
  , moderateBrightnessJitter
  , fullBrightnessJitter
  , brightnessJitterDebugInfo
  
  -- Purity (0 to 100)
  , Purity(Purity)
  , purity
  , purityBounds
  , unwrapPurity
  , grayscalePurity
  , desaturatedPurity
  , standardPurity
  , vibrantPurity
  , purityDebugInfo
  
  -- FGBGPosition (0 to 1)
  , FGBGPosition(FGBGPosition)
  , fgbgPosition
  , fgbgPositionBounds
  , unwrapFGBGPosition
  , atForeground
  , atMidpoint
  , atBackground
  , fgbgPositionDebugInfo
  
  -- MixRatio (0 to 100)
  , MixRatio(MixRatio)
  , mixRatio
  , mixRatioBounds
  , unwrapMixRatio
  , noMixing
  , lightMixing
  , heavyMixing
  , fullMixing
  , mixRatioDebugInfo
  
  -- PaintLoad (0 to 100)
  , PaintLoad(PaintLoad)
  , paintLoad
  , paintLoadBounds
  , unwrapPaintLoad
  , emptyBrush
  , lightLoad
  , standardLoad
  , heavyLoad
  , paintLoadDebugInfo
  
  -- Range queries
  , hasSignificantHueJitter
  , hasSignificantSaturationJitter
  , hasSignificantBrightnessJitter
  , hasAnyColorJitter
  ) as AtomsExports

import Hydrogen.Schema.Brush.ColorDynamics.Mapping
  ( -- FGBGCurve ADT
    FGBGCurve
      ( FGBGLinear
      , FGBGSoft
      , FGBGFirm
      , FGBGSCurve
      , FGBGLogarithmic
      , FGBGExponential
      )
  , allFGBGCurves
  , fgbgCurveDebugInfo
  , fgbgCurveDescription
  , fgbgCurveFormula
  , fgbgCurveMaxSensitivity
  , fgbgCurveToId
  
  -- FGBGMapping Record
  , FGBGMapping
  , defaultFGBGMapping
  , fgbgMappingDebugInfo
  
  -- Presets
  , distanceFGBGMapping
  , dramaticPressureMapping
  , invertedPressureMapping
  , noFGBGMapping
  , pressureFGBGMapping
  , randomFGBGMapping
  , subtlePressureMapping
  , tiltFGBGMapping
  , velocityFGBGMapping
  
  -- Queries
  , fgbgMappingComplexity
  , getPositionRange
  , isFGBGMappingEnabled
  , isInvertedMapping
  
  -- Debug Utilities
  , showWithFGBGMapping
  ) as MappingExports

import Hydrogen.Schema.Brush.ColorDynamics.Config
  ( -- ColorDynamicsConfig record
    ColorDynamicsConfig
  , defaultColorDynamicsConfig
  , colorDynamicsConfigDebugInfo
  
  -- Presets
  , solidColorConfig
  , twoToneConfig
  , rainbowConfig
  , impressionistConfig
  , oilPaintConfig
  , watercolorMixConfig
  , gradientStrokeConfig
  , paletteKnifeConfig
  , dryBrushConfig
  
  -- Queries
  , hasColorJitter
  , hasFGBGDynamics
  , hasCanvasMixing
  , isStaticColor
  , isDynamicColor
  , totalJitterPercent
  , configColorComplexity
  
  -- Debug utilities
  , showWithColorConfig
  ) as ConfigExports
