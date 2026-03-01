-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brush // wetmedia
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WetMedia — Wet paint simulation for digital painting.
-- |
-- | ## Module Structure
-- |
-- | - **Types**: WetMediaType, WetInteraction ADTs
-- | - **Atoms**: Bounded primitives (Wetness, Viscosity, etc.)
-- | - **Config**: Configuration records and presets
-- | - **Dynamics**: Physics integration for tilt-responsive flow
-- |
-- | ## Physics Integration
-- |
-- | This module integrates with Physics/Force for realistic paint behavior:
-- |   - Tilt your phone → paint slides based on gravity direction
-- |   - Viscosity maps to drag coefficient
-- |   - Wetness affects flow velocity
-- |   - Drying follows exponential decay
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Brush.WetMedia.Types
-- | - Hydrogen.Schema.Brush.WetMedia.Atoms
-- | - Hydrogen.Schema.Brush.WetMedia.Config
-- | - Hydrogen.Schema.Brush.WetMedia.Dynamics

module Hydrogen.Schema.Brush.WetMedia
  ( module Hydrogen.Schema.Brush.WetMedia.Types
  , module Hydrogen.Schema.Brush.WetMedia.Atoms
  , module Hydrogen.Schema.Brush.WetMedia.Config
  , module Hydrogen.Schema.Brush.WetMedia.Dynamics
  ) where

import Hydrogen.Schema.Brush.WetMedia.Types
  ( WetMediaType
      ( Watercolor
      , OilPaint
      , Acrylic
      , Gouache
      , Ink
      , WetIntoWet
      )
  , allWetMediaTypes
  , wetMediaTypeDescription
  , isTransparentMedia
  , isThickMedia
  , defaultDryingRate
  , WetInteraction
      ( WetOnDry
      , WetOnWet
      , WetInWet
      , DryBrush
      )
  , allWetInteractions
  , wetInteractionDescription
  , blendIntensity
  , wetMediaTypeDebugInfo
  , wetMediaTypeToId
  , sameWetMediaTypeKind
  , wetInteractionDebugInfo
  , wetInteractionToId
  )

import Hydrogen.Schema.Brush.WetMedia.Atoms
  ( Wetness
  , mkWetness
  , unwrapWetness
  , wetnessDry
  , wetnessDamp
  , wetnessWet
  , wetnessSoaked
  , wetnessFlooded
  , isWet
  , Viscosity
  , mkViscosity
  , unwrapViscosity
  , viscosityWatery
  , viscosityThin
  , viscosityMedium
  , viscosityThick
  , viscosityPaste
  , isFlowable
  , Dilution
  , mkDilution
  , unwrapDilution
  , dilutionNone
  , dilutionLight
  , dilutionMedium
  , dilutionHeavy
  , dilutionWash
  , PigmentLoad
  , mkPigmentLoad
  , unwrapPigmentLoad
  , pigmentLoadEmpty
  , pigmentLoadLight
  , pigmentLoadMedium
  , pigmentLoadHeavy
  , pigmentLoadSaturated
  , BleedRate
  , mkBleedRate
  , unwrapBleedRate
  , bleedRateNone
  , bleedRateSlow
  , bleedRateMedium
  , bleedRateFast
  , bleedRateAggressive
  , DryingRate
  , mkDryingRate
  , unwrapDryingRate
  , dryingRateNever
  , dryingRateSlow
  , dryingRateMedium
  , dryingRateFast
  , dryingRateInstant
  , Granulation
  , mkGranulation
  , unwrapGranulation
  , granulationNone
  , granulationSubtle
  , granulationMedium
  , granulationStrong
  , granulationExtreme
  , Diffusion
  , mkDiffusion
  , unwrapDiffusion
  , diffusionNone
  , diffusionSubtle
  , diffusionMedium
  , diffusionStrong
  , diffusionMaximum
  , isValidPercent
  )

import Hydrogen.Schema.Brush.WetMedia.Config
  ( WetMediaConfig
  , defaultWetMediaConfig
  , watercolorMediaConfig
  , oilMediaConfig
  , acrylicMediaConfig
  , inkMediaConfig
  , WatercolorConfig
  , defaultWatercolorConfig
  , wetWatercolorConfig
  , dryWatercolorConfig
  , granulatingWatercolorConfig
  , OilPaintConfig
  , defaultOilPaintConfig
  , thinOilConfig
  , impastoOilConfig
  , glazingOilConfig
  , wetMediaConfigDebugInfo
  )

import Hydrogen.Schema.Brush.WetMedia.Dynamics
  ( GravityDirection
  , tiltToGravity
  , gravityFlat
  , gravityTiltedLeft
  , gravityTiltedRight
  , gravityTiltedForward
  , gravityTiltedBack
  , FlowVelocity
  , calculateFlowVelocity
  , flowVelocityMagnitude
  , flowVelocityX
  , flowVelocityY
  , noFlow
  , slowFlow
  , moderateFlow
  , fastFlow
  , applyDrying
  , timeToHalfWetness
  , effectiveDrag
  , canFlow
  , gravityPressure
  )
