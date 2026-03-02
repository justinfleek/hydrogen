-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // effects // distortion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion Effects — Spatial distortion and warping effects.
-- |
-- | ## Industry Standard
-- |
-- | Implements AE's Distortion effect category:
-- |
-- | - **Warp**: standard warp with 15 presets
-- | - **Displacement Map**: Displace pixels using map image
-- | - **Bezier Warp**: 4-point bezier mesh deformation
-- | - **Bulge**: Spherical bulge distortion
-- | - **Corner Pin**: 4-corner perspective distortion
-- | - **Liquify**: Brush-based deformation
-- | - **Mirror**: Reflection/mirror effects
-- | - **Offset**: Tile/offset image
-- | - **Optics Compensation**: Lens distortion correction
-- | - **Polar Coordinates**: Rectangular to polar conversion
-- | - **Ripple**: Radial wave distortion
-- | - **Spherize**: Wrap around sphere
-- | - **Transform**: Basic spatial transform
-- | - **Turbulent Displace**: Fractal-based displacement
-- | - **Twirl**: Rotational distortion
-- | - **Wave Warp**: Sine wave distortion
-- | - **Bend It**: Bend layer around axis
-- | - **Blobbylize**: Organic blob distortion
-- | - **Flo Motion**: Flow-based motion blur
-- | - **Griddler**: Grid-based distortion
-- | - **Lens Distortion**: Lens distortion effect
-- | - **Page Turn**: Page turn effect
-- | - **Power Pin**: Advanced corner pin
-- | - **Ripple Pulse**: Expanding ripple
-- | - **Slant**: Perspective slant
-- | - **Smear**: Directional smear
-- | - **Split**: Split/duplicate effect
-- | - **Tiler**: Tiling effect
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Distortion.Types`: Core enumerations (RampShape, WarpStyle, etc.)
-- | - `Distortion.Warp`: Warp, Bezier, Bulge, Twirl, Wave effects
-- | - `Distortion.Displacement`: Displacement Map, Turbulent Displace
-- | - `Distortion.Transform`: Corner Pin, Mirror, Offset, Polar, etc.
-- | - `Distortion.Extended`: Extended distortion effects
-- | - `Distortion.Queries`: Query/utility functions
-- |
-- | ## Bounded Properties
-- |
-- | All properties use bounded types for deterministic rendering.

module Hydrogen.Schema.Motion.Effects.Distortion
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Motion.Effects.Distortion.Types
    
    -- * Re-exports from Warp
  , module Hydrogen.Schema.Motion.Effects.Distortion.Warp
  
    -- * Re-exports from Displacement
  , module Hydrogen.Schema.Motion.Effects.Distortion.Displacement
  
    -- * Re-exports from Transform
  , module Hydrogen.Schema.Motion.Effects.Distortion.Transform
  
    -- * Re-exports from Extended
  , module Hydrogen.Schema.Motion.Effects.Distortion.Extended
  
    -- * Re-exports from Queries
  , module Hydrogen.Schema.Motion.Effects.Distortion.Queries
  ) where

import Hydrogen.Schema.Motion.Effects.Distortion.Types
  ( RampShape(..)
  , allRampShapes
  , rampShapeToString
  , rampShapeFromString
  , WarpStyle(..)
  , allWarpStyles
  , warpStyleToString
  , warpStyleFromString
  , DisplacementMapType(..)
  , allDisplacementMapTypes
  , displacementMapTypeToString
  , displacementMapTypeFromString
  , DisplacementChannel(..)
  , allDisplacementChannels
  , displacementChannelToString
  , displacementChannelFromString
  , EdgeBehavior(..)
  , allEdgeBehaviors
  , edgeBehaviorToString
  , edgeBehaviorFromString
  )

import Hydrogen.Schema.Motion.Effects.Distortion.Warp
  ( WarpEffect
  , defaultWarp
  , warpWithStyle
  , warpWithBend
  , BezierWarpEffect
  , defaultBezierWarp
  , BulgeEffect
  , defaultBulge
  , bulgeWithRadius
  , TwirlEffect
  , defaultTwirl
  , twirlWithAngle
  , WaveWarpEffect
  , WaveType(..)
  , defaultWaveWarp
  , waveWarpWithHeight
  , RippleEffect
  , RippleConversion(..)
  , defaultRipple
  , rippleWithWaves
  , SpherizeEffect
  , defaultSpherize
  , spherizeWithRadius
  , LiquifyEffect
  , LiquifyTool(..)
  , defaultLiquify
  , liquifyToolToString
  , rippleConversionToString
  , waveTypeToString
  )

import Hydrogen.Schema.Motion.Effects.Distortion.Displacement
  ( DisplacementMapEffect
  , defaultDisplacementMap
  , displacementMapWithLayer
  , TurbulentDisplaceEffect
  , TurbulentDisplaceType(..)
  , defaultTurbulentDisplace
  , turbulentDisplaceWithAmount
  , turbulentDisplaceTypeToString
  )

import Hydrogen.Schema.Motion.Effects.Distortion.Transform
  ( CornerPinEffect
  , defaultCornerPin
  , MirrorEffect
  , defaultMirror
  , mirrorWithAngle
  , OffsetEffect
  , defaultOffset
  , offsetWithShift
  , OpticsCompensationEffect
  , defaultOpticsCompensation
  , PolarCoordinatesEffect
  , PolarType(..)
  , defaultPolarCoordinates
  , TransformEffect
  , defaultTransform
  , transformWithPosition
  , polarTypeToString
  )

import Hydrogen.Schema.Motion.Effects.Distortion.Extended
  ( BendItEffect
  , defaultBendIt
  , BlobbylizeEffect
  , defaultBlobbylize
  , FloMotionEffect
  , defaultFloMotion
  , GriddlerEffect
  , defaultGriddler
  , LensDistortionEffect
  , defaultLensDistortion
  , PageTurnEffect
  , defaultPageTurn
  , PowerPinEffect
  , defaultPowerPin
  , RipplePulseEffect
  , defaultRipplePulse
  , SlantEffect
  , defaultSlant
  , SmearEffect
  , defaultSmear
  , SplitEffect
  , SplitDirection(..)
  , defaultSplit
  , TilerEffect
  , defaultTiler
  , splitDirectionToString
  )

import Hydrogen.Schema.Motion.Effects.Distortion.Queries
  ( warpEffectName
  , displacementMapEffectName
  , bezierWarpEffectName
  , bulgeEffectName
  , cornerPinEffectName
  , liquifyEffectName
  , mirrorEffectName
  , offsetEffectName
  , opticsCompensationEffectName
  , polarCoordinatesEffectName
  , rippleEffectName
  , spherizeEffectName
  , transformEffectName
  , turbulentDisplaceEffectName
  , twirlEffectName
  , waveWarpEffectName
  , bendItEffectName
  , blobbylizeEffectName
  , floMotionEffectName
  , griddlerEffectName
  , lensDistortionEffectName
  , pageTurnEffectName
  , powerPinEffectName
  , ripplePulseEffectName
  , slantEffectName
  , smearEffectName
  , splitEffectName
  , tilerEffectName
  , describeWarp
  , describeDisplacementMap
  , describeBulge
  , describeTwirl
  , describeWaveWarp
  , describeTurbulentDisplace
  , isWarpBent
  , isDisplacementActive
  , hasBulgeHeight
  , isTwirlSignificant
  , isWaveWarpAnimated
  , isTurbulentDisplaceComplex
  , scaleWarpBend
  , combineBulgeHeights
  , totalDisplacementMagnitude
  , waveWarpIntensity
  , isBulgeExpanding
  , twirlRevolutions
  , offsetTwirlAngle
  , scaleTurbulentAmount
  , displacementDifference
  , classifyWarpIntensity
  , hasTransformChange
  , hasWarpBothDistortions
  )
