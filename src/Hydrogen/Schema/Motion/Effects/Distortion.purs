-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // motion // effects // distortion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distortion Effects — Spatial distortion and warping effects.
-- |
-- | ## After Effects Parity
-- |
-- | Implements AE's Distortion effect category:
-- |
-- | - **Warp**: Photoshop-style warp with 15 presets
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
-- | - **CC Bend It**: Bend layer around axis
-- | - **CC Blobbylize**: Organic blob distortion
-- | - **CC Flo Motion**: Flow-based motion blur
-- | - **CC Griddler**: Grid-based distortion
-- | - **CC Lens**: Lens distortion
-- | - **CC Page Turn**: Page turn effect
-- | - **CC Power Pin**: Advanced corner pin
-- | - **CC Ripple Pulse**: Expanding ripple
-- | - **CC Slant**: Perspective slant
-- | - **CC Smear**: Directional smear
-- | - **CC Split**: Split/duplicate effect
-- | - **CC Tiler**: Tiling effect
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Distortion.Types`: Core enumerations (RampShape, WarpStyle, etc.)
-- | - `Distortion.Warp`: Warp, Bezier, Bulge, Twirl, Wave effects
-- | - `Distortion.Displacement`: Displacement Map, Turbulent Displace
-- | - `Distortion.Transform`: Corner Pin, Mirror, Offset, Polar, etc.
-- | - `Distortion.CC`: All CC* effects
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
  
    -- * Re-exports from CC
  , module Hydrogen.Schema.Motion.Effects.Distortion.CC
  
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

import Hydrogen.Schema.Motion.Effects.Distortion.CC
  ( CCBendItEffect
  , defaultCCBendIt
  , CCBlobbylizeEffect
  , defaultCCBlobbylize
  , CCFloMotionEffect
  , defaultCCFloMotion
  , CCGriddlerEffect
  , defaultCCGriddler
  , CCLensEffect
  , defaultCCLens
  , CCPageTurnEffect
  , defaultCCPageTurn
  , CCPowerPinEffect
  , defaultCCPowerPin
  , CCRipplePulseEffect
  , defaultCCRipplePulse
  , CCSlantEffect
  , defaultCCSlant
  , CCSmearEffect
  , defaultCCSmear
  , CCSplitEffect
  , CCSplitDirection(..)
  , defaultCCSplit
  , CCTilerEffect
  , defaultCCTiler
  , ccSplitDirectionToString
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
  , ccBendItEffectName
  , ccBlobbylizeEffectName
  , ccFloMotionEffectName
  , ccGriddlerEffectName
  , ccLensEffectName
  , ccPageTurnEffectName
  , ccPowerPinEffectName
  , ccRipplePulseEffectName
  , ccSlantEffectName
  , ccSmearEffectName
  , ccSplitEffectName
  , ccTilerEffectName
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
