-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // motion // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect types, enums, and parameters for motion graphics.
-- |
-- | This is the leader module that re-exports all Effects submodules.
-- | Effects are visual filters and transformations applied to layers.
-- | Each effect has parameters that can be animated.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Effects` from the Haskell backend.
-- |
-- | ## Categories
-- |
-- | - Blur/Sharpen: Gaussian, directional, radial blur
-- | - Color Correction: Levels, curves, color balance
-- | - Distort: Warp, displacement, mesh deform
-- | - Generate: Fractal noise, gradients
-- | - Stylize: Glow, shadows, scanlines
-- | - Time: Echo, time displacement
-- |
-- | ## Submodules
-- |
-- | - Effects.Core: Parameter types, effect categories, effect instances
-- | - Effects.Blur: Blur dimension, radial blur type, antialiasing
-- | - Effects.Distortion: Warp styles, displacement maps, edge behavior
-- | - Effects.Glow: Composite modes, falloff, tonemapping, bloom
-- | - Effects.Noise: Fractal types, noise types
-- | - Effects.Time: Echo operators, time resolution
-- | - Effects.Mesh: Pin falloff, turbulent displacement, pinning modes
-- | - Effects.Stylize: Scanlines, dithering, halftone, pixel sorting

module Hydrogen.Schema.Motion.Effects
  ( -- * Re-exports from Core
    module Core
    
    -- * Re-exports from Blur
  , module Blur
  
    -- * Re-exports from Distortion
  , module Distortion
  
    -- * Re-exports from Glow
  , module Glow
  
    -- * Re-exports from Noise
  , module Noise
  
    -- * Re-exports from Time
  , module Time
  
    -- * Re-exports from Mesh
  , module Mesh
  
    -- * Re-exports from Stylize
  , module Stylize
  ) where

import Hydrogen.Schema.Motion.Effects.Core
  ( EffectParameterType(EPTNumber, EPTColor, EPTPoint, EPTPoint3D, EPTAngle, EPTCheckbox, EPTDropdown, EPTLayer, EPTString, EPTCurve, EPTData)
  , allEffectParameterTypes
  , effectParameterTypeToString
  , effectParameterTypeFromString
  , EffectAnimatableType(EATNumber, EATPosition, EATColor, EATEnum, EATVector3)
  , allEffectAnimatableTypes
  , effectAnimatableTypeToString
  , effectAnimatableTypeFromString
  , EffectCategory(ECBlurSharpen, ECColorCorrection, ECDistort, ECGenerate, ECKeying, ECMatte, ECNoiseGrain, ECPerspective, ECStylize, ECTime, ECTransition, ECUtility)
  , allEffectCategories
  , effectCategoryToString
  , effectCategoryFromString
  , EffectPoint2D
  , mkEffectPoint2D
  , EffectPoint3D
  , mkEffectPoint3D
  , EffectRGBA
  , mkEffectRGBA
  , effectRGBAOpaque
  , CurvePoint
  , mkCurvePoint
  , EffectParameterValue(EPVNumber, EPVString, EPVBoolean, EPVPoint2D, EPVPoint3D, EPVColor, EPVCurve, EPVData, EPVNull)
  , EffectDropdownOption
  , EffectParameterDef
  , defaultEffectParameterDef
  , EffectParameter
  , defaultEffectParameter
  , EffectId(EffectId)
  , mkEffectId
  , Effect
  , defaultEffect
  , effectEnabled
  , EffectInstance
  , defaultEffectInstance
  , MeshDeformEffectInstance
  , EffectDefinition
  , EffectCategoryInfo
  ) as Core

import Hydrogen.Schema.Motion.Effects.Blur
  ( BlurDimension(BDHorizontal, BDVertical, BDBoth)
  , allBlurDimensions
  , blurDimensionToString
  , blurDimensionFromString
  , RadialBlurType(RBTSpin, RBTZoom)
  , allRadialBlurTypes
  , radialBlurTypeToString
  , radialBlurTypeFromString
  , AntialiasingQuality(AAQLow, AAQMedium, AAQHigh)
  , allAntialiasingQualities
  , antialiasingQualityToString
  , antialiasingQualityFromString
  ) as Blur

import Hydrogen.Schema.Motion.Effects.Distortion
  ( RampShape(RSLinear, RSRadial)
  , allRampShapes
  , rampShapeToString
  , rampShapeFromString
  , WarpStyle(WSArc, WSArcLower, WSArcUpper, WSArch, WSBulge, WSShellLower, WSShellUpper, WSFlag, WSWave, WSFish, WSRise, WSFisheye, WSInflate, WSSqueeze, WSTwist)
  , allWarpStyles
  , warpStyleToString
  , warpStyleFromString
  , DisplacementMapType(DMTLayer, DMTNoise, DMTGradientH, DMTGradientV, DMTRadial, DMTSineH, DMTSineV, DMTChecker)
  , allDisplacementMapTypes
  , displacementMapTypeToString
  , displacementMapTypeFromString
  , DisplacementChannel(DCRed, DCGreen, DCBlue, DCAlpha, DCLuminance, DCOff)
  , allDisplacementChannels
  , displacementChannelToString
  , displacementChannelFromString
  , EdgeBehavior(EBOff, EBTiles, EBMirror)
  , allEdgeBehaviors
  , edgeBehaviorToString
  , edgeBehaviorFromString
  ) as Distortion

import Hydrogen.Schema.Motion.Effects.Glow
  ( GlowCompositeMode(GCMOnTop, GCMBehind, GCMNone)
  , allGlowCompositeModes
  , glowCompositeModeToString
  , glowCompositeModeFromString
  , GlowColorsMode(GCMOriginal, GCMAB)
  , allGlowColorsModes
  , glowColorsModeToString
  , glowColorsModeFromString
  , ColorLooping(CLNone, CLSawtoothAB, CLSawtoothBA, CLTriangle)
  , allColorLoopings
  , colorLoopingToString
  , colorLoopingFromString
  , FalloffMode(FMInverseSquare, FMGaussian, FMExponential)
  , allFalloffModes
  , falloffModeToString
  , falloffModeFromString
  , TonemapMode(TMNone, TMACES, TMReinhard, TMHable)
  , allTonemapModes
  , tonemapModeToString
  , tonemapModeFromString
  , BloomBlendMode(BBMAdd, BBMScreen, BBMOverlay, BBMSoftLight)
  , allBloomBlendModes
  , bloomBlendModeToString
  , bloomBlendModeFromString
  ) as Glow

import Hydrogen.Schema.Motion.Effects.Noise
  ( FractalType(FTBasic, FTTurbulentBasic, FTSoftLinear, FTTurbulentSoft)
  , allFractalTypes
  , fractalTypeToString
  , fractalTypeFromString
  , NoiseType(NTBlock, NTLinear, NTSoftLinear, NTSpline)
  , allNoiseTypes
  , noiseTypeToString
  , noiseTypeFromString
  ) as Noise

import Hydrogen.Schema.Motion.Effects.Time
  ( EchoOperator(EOAdd, EOScreen, EOMaximum, EOMinimum, EOCompositeBack, EOCompositeFront, EOBlend)
  , allEchoOperators
  , echoOperatorToString
  , echoOperatorFromString
  , TimeResolution(TRFrame, TRHalf, TRQuarter)
  , allTimeResolutions
  , timeResolutionToString
  , timeResolutionFromString
  ) as Time

import Hydrogen.Schema.Motion.Effects.Mesh
  ( PinFalloff(PFInverseDistance, PFRadialBasis)
  , allPinFalloffs
  , pinFalloffToString
  , pinFalloffFromString
  , TurbulentDisplaceType(TDTTurbulent, TDTBulge, TDTTwist, TDTTurbulentSmoother, TDTHorizontal, TDTVertical, TDTCross)
  , allTurbulentDisplaceTypes
  , turbulentDisplaceTypeToString
  , turbulentDisplaceTypeFromString
  , PinningMode(PMNone, PMAll, PMHorizontal, PMVertical)
  , allPinningModes
  , pinningModeToString
  , pinningModeFromString
  ) as Mesh

import Hydrogen.Schema.Motion.Effects.Stylize
  ( ScanlinesDirection(SDHorizontal, SDVertical)
  , allScanlinesDirections
  , scanlinesDirectionToString
  , scanlinesDirectionFromString
  , RGBSplitBlendMode(RSBMScreen, RSBMAdd, RSBMNormal)
  , allRGBSplitBlendModes
  , rgbSplitBlendModeToString
  , rgbSplitBlendModeFromString
  , PixelSortDirection(PSDHorizontal, PSDVertical)
  , allPixelSortDirections
  , pixelSortDirectionToString
  , pixelSortDirectionFromString
  , SortByCriterion(SBCSaturation, SBCBrightness, SBCHue)
  , allSortByCriteria
  , sortByCriterionToString
  , sortByCriterionFromString
  , HalftoneColorMode(HCMGrayscale, HCMRGB, HCMCMYK)
  , allHalftoneColorModes
  , halftoneColorModeToString
  , halftoneColorModeFromString
  , DitherMethod(DMOrdered, DMFloydSteinberg, DMAtkinson)
  , allDitherMethods
  , ditherMethodToString
  , ditherMethodFromString
  , DitherMatrixSize(DMS2x2, DMS4x4, DMS8x8)
  , allDitherMatrixSizes
  , ditherMatrixSizeToString
  , ditherMatrixSizeFromString
  , EffectColorChannel(ECCRGB, ECCRed, ECCGreen, ECCBlue, ECCAlpha)
  , allEffectColorChannels
  , effectColorChannelToString
  , effectColorChannelFromString
  , HSLChannel(HSLMaster, HSLReds, HSLYellows, HSLGreens, HSLCyans, HSLBlues, HSLMagentas)
  , allHSLChannels
  , hslChannelToString
  , hslChannelFromString
  ) as Stylize
