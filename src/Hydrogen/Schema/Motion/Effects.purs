-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // motion // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Effect types, enums, and parameters for motion graphics.
-- |
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

module Hydrogen.Schema.Motion.Effects
  ( -- * Effect Parameter Type
    EffectParameterType(..)
  , effectParameterTypeToString
  , effectParameterTypeFromString
  
  , EffectAnimatableType(..)
  , effectAnimatableTypeToString
  , effectAnimatableTypeFromString
  
  -- * Blur Enums
  , BlurDimension(..)
  , blurDimensionToString
  , blurDimensionFromString
  
  , RadialBlurType(..)
  , radialBlurTypeToString
  , radialBlurTypeFromString
  
  , AntialiasingQuality(..)
  , antialiasingQualityToString
  , antialiasingQualityFromString
  
  -- * Distortion Enums
  , RampShape(..)
  , rampShapeToString
  , rampShapeFromString
  
  , WarpStyle(..)
  , warpStyleToString
  , warpStyleFromString
  
  , DisplacementMapType(..)
  , displacementMapTypeToString
  , displacementMapTypeFromString
  
  , DisplacementChannel(..)
  , displacementChannelToString
  , displacementChannelFromString
  
  , EdgeBehavior(..)
  , edgeBehaviorToString
  , edgeBehaviorFromString
  
  -- * Glow Enums
  , GlowCompositeMode(..)
  , glowCompositeModeToString
  , glowCompositeModeFromString
  
  , GlowColorsMode(..)
  , glowColorsModeToString
  , glowColorsModeFromString
  
  , ColorLooping(..)
  , colorLoopingToString
  , colorLoopingFromString
  
  , FalloffMode(..)
  , falloffModeToString
  , falloffModeFromString
  
  , TonemapMode(..)
  , tonemapModeToString
  , tonemapModeFromString
  
  , BloomBlendMode(..)
  , bloomBlendModeToString
  , bloomBlendModeFromString
  
  -- * Noise Enums
  , FractalType(..)
  , fractalTypeToString
  , fractalTypeFromString
  
  , NoiseType(..)
  , noiseTypeToString
  , noiseTypeFromString
  
  -- * Time Enums
  , EchoOperator(..)
  , echoOperatorToString
  , echoOperatorFromString
  
  , TimeResolution(..)
  , timeResolutionToString
  , timeResolutionFromString
  
  -- * Mesh Enums
  , PinFalloff(..)
  , pinFalloffToString
  , pinFalloffFromString
  
  , TurbulentDisplaceType(..)
  , turbulentDisplaceTypeToString
  , turbulentDisplaceTypeFromString
  
  , PinningMode(..)
  , pinningModeToString
  , pinningModeFromString
  
  -- * Stylize Enums
  , ScanlinesDirection(..)
  , scanlinesDirectionToString
  , scanlinesDirectionFromString
  
  , RGBSplitBlendMode(..)
  , rgbSplitBlendModeToString
  , rgbSplitBlendModeFromString
  
  , PixelSortDirection(..)
  , pixelSortDirectionToString
  , pixelSortDirectionFromString
  
  , SortByCriterion(..)
  , sortByCriterionToString
  , sortByCriterionFromString
  
  , HalftoneColorMode(..)
  , halftoneColorModeToString
  , halftoneColorModeFromString
  
  , DitherMethod(..)
  , ditherMethodToString
  , ditherMethodFromString
  
  , DitherMatrixSize(..)
  , ditherMatrixSizeToString
  , ditherMatrixSizeFromString
  
  , EffectColorChannel(..)
  , effectColorChannelToString
  , effectColorChannelFromString
  
  , HSLChannel(..)
  , hslChannelToString
  , hslChannelFromString
  
  -- * Effect Category
  , EffectCategory(..)
  , effectCategoryToString
  , effectCategoryFromString
  
  -- * Parameter Types
  , EffectPoint2D(..)
  , mkEffectPoint2D
  
  , EffectPoint3D(..)
  , mkEffectPoint3D
  
  , EffectRGBA(..)
  , mkEffectRGBA
  , effectRGBAOpaque
  
  , CurvePoint(..)
  , mkCurvePoint
  
  , EffectParameterValue(..)
  
  , EffectDropdownOption(..)
  
  , EffectParameterDef(..)
  , defaultEffectParameterDef
  
  , EffectParameter(..)
  , defaultEffectParameter
  
  -- * Effect Types
  , EffectId(..)
  , mkEffectId
  
  , Effect(..)
  , defaultEffect
  , effectEnabled
  
  , EffectInstance(..)
  , defaultEffectInstance
  
  , MeshDeformEffectInstance(..)
  
  , EffectDefinition(..)
  
  , EffectCategoryInfo(..)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.MeshWarp (WarpPin)
import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // effect // parameter // type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of parameter an effect can have.
data EffectParameterType
  = EPTNumber      -- ^ Numeric value
  | EPTColor       -- ^ RGBA color
  | EPTPoint       -- ^ 2D point
  | EPTPoint3D     -- ^ 3D point
  | EPTAngle       -- ^ Angle in degrees
  | EPTCheckbox    -- ^ Boolean toggle
  | EPTDropdown    -- ^ Selection from options
  | EPTLayer       -- ^ Reference to another layer
  | EPTString      -- ^ Text value
  | EPTCurve       -- ^ Bezier curve
  | EPTData        -- ^ JSON-encoded data

derive instance eqEffectParameterType :: Eq EffectParameterType
derive instance ordEffectParameterType :: Ord EffectParameterType

instance showEffectParameterType :: Show EffectParameterType where
  show EPTNumber = "EPTNumber"
  show EPTColor = "EPTColor"
  show EPTPoint = "EPTPoint"
  show EPTPoint3D = "EPTPoint3D"
  show EPTAngle = "EPTAngle"
  show EPTCheckbox = "EPTCheckbox"
  show EPTDropdown = "EPTDropdown"
  show EPTLayer = "EPTLayer"
  show EPTString = "EPTString"
  show EPTCurve = "EPTCurve"
  show EPTData = "EPTData"

effectParameterTypeToString :: EffectParameterType -> String
effectParameterTypeToString EPTNumber = "number"
effectParameterTypeToString EPTColor = "color"
effectParameterTypeToString EPTPoint = "point"
effectParameterTypeToString EPTPoint3D = "point3d"
effectParameterTypeToString EPTAngle = "angle"
effectParameterTypeToString EPTCheckbox = "checkbox"
effectParameterTypeToString EPTDropdown = "dropdown"
effectParameterTypeToString EPTLayer = "layer"
effectParameterTypeToString EPTString = "string"
effectParameterTypeToString EPTCurve = "curve"
effectParameterTypeToString EPTData = "data"

effectParameterTypeFromString :: String -> Maybe EffectParameterType
effectParameterTypeFromString "number" = Just EPTNumber
effectParameterTypeFromString "color" = Just EPTColor
effectParameterTypeFromString "point" = Just EPTPoint
effectParameterTypeFromString "point3d" = Just EPTPoint3D
effectParameterTypeFromString "angle" = Just EPTAngle
effectParameterTypeFromString "checkbox" = Just EPTCheckbox
effectParameterTypeFromString "dropdown" = Just EPTDropdown
effectParameterTypeFromString "layer" = Just EPTLayer
effectParameterTypeFromString "string" = Just EPTString
effectParameterTypeFromString "curve" = Just EPTCurve
effectParameterTypeFromString "data" = Just EPTData
effectParameterTypeFromString _ = Nothing

-- | Type of animatable value for effects.
data EffectAnimatableType
  = EATNumber     -- ^ Scalar number
  | EATPosition   -- ^ 2D/3D position
  | EATColor      -- ^ Color value
  | EATEnum       -- ^ Enumerated value
  | EATVector3    -- ^ 3D vector

derive instance eqEffectAnimatableType :: Eq EffectAnimatableType
derive instance ordEffectAnimatableType :: Ord EffectAnimatableType

instance showEffectAnimatableType :: Show EffectAnimatableType where
  show EATNumber = "EATNumber"
  show EATPosition = "EATPosition"
  show EATColor = "EATColor"
  show EATEnum = "EATEnum"
  show EATVector3 = "EATVector3"

effectAnimatableTypeToString :: EffectAnimatableType -> String
effectAnimatableTypeToString EATNumber = "number"
effectAnimatableTypeToString EATPosition = "position"
effectAnimatableTypeToString EATColor = "color"
effectAnimatableTypeToString EATEnum = "enum"
effectAnimatableTypeToString EATVector3 = "vector3"

effectAnimatableTypeFromString :: String -> Maybe EffectAnimatableType
effectAnimatableTypeFromString "number" = Just EATNumber
effectAnimatableTypeFromString "position" = Just EATPosition
effectAnimatableTypeFromString "color" = Just EATColor
effectAnimatableTypeFromString "enum" = Just EATEnum
effectAnimatableTypeFromString "vector3" = Just EATVector3
effectAnimatableTypeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // blur // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction of blur effect.
data BlurDimension
  = BDHorizontal  -- ^ Blur only horizontally
  | BDVertical    -- ^ Blur only vertically
  | BDBoth        -- ^ Blur in both directions

derive instance eqBlurDimension :: Eq BlurDimension
derive instance ordBlurDimension :: Ord BlurDimension

instance showBlurDimension :: Show BlurDimension where
  show BDHorizontal = "BDHorizontal"
  show BDVertical = "BDVertical"
  show BDBoth = "BDBoth"

blurDimensionToString :: BlurDimension -> String
blurDimensionToString BDHorizontal = "horizontal"
blurDimensionToString BDVertical = "vertical"
blurDimensionToString BDBoth = "both"

blurDimensionFromString :: String -> Maybe BlurDimension
blurDimensionFromString "horizontal" = Just BDHorizontal
blurDimensionFromString "vertical" = Just BDVertical
blurDimensionFromString "both" = Just BDBoth
blurDimensionFromString _ = Nothing

-- | Type of radial blur.
data RadialBlurType
  = RBTSpin   -- ^ Rotational blur around center
  | RBTZoom   -- ^ Zoom blur from center

derive instance eqRadialBlurType :: Eq RadialBlurType
derive instance ordRadialBlurType :: Ord RadialBlurType

instance showRadialBlurType :: Show RadialBlurType where
  show RBTSpin = "RBTSpin"
  show RBTZoom = "RBTZoom"

radialBlurTypeToString :: RadialBlurType -> String
radialBlurTypeToString RBTSpin = "spin"
radialBlurTypeToString RBTZoom = "zoom"

radialBlurTypeFromString :: String -> Maybe RadialBlurType
radialBlurTypeFromString "spin" = Just RBTSpin
radialBlurTypeFromString "zoom" = Just RBTZoom
radialBlurTypeFromString _ = Nothing

-- | Antialiasing quality level.
data AntialiasingQuality
  = AAQLow     -- ^ Fast, lower quality
  | AAQMedium  -- ^ Balanced
  | AAQHigh    -- ^ Best quality, slower

derive instance eqAntialiasingQuality :: Eq AntialiasingQuality
derive instance ordAntialiasingQuality :: Ord AntialiasingQuality

instance showAntialiasingQuality :: Show AntialiasingQuality where
  show AAQLow = "AAQLow"
  show AAQMedium = "AAQMedium"
  show AAQHigh = "AAQHigh"

antialiasingQualityToString :: AntialiasingQuality -> String
antialiasingQualityToString AAQLow = "low"
antialiasingQualityToString AAQMedium = "medium"
antialiasingQualityToString AAQHigh = "high"

antialiasingQualityFromString :: String -> Maybe AntialiasingQuality
antialiasingQualityFromString "low" = Just AAQLow
antialiasingQualityFromString "medium" = Just AAQMedium
antialiasingQualityFromString "high" = Just AAQHigh
antialiasingQualityFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // distortion // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shape of gradient ramp.
data RampShape
  = RSLinear   -- ^ Linear gradient
  | RSRadial   -- ^ Radial gradient

derive instance eqRampShape :: Eq RampShape
derive instance ordRampShape :: Ord RampShape

instance showRampShape :: Show RampShape where
  show RSLinear = "RSLinear"
  show RSRadial = "RSRadial"

rampShapeToString :: RampShape -> String
rampShapeToString RSLinear = "linear"
rampShapeToString RSRadial = "radial"

rampShapeFromString :: String -> Maybe RampShape
rampShapeFromString "linear" = Just RSLinear
rampShapeFromString "radial" = Just RSRadial
rampShapeFromString _ = Nothing

-- | Style of warp distortion (15 variants, matches Photoshop).
data WarpStyle
  = WSArc          -- ^ Arc warp
  | WSArcLower     -- ^ Lower arc
  | WSArcUpper     -- ^ Upper arc
  | WSArch         -- ^ Arch shape
  | WSBulge        -- ^ Bulge outward
  | WSShellLower   -- ^ Lower shell
  | WSShellUpper   -- ^ Upper shell
  | WSFlag         -- ^ Flag wave
  | WSWave         -- ^ Wave distortion
  | WSFish         -- ^ Fish shape
  | WSRise         -- ^ Rising effect
  | WSFisheye      -- ^ Fisheye lens
  | WSInflate      -- ^ Inflate/balloon
  | WSSqueeze      -- ^ Squeeze horizontally
  | WSTwist        -- ^ Twist around center

derive instance eqWarpStyle :: Eq WarpStyle
derive instance ordWarpStyle :: Ord WarpStyle

instance showWarpStyle :: Show WarpStyle where
  show WSArc = "WSArc"
  show WSArcLower = "WSArcLower"
  show WSArcUpper = "WSArcUpper"
  show WSArch = "WSArch"
  show WSBulge = "WSBulge"
  show WSShellLower = "WSShellLower"
  show WSShellUpper = "WSShellUpper"
  show WSFlag = "WSFlag"
  show WSWave = "WSWave"
  show WSFish = "WSFish"
  show WSRise = "WSRise"
  show WSFisheye = "WSFisheye"
  show WSInflate = "WSInflate"
  show WSSqueeze = "WSSqueeze"
  show WSTwist = "WSTwist"

warpStyleToString :: WarpStyle -> String
warpStyleToString WSArc = "arc"
warpStyleToString WSArcLower = "arc-lower"
warpStyleToString WSArcUpper = "arc-upper"
warpStyleToString WSArch = "arch"
warpStyleToString WSBulge = "bulge"
warpStyleToString WSShellLower = "shell-lower"
warpStyleToString WSShellUpper = "shell-upper"
warpStyleToString WSFlag = "flag"
warpStyleToString WSWave = "wave"
warpStyleToString WSFish = "fish"
warpStyleToString WSRise = "rise"
warpStyleToString WSFisheye = "fisheye"
warpStyleToString WSInflate = "inflate"
warpStyleToString WSSqueeze = "squeeze"
warpStyleToString WSTwist = "twist"

warpStyleFromString :: String -> Maybe WarpStyle
warpStyleFromString "arc" = Just WSArc
warpStyleFromString "arc-lower" = Just WSArcLower
warpStyleFromString "arc-upper" = Just WSArcUpper
warpStyleFromString "arch" = Just WSArch
warpStyleFromString "bulge" = Just WSBulge
warpStyleFromString "shell-lower" = Just WSShellLower
warpStyleFromString "shell-upper" = Just WSShellUpper
warpStyleFromString "flag" = Just WSFlag
warpStyleFromString "wave" = Just WSWave
warpStyleFromString "fish" = Just WSFish
warpStyleFromString "rise" = Just WSRise
warpStyleFromString "fisheye" = Just WSFisheye
warpStyleFromString "inflate" = Just WSInflate
warpStyleFromString "squeeze" = Just WSSqueeze
warpStyleFromString "twist" = Just WSTwist
warpStyleFromString _ = Nothing

-- | Type of displacement map source.
data DisplacementMapType
  = DMTLayer      -- ^ Use another layer
  | DMTNoise      -- ^ Procedural noise
  | DMTGradientH  -- ^ Horizontal gradient
  | DMTGradientV  -- ^ Vertical gradient
  | DMTRadial     -- ^ Radial gradient
  | DMTSineH      -- ^ Horizontal sine wave
  | DMTSineV      -- ^ Vertical sine wave
  | DMTChecker    -- ^ Checkerboard pattern

derive instance eqDisplacementMapType :: Eq DisplacementMapType
derive instance ordDisplacementMapType :: Ord DisplacementMapType

instance showDisplacementMapType :: Show DisplacementMapType where
  show DMTLayer = "DMTLayer"
  show DMTNoise = "DMTNoise"
  show DMTGradientH = "DMTGradientH"
  show DMTGradientV = "DMTGradientV"
  show DMTRadial = "DMTRadial"
  show DMTSineH = "DMTSineH"
  show DMTSineV = "DMTSineV"
  show DMTChecker = "DMTChecker"

displacementMapTypeToString :: DisplacementMapType -> String
displacementMapTypeToString DMTLayer = "layer"
displacementMapTypeToString DMTNoise = "noise"
displacementMapTypeToString DMTGradientH = "gradient-h"
displacementMapTypeToString DMTGradientV = "gradient-v"
displacementMapTypeToString DMTRadial = "radial"
displacementMapTypeToString DMTSineH = "sine-h"
displacementMapTypeToString DMTSineV = "sine-v"
displacementMapTypeToString DMTChecker = "checker"

displacementMapTypeFromString :: String -> Maybe DisplacementMapType
displacementMapTypeFromString "layer" = Just DMTLayer
displacementMapTypeFromString "noise" = Just DMTNoise
displacementMapTypeFromString "gradient-h" = Just DMTGradientH
displacementMapTypeFromString "gradient-v" = Just DMTGradientV
displacementMapTypeFromString "radial" = Just DMTRadial
displacementMapTypeFromString "sine-h" = Just DMTSineH
displacementMapTypeFromString "sine-v" = Just DMTSineV
displacementMapTypeFromString "checker" = Just DMTChecker
displacementMapTypeFromString _ = Nothing

-- | Channel used for displacement.
data DisplacementChannel
  = DCRed        -- ^ Red channel
  | DCGreen      -- ^ Green channel
  | DCBlue       -- ^ Blue channel
  | DCAlpha      -- ^ Alpha channel
  | DCLuminance  -- ^ Luminance (grayscale)
  | DCOff        -- ^ No displacement

derive instance eqDisplacementChannel :: Eq DisplacementChannel
derive instance ordDisplacementChannel :: Ord DisplacementChannel

instance showDisplacementChannel :: Show DisplacementChannel where
  show DCRed = "DCRed"
  show DCGreen = "DCGreen"
  show DCBlue = "DCBlue"
  show DCAlpha = "DCAlpha"
  show DCLuminance = "DCLuminance"
  show DCOff = "DCOff"

displacementChannelToString :: DisplacementChannel -> String
displacementChannelToString DCRed = "red"
displacementChannelToString DCGreen = "green"
displacementChannelToString DCBlue = "blue"
displacementChannelToString DCAlpha = "alpha"
displacementChannelToString DCLuminance = "luminance"
displacementChannelToString DCOff = "off"

displacementChannelFromString :: String -> Maybe DisplacementChannel
displacementChannelFromString "red" = Just DCRed
displacementChannelFromString "green" = Just DCGreen
displacementChannelFromString "blue" = Just DCBlue
displacementChannelFromString "alpha" = Just DCAlpha
displacementChannelFromString "luminance" = Just DCLuminance
displacementChannelFromString "off" = Just DCOff
displacementChannelFromString _ = Nothing

-- | Behavior at image edges.
data EdgeBehavior
  = EBOff     -- ^ No edge handling
  | EBTiles   -- ^ Tile/wrap edges
  | EBMirror  -- ^ Mirror at edges

derive instance eqEdgeBehavior :: Eq EdgeBehavior
derive instance ordEdgeBehavior :: Ord EdgeBehavior

instance showEdgeBehavior :: Show EdgeBehavior where
  show EBOff = "EBOff"
  show EBTiles = "EBTiles"
  show EBMirror = "EBMirror"

edgeBehaviorToString :: EdgeBehavior -> String
edgeBehaviorToString EBOff = "off"
edgeBehaviorToString EBTiles = "tiles"
edgeBehaviorToString EBMirror = "mirror"

edgeBehaviorFromString :: String -> Maybe EdgeBehavior
edgeBehaviorFromString "off" = Just EBOff
edgeBehaviorFromString "tiles" = Just EBTiles
edgeBehaviorFromString "mirror" = Just EBMirror
edgeBehaviorFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // glow // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How glow is composited with source.
data GlowCompositeMode
  = GCMOnTop   -- ^ Glow on top of source
  | GCMBehind  -- ^ Glow behind source
  | GCMNone    -- ^ Glow only (no source)

derive instance eqGlowCompositeMode :: Eq GlowCompositeMode
derive instance ordGlowCompositeMode :: Ord GlowCompositeMode

instance showGlowCompositeMode :: Show GlowCompositeMode where
  show GCMOnTop = "GCMOnTop"
  show GCMBehind = "GCMBehind"
  show GCMNone = "GCMNone"

glowCompositeModeToString :: GlowCompositeMode -> String
glowCompositeModeToString GCMOnTop = "on-top"
glowCompositeModeToString GCMBehind = "behind"
glowCompositeModeToString GCMNone = "none"

glowCompositeModeFromString :: String -> Maybe GlowCompositeMode
glowCompositeModeFromString "on-top" = Just GCMOnTop
glowCompositeModeFromString "behind" = Just GCMBehind
glowCompositeModeFromString "none" = Just GCMNone
glowCompositeModeFromString _ = Nothing

-- | How glow colors are determined.
data GlowColorsMode
  = GCMOriginal  -- ^ Use original source colors
  | GCMAB        -- ^ Interpolate between A and B colors

derive instance eqGlowColorsMode :: Eq GlowColorsMode
derive instance ordGlowColorsMode :: Ord GlowColorsMode

instance showGlowColorsMode :: Show GlowColorsMode where
  show GCMOriginal = "GCMOriginal"
  show GCMAB = "GCMAB"

glowColorsModeToString :: GlowColorsMode -> String
glowColorsModeToString GCMOriginal = "original"
glowColorsModeToString GCMAB = "ab"

glowColorsModeFromString :: String -> Maybe GlowColorsMode
glowColorsModeFromString "original" = Just GCMOriginal
glowColorsModeFromString "ab" = Just GCMAB
glowColorsModeFromString _ = Nothing

-- | Color cycling behavior for glow.
data ColorLooping
  = CLNone        -- ^ No looping
  | CLSawtoothAB  -- ^ Sawtooth A→B
  | CLSawtoothBA  -- ^ Sawtooth B→A
  | CLTriangle    -- ^ Triangle wave A→B→A

derive instance eqColorLooping :: Eq ColorLooping
derive instance ordColorLooping :: Ord ColorLooping

instance showColorLooping :: Show ColorLooping where
  show CLNone = "CLNone"
  show CLSawtoothAB = "CLSawtoothAB"
  show CLSawtoothBA = "CLSawtoothBA"
  show CLTriangle = "CLTriangle"

colorLoopingToString :: ColorLooping -> String
colorLoopingToString CLNone = "none"
colorLoopingToString CLSawtoothAB = "sawtooth-ab"
colorLoopingToString CLSawtoothBA = "sawtooth-ba"
colorLoopingToString CLTriangle = "triangle"

colorLoopingFromString :: String -> Maybe ColorLooping
colorLoopingFromString "none" = Just CLNone
colorLoopingFromString "sawtooth-ab" = Just CLSawtoothAB
colorLoopingFromString "sawtooth-ba" = Just CLSawtoothBA
colorLoopingFromString "triangle" = Just CLTriangle
colorLoopingFromString _ = Nothing

-- | Intensity falloff mode.
data FalloffMode
  = FMInverseSquare  -- ^ 1/r² falloff (physically accurate)
  | FMGaussian       -- ^ Gaussian curve
  | FMExponential    -- ^ Exponential decay

derive instance eqFalloffMode :: Eq FalloffMode
derive instance ordFalloffMode :: Ord FalloffMode

instance showFalloffMode :: Show FalloffMode where
  show FMInverseSquare = "FMInverseSquare"
  show FMGaussian = "FMGaussian"
  show FMExponential = "FMExponential"

falloffModeToString :: FalloffMode -> String
falloffModeToString FMInverseSquare = "inverse-square"
falloffModeToString FMGaussian = "gaussian"
falloffModeToString FMExponential = "exponential"

falloffModeFromString :: String -> Maybe FalloffMode
falloffModeFromString "inverse-square" = Just FMInverseSquare
falloffModeFromString "gaussian" = Just FMGaussian
falloffModeFromString "exponential" = Just FMExponential
falloffModeFromString _ = Nothing

-- | HDR tonemapping mode.
data TonemapMode
  = TMNone      -- ^ No tonemapping
  | TMACES      -- ^ ACES filmic
  | TMReinhard  -- ^ Reinhard tonemapping
  | TMHable     -- ^ Hable/Uncharted 2

derive instance eqTonemapMode :: Eq TonemapMode
derive instance ordTonemapMode :: Ord TonemapMode

instance showTonemapMode :: Show TonemapMode where
  show TMNone = "TMNone"
  show TMACES = "TMACES"
  show TMReinhard = "TMReinhard"
  show TMHable = "TMHable"

tonemapModeToString :: TonemapMode -> String
tonemapModeToString TMNone = "none"
tonemapModeToString TMACES = "aces"
tonemapModeToString TMReinhard = "reinhard"
tonemapModeToString TMHable = "hable"

tonemapModeFromString :: String -> Maybe TonemapMode
tonemapModeFromString "none" = Just TMNone
tonemapModeFromString "aces" = Just TMACES
tonemapModeFromString "reinhard" = Just TMReinhard
tonemapModeFromString "hable" = Just TMHable
tonemapModeFromString _ = Nothing

-- | Bloom effect blend mode.
data BloomBlendMode
  = BBMAdd       -- ^ Additive blend
  | BBMScreen    -- ^ Screen blend
  | BBMOverlay   -- ^ Overlay blend
  | BBMSoftLight -- ^ Soft light blend

derive instance eqBloomBlendMode :: Eq BloomBlendMode
derive instance ordBloomBlendMode :: Ord BloomBlendMode

instance showBloomBlendMode :: Show BloomBlendMode where
  show BBMAdd = "BBMAdd"
  show BBMScreen = "BBMScreen"
  show BBMOverlay = "BBMOverlay"
  show BBMSoftLight = "BBMSoftLight"

bloomBlendModeToString :: BloomBlendMode -> String
bloomBlendModeToString BBMAdd = "add"
bloomBlendModeToString BBMScreen = "screen"
bloomBlendModeToString BBMOverlay = "overlay"
bloomBlendModeToString BBMSoftLight = "soft-light"

bloomBlendModeFromString :: String -> Maybe BloomBlendMode
bloomBlendModeFromString "add" = Just BBMAdd
bloomBlendModeFromString "screen" = Just BBMScreen
bloomBlendModeFromString "overlay" = Just BBMOverlay
bloomBlendModeFromString "soft-light" = Just BBMSoftLight
bloomBlendModeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // noise // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Type of fractal noise generation.
data FractalType
  = FTBasic          -- ^ Basic fractal noise
  | FTTurbulentBasic -- ^ Turbulent (absolute value)
  | FTSoftLinear     -- ^ Soft linear interpolation
  | FTTurbulentSoft  -- ^ Turbulent with soft interp

derive instance eqFractalType :: Eq FractalType
derive instance ordFractalType :: Ord FractalType

instance showFractalType :: Show FractalType where
  show FTBasic = "FTBasic"
  show FTTurbulentBasic = "FTTurbulentBasic"
  show FTSoftLinear = "FTSoftLinear"
  show FTTurbulentSoft = "FTTurbulentSoft"

fractalTypeToString :: FractalType -> String
fractalTypeToString FTBasic = "basic"
fractalTypeToString FTTurbulentBasic = "turbulent-basic"
fractalTypeToString FTSoftLinear = "soft-linear"
fractalTypeToString FTTurbulentSoft = "turbulent-soft"

fractalTypeFromString :: String -> Maybe FractalType
fractalTypeFromString "basic" = Just FTBasic
fractalTypeFromString "turbulent-basic" = Just FTTurbulentBasic
fractalTypeFromString "soft-linear" = Just FTSoftLinear
fractalTypeFromString "turbulent-soft" = Just FTTurbulentSoft
fractalTypeFromString _ = Nothing

-- | Type of base noise.
data NoiseType
  = NTBlock       -- ^ Block/cell noise
  | NTLinear      -- ^ Linear interpolated
  | NTSoftLinear  -- ^ Soft linear
  | NTSpline      -- ^ Spline interpolated

derive instance eqNoiseType :: Eq NoiseType
derive instance ordNoiseType :: Ord NoiseType

instance showNoiseType :: Show NoiseType where
  show NTBlock = "NTBlock"
  show NTLinear = "NTLinear"
  show NTSoftLinear = "NTSoftLinear"
  show NTSpline = "NTSpline"

noiseTypeToString :: NoiseType -> String
noiseTypeToString NTBlock = "block"
noiseTypeToString NTLinear = "linear"
noiseTypeToString NTSoftLinear = "soft-linear"
noiseTypeToString NTSpline = "spline"

noiseTypeFromString :: String -> Maybe NoiseType
noiseTypeFromString "block" = Just NTBlock
noiseTypeFromString "linear" = Just NTLinear
noiseTypeFromString "soft-linear" = Just NTSoftLinear
noiseTypeFromString "spline" = Just NTSpline
noiseTypeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // time // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Operator for combining echo frames.
data EchoOperator
  = EOAdd            -- ^ Add frames together
  | EOScreen         -- ^ Screen blend
  | EOMaximum        -- ^ Take maximum values
  | EOMinimum        -- ^ Take minimum values
  | EOCompositeBack  -- ^ Composite echoes behind
  | EOCompositeFront -- ^ Composite echoes in front
  | EOBlend          -- ^ Linear blend

derive instance eqEchoOperator :: Eq EchoOperator
derive instance ordEchoOperator :: Ord EchoOperator

instance showEchoOperator :: Show EchoOperator where
  show EOAdd = "EOAdd"
  show EOScreen = "EOScreen"
  show EOMaximum = "EOMaximum"
  show EOMinimum = "EOMinimum"
  show EOCompositeBack = "EOCompositeBack"
  show EOCompositeFront = "EOCompositeFront"
  show EOBlend = "EOBlend"

echoOperatorToString :: EchoOperator -> String
echoOperatorToString EOAdd = "add"
echoOperatorToString EOScreen = "screen"
echoOperatorToString EOMaximum = "maximum"
echoOperatorToString EOMinimum = "minimum"
echoOperatorToString EOCompositeBack = "composite-back"
echoOperatorToString EOCompositeFront = "composite-front"
echoOperatorToString EOBlend = "blend"

echoOperatorFromString :: String -> Maybe EchoOperator
echoOperatorFromString "add" = Just EOAdd
echoOperatorFromString "screen" = Just EOScreen
echoOperatorFromString "maximum" = Just EOMaximum
echoOperatorFromString "minimum" = Just EOMinimum
echoOperatorFromString "composite-back" = Just EOCompositeBack
echoOperatorFromString "composite-front" = Just EOCompositeFront
echoOperatorFromString "blend" = Just EOBlend
echoOperatorFromString _ = Nothing

-- | Resolution for time-based effects.
data TimeResolution
  = TRFrame    -- ^ Full frame
  | TRHalf     -- ^ Half frame
  | TRQuarter  -- ^ Quarter frame

derive instance eqTimeResolution :: Eq TimeResolution
derive instance ordTimeResolution :: Ord TimeResolution

instance showTimeResolution :: Show TimeResolution where
  show TRFrame = "TRFrame"
  show TRHalf = "TRHalf"
  show TRQuarter = "TRQuarter"

timeResolutionToString :: TimeResolution -> String
timeResolutionToString TRFrame = "frame"
timeResolutionToString TRHalf = "half"
timeResolutionToString TRQuarter = "quarter"

timeResolutionFromString :: String -> Maybe TimeResolution
timeResolutionFromString "frame" = Just TRFrame
timeResolutionFromString "half" = Just TRHalf
timeResolutionFromString "quarter" = Just TRQuarter
timeResolutionFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // mesh // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Falloff type for pin influence.
data PinFalloff
  = PFInverseDistance  -- ^ Standard 1/d falloff
  | PFRadialBasis      -- ^ RBF interpolation

derive instance eqPinFalloff :: Eq PinFalloff
derive instance ordPinFalloff :: Ord PinFalloff

instance showPinFalloff :: Show PinFalloff where
  show PFInverseDistance = "PFInverseDistance"
  show PFRadialBasis = "PFRadialBasis"

pinFalloffToString :: PinFalloff -> String
pinFalloffToString PFInverseDistance = "inverse-distance"
pinFalloffToString PFRadialBasis = "radial-basis"

pinFalloffFromString :: String -> Maybe PinFalloff
pinFalloffFromString "inverse-distance" = Just PFInverseDistance
pinFalloffFromString "radial-basis" = Just PFRadialBasis
pinFalloffFromString _ = Nothing

-- | Type of turbulent displacement.
data TurbulentDisplaceType
  = TDTTurbulent        -- ^ Standard turbulence
  | TDTBulge            -- ^ Bulge displacement
  | TDTTwist            -- ^ Twist displacement
  | TDTTurbulentSmoother -- ^ Smoother turbulence
  | TDTHorizontal       -- ^ Horizontal only
  | TDTVertical         -- ^ Vertical only
  | TDTCross            -- ^ Cross pattern

derive instance eqTurbulentDisplaceType :: Eq TurbulentDisplaceType
derive instance ordTurbulentDisplaceType :: Ord TurbulentDisplaceType

instance showTurbulentDisplaceType :: Show TurbulentDisplaceType where
  show TDTTurbulent = "TDTTurbulent"
  show TDTBulge = "TDTBulge"
  show TDTTwist = "TDTTwist"
  show TDTTurbulentSmoother = "TDTTurbulentSmoother"
  show TDTHorizontal = "TDTHorizontal"
  show TDTVertical = "TDTVertical"
  show TDTCross = "TDTCross"

turbulentDisplaceTypeToString :: TurbulentDisplaceType -> String
turbulentDisplaceTypeToString TDTTurbulent = "turbulent"
turbulentDisplaceTypeToString TDTBulge = "bulge"
turbulentDisplaceTypeToString TDTTwist = "twist"
turbulentDisplaceTypeToString TDTTurbulentSmoother = "turbulent-smoother"
turbulentDisplaceTypeToString TDTHorizontal = "horizontal"
turbulentDisplaceTypeToString TDTVertical = "vertical"
turbulentDisplaceTypeToString TDTCross = "cross"

turbulentDisplaceTypeFromString :: String -> Maybe TurbulentDisplaceType
turbulentDisplaceTypeFromString "turbulent" = Just TDTTurbulent
turbulentDisplaceTypeFromString "bulge" = Just TDTBulge
turbulentDisplaceTypeFromString "twist" = Just TDTTwist
turbulentDisplaceTypeFromString "turbulent-smoother" = Just TDTTurbulentSmoother
turbulentDisplaceTypeFromString "horizontal" = Just TDTHorizontal
turbulentDisplaceTypeFromString "vertical" = Just TDTVertical
turbulentDisplaceTypeFromString "cross" = Just TDTCross
turbulentDisplaceTypeFromString _ = Nothing

-- | Edge pinning mode for mesh deform.
data PinningMode
  = PMNone        -- ^ No edge pinning
  | PMAll         -- ^ Pin all edges
  | PMHorizontal  -- ^ Pin horizontal edges
  | PMVertical    -- ^ Pin vertical edges

derive instance eqPinningMode :: Eq PinningMode
derive instance ordPinningMode :: Ord PinningMode

instance showPinningMode :: Show PinningMode where
  show PMNone = "PMNone"
  show PMAll = "PMAll"
  show PMHorizontal = "PMHorizontal"
  show PMVertical = "PMVertical"

pinningModeToString :: PinningMode -> String
pinningModeToString PMNone = "none"
pinningModeToString PMAll = "all"
pinningModeToString PMHorizontal = "horizontal"
pinningModeToString PMVertical = "vertical"

pinningModeFromString :: String -> Maybe PinningMode
pinningModeFromString "none" = Just PMNone
pinningModeFromString "all" = Just PMAll
pinningModeFromString "horizontal" = Just PMHorizontal
pinningModeFromString "vertical" = Just PMVertical
pinningModeFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // stylize // enums
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction of scanlines effect.
data ScanlinesDirection
  = SDHorizontal  -- ^ Horizontal scanlines
  | SDVertical    -- ^ Vertical scanlines

derive instance eqScanlinesDirection :: Eq ScanlinesDirection
derive instance ordScanlinesDirection :: Ord ScanlinesDirection

instance showScanlinesDirection :: Show ScanlinesDirection where
  show SDHorizontal = "SDHorizontal"
  show SDVertical = "SDVertical"

scanlinesDirectionToString :: ScanlinesDirection -> String
scanlinesDirectionToString SDHorizontal = "horizontal"
scanlinesDirectionToString SDVertical = "vertical"

scanlinesDirectionFromString :: String -> Maybe ScanlinesDirection
scanlinesDirectionFromString "horizontal" = Just SDHorizontal
scanlinesDirectionFromString "vertical" = Just SDVertical
scanlinesDirectionFromString _ = Nothing

-- | Blend mode for RGB split effect.
data RGBSplitBlendMode
  = RSBMScreen  -- ^ Screen blend
  | RSBMAdd     -- ^ Additive blend
  | RSBMNormal  -- ^ Normal blend

derive instance eqRGBSplitBlendMode :: Eq RGBSplitBlendMode
derive instance ordRGBSplitBlendMode :: Ord RGBSplitBlendMode

instance showRGBSplitBlendMode :: Show RGBSplitBlendMode where
  show RSBMScreen = "RSBMScreen"
  show RSBMAdd = "RSBMAdd"
  show RSBMNormal = "RSBMNormal"

rgbSplitBlendModeToString :: RGBSplitBlendMode -> String
rgbSplitBlendModeToString RSBMScreen = "screen"
rgbSplitBlendModeToString RSBMAdd = "add"
rgbSplitBlendModeToString RSBMNormal = "normal"

rgbSplitBlendModeFromString :: String -> Maybe RGBSplitBlendMode
rgbSplitBlendModeFromString "screen" = Just RSBMScreen
rgbSplitBlendModeFromString "add" = Just RSBMAdd
rgbSplitBlendModeFromString "normal" = Just RSBMNormal
rgbSplitBlendModeFromString _ = Nothing

-- | Direction of pixel sorting.
data PixelSortDirection
  = PSDHorizontal  -- ^ Sort horizontally
  | PSDVertical    -- ^ Sort vertically

derive instance eqPixelSortDirection :: Eq PixelSortDirection
derive instance ordPixelSortDirection :: Ord PixelSortDirection

instance showPixelSortDirection :: Show PixelSortDirection where
  show PSDHorizontal = "PSDHorizontal"
  show PSDVertical = "PSDVertical"

pixelSortDirectionToString :: PixelSortDirection -> String
pixelSortDirectionToString PSDHorizontal = "horizontal"
pixelSortDirectionToString PSDVertical = "vertical"

pixelSortDirectionFromString :: String -> Maybe PixelSortDirection
pixelSortDirectionFromString "horizontal" = Just PSDHorizontal
pixelSortDirectionFromString "vertical" = Just PSDVertical
pixelSortDirectionFromString _ = Nothing

-- | Criterion for sorting pixels.
data SortByCriterion
  = SBCSaturation  -- ^ Sort by saturation
  | SBCBrightness  -- ^ Sort by brightness
  | SBCHue         -- ^ Sort by hue

derive instance eqSortByCriterion :: Eq SortByCriterion
derive instance ordSortByCriterion :: Ord SortByCriterion

instance showSortByCriterion :: Show SortByCriterion where
  show SBCSaturation = "SBCSaturation"
  show SBCBrightness = "SBCBrightness"
  show SBCHue = "SBCHue"

sortByCriterionToString :: SortByCriterion -> String
sortByCriterionToString SBCSaturation = "saturation"
sortByCriterionToString SBCBrightness = "brightness"
sortByCriterionToString SBCHue = "hue"

sortByCriterionFromString :: String -> Maybe SortByCriterion
sortByCriterionFromString "saturation" = Just SBCSaturation
sortByCriterionFromString "brightness" = Just SBCBrightness
sortByCriterionFromString "hue" = Just SBCHue
sortByCriterionFromString _ = Nothing

-- | Color mode for halftone effect.
data HalftoneColorMode
  = HCMGrayscale  -- ^ Grayscale halftone
  | HCMRGB        -- ^ RGB halftone
  | HCMCMYK       -- ^ CMYK halftone

derive instance eqHalftoneColorMode :: Eq HalftoneColorMode
derive instance ordHalftoneColorMode :: Ord HalftoneColorMode

instance showHalftoneColorMode :: Show HalftoneColorMode where
  show HCMGrayscale = "HCMGrayscale"
  show HCMRGB = "HCMRGB"
  show HCMCMYK = "HCMCMYK"

halftoneColorModeToString :: HalftoneColorMode -> String
halftoneColorModeToString HCMGrayscale = "grayscale"
halftoneColorModeToString HCMRGB = "rgb"
halftoneColorModeToString HCMCMYK = "cmyk"

halftoneColorModeFromString :: String -> Maybe HalftoneColorMode
halftoneColorModeFromString "grayscale" = Just HCMGrayscale
halftoneColorModeFromString "rgb" = Just HCMRGB
halftoneColorModeFromString "cmyk" = Just HCMCMYK
halftoneColorModeFromString _ = Nothing

-- | Dithering method.
data DitherMethod
  = DMOrdered         -- ^ Ordered (Bayer) dither
  | DMFloydSteinberg  -- ^ Floyd-Steinberg error diffusion
  | DMAtkinson        -- ^ Atkinson dither

derive instance eqDitherMethod :: Eq DitherMethod
derive instance ordDitherMethod :: Ord DitherMethod

instance showDitherMethod :: Show DitherMethod where
  show DMOrdered = "DMOrdered"
  show DMFloydSteinberg = "DMFloydSteinberg"
  show DMAtkinson = "DMAtkinson"

ditherMethodToString :: DitherMethod -> String
ditherMethodToString DMOrdered = "ordered"
ditherMethodToString DMFloydSteinberg = "floyd-steinberg"
ditherMethodToString DMAtkinson = "atkinson"

ditherMethodFromString :: String -> Maybe DitherMethod
ditherMethodFromString "ordered" = Just DMOrdered
ditherMethodFromString "floyd-steinberg" = Just DMFloydSteinberg
ditherMethodFromString "atkinson" = Just DMAtkinson
ditherMethodFromString _ = Nothing

-- | Size of dither matrix.
data DitherMatrixSize
  = DMS2x2  -- ^ 2×2 matrix
  | DMS4x4  -- ^ 4×4 matrix
  | DMS8x8  -- ^ 8×8 matrix

derive instance eqDitherMatrixSize :: Eq DitherMatrixSize
derive instance ordDitherMatrixSize :: Ord DitherMatrixSize

instance showDitherMatrixSize :: Show DitherMatrixSize where
  show DMS2x2 = "DMS2x2"
  show DMS4x4 = "DMS4x4"
  show DMS8x8 = "DMS8x8"

ditherMatrixSizeToString :: DitherMatrixSize -> String
ditherMatrixSizeToString DMS2x2 = "2x2"
ditherMatrixSizeToString DMS4x4 = "4x4"
ditherMatrixSizeToString DMS8x8 = "8x8"

ditherMatrixSizeFromString :: String -> Maybe DitherMatrixSize
ditherMatrixSizeFromString "2x2" = Just DMS2x2
ditherMatrixSizeFromString "4x4" = Just DMS4x4
ditherMatrixSizeFromString "8x8" = Just DMS8x8
ditherMatrixSizeFromString _ = Nothing

-- | Color channel selection for effects.
data EffectColorChannel
  = ECCRGB    -- ^ All RGB channels
  | ECCRed    -- ^ Red channel only
  | ECCGreen  -- ^ Green channel only
  | ECCBlue   -- ^ Blue channel only
  | ECCAlpha  -- ^ Alpha channel only

derive instance eqEffectColorChannel :: Eq EffectColorChannel
derive instance ordEffectColorChannel :: Ord EffectColorChannel

instance showEffectColorChannel :: Show EffectColorChannel where
  show ECCRGB = "ECCRGB"
  show ECCRed = "ECCRed"
  show ECCGreen = "ECCGreen"
  show ECCBlue = "ECCBlue"
  show ECCAlpha = "ECCAlpha"

effectColorChannelToString :: EffectColorChannel -> String
effectColorChannelToString ECCRGB = "rgb"
effectColorChannelToString ECCRed = "red"
effectColorChannelToString ECCGreen = "green"
effectColorChannelToString ECCBlue = "blue"
effectColorChannelToString ECCAlpha = "alpha"

effectColorChannelFromString :: String -> Maybe EffectColorChannel
effectColorChannelFromString "rgb" = Just ECCRGB
effectColorChannelFromString "red" = Just ECCRed
effectColorChannelFromString "green" = Just ECCGreen
effectColorChannelFromString "blue" = Just ECCBlue
effectColorChannelFromString "alpha" = Just ECCAlpha
effectColorChannelFromString _ = Nothing

-- | HSL channel selection.
data HSLChannel
  = HSLMaster    -- ^ All colors
  | HSLReds      -- ^ Red range
  | HSLYellows   -- ^ Yellow range
  | HSLGreens    -- ^ Green range
  | HSLCyans     -- ^ Cyan range
  | HSLBlues     -- ^ Blue range
  | HSLMagentas  -- ^ Magenta range

derive instance eqHSLChannel :: Eq HSLChannel
derive instance ordHSLChannel :: Ord HSLChannel

instance showHSLChannel :: Show HSLChannel where
  show HSLMaster = "HSLMaster"
  show HSLReds = "HSLReds"
  show HSLYellows = "HSLYellows"
  show HSLGreens = "HSLGreens"
  show HSLCyans = "HSLCyans"
  show HSLBlues = "HSLBlues"
  show HSLMagentas = "HSLMagentas"

hslChannelToString :: HSLChannel -> String
hslChannelToString HSLMaster = "master"
hslChannelToString HSLReds = "reds"
hslChannelToString HSLYellows = "yellows"
hslChannelToString HSLGreens = "greens"
hslChannelToString HSLCyans = "cyans"
hslChannelToString HSLBlues = "blues"
hslChannelToString HSLMagentas = "magentas"

hslChannelFromString :: String -> Maybe HSLChannel
hslChannelFromString "master" = Just HSLMaster
hslChannelFromString "reds" = Just HSLReds
hslChannelFromString "yellows" = Just HSLYellows
hslChannelFromString "greens" = Just HSLGreens
hslChannelFromString "cyans" = Just HSLCyans
hslChannelFromString "blues" = Just HSLBlues
hslChannelFromString "magentas" = Just HSLMagentas
hslChannelFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // effect // category
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Category of effect for organization.
data EffectCategory
  = ECBlurSharpen       -- ^ Blur and sharpen effects
  | ECColorCorrection   -- ^ Color adjustment effects
  | ECDistort           -- ^ Distortion effects
  | ECGenerate          -- ^ Generation effects (noise, patterns)
  | ECKeying            -- ^ Keying/chroma key effects
  | ECMatte             -- ^ Matte tools
  | ECNoiseGrain        -- ^ Noise and grain effects
  | ECPerspective       -- ^ 3D perspective effects
  | ECStylize           -- ^ Stylization effects
  | ECTime              -- ^ Time-based effects
  | ECTransition        -- ^ Transition effects
  | ECUtility           -- ^ Utility effects

derive instance eqEffectCategory :: Eq EffectCategory
derive instance ordEffectCategory :: Ord EffectCategory

instance showEffectCategory :: Show EffectCategory where
  show ECBlurSharpen = "ECBlurSharpen"
  show ECColorCorrection = "ECColorCorrection"
  show ECDistort = "ECDistort"
  show ECGenerate = "ECGenerate"
  show ECKeying = "ECKeying"
  show ECMatte = "ECMatte"
  show ECNoiseGrain = "ECNoiseGrain"
  show ECPerspective = "ECPerspective"
  show ECStylize = "ECStylize"
  show ECTime = "ECTime"
  show ECTransition = "ECTransition"
  show ECUtility = "ECUtility"

effectCategoryToString :: EffectCategory -> String
effectCategoryToString ECBlurSharpen = "blur-sharpen"
effectCategoryToString ECColorCorrection = "color-correction"
effectCategoryToString ECDistort = "distort"
effectCategoryToString ECGenerate = "generate"
effectCategoryToString ECKeying = "keying"
effectCategoryToString ECMatte = "matte"
effectCategoryToString ECNoiseGrain = "noise-grain"
effectCategoryToString ECPerspective = "perspective"
effectCategoryToString ECStylize = "stylize"
effectCategoryToString ECTime = "time"
effectCategoryToString ECTransition = "transition"
effectCategoryToString ECUtility = "utility"

effectCategoryFromString :: String -> Maybe EffectCategory
effectCategoryFromString "blur-sharpen" = Just ECBlurSharpen
effectCategoryFromString "color-correction" = Just ECColorCorrection
effectCategoryFromString "distort" = Just ECDistort
effectCategoryFromString "generate" = Just ECGenerate
effectCategoryFromString "keying" = Just ECKeying
effectCategoryFromString "matte" = Just ECMatte
effectCategoryFromString "noise-grain" = Just ECNoiseGrain
effectCategoryFromString "perspective" = Just ECPerspective
effectCategoryFromString "stylize" = Just ECStylize
effectCategoryFromString "time" = Just ECTime
effectCategoryFromString "transition" = Just ECTransition
effectCategoryFromString "utility" = Just ECUtility
effectCategoryFromString _ = Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // parameter // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | 2D point for effect parameters.
type EffectPoint2D =
  { x :: Number
  , y :: Number
  }

-- | Create a 2D point.
mkEffectPoint2D :: Number -> Number -> EffectPoint2D
mkEffectPoint2D x y = { x, y }

-- | 3D point for effect parameters.
type EffectPoint3D =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a 3D point.
mkEffectPoint3D :: Number -> Number -> Number -> EffectPoint3D
mkEffectPoint3D x y z = { x, y, z }

-- | RGBA color for effect parameters.
-- |
-- | RGB channels are 0-255, alpha is 0.0-1.0.
type EffectRGBA =
  { r :: Int    -- ^ Red (0-255)
  , g :: Int    -- ^ Green (0-255)
  , b :: Int    -- ^ Blue (0-255)
  , a :: Number -- ^ Alpha (0.0-1.0)
  }

-- | Create an RGBA color.
mkEffectRGBA :: Int -> Int -> Int -> Number -> EffectRGBA
mkEffectRGBA r g b a = { r, g, b, a }

-- | Create an opaque color.
effectRGBAOpaque :: Int -> Int -> Int -> EffectRGBA
effectRGBAOpaque r g b = { r, g, b, a: 1.0 }

-- | Point on a curve (for bezier/spline parameters).
type CurvePoint =
  { x :: Number
  , y :: Number
  }

-- | Create a curve point.
mkCurvePoint :: Number -> Number -> CurvePoint
mkCurvePoint x y = { x, y }

-- | Value of an effect parameter.
data EffectParameterValue
  = EPVNumber Number
  | EPVString String
  | EPVBoolean Boolean
  | EPVPoint2D EffectPoint2D
  | EPVPoint3D EffectPoint3D
  | EPVColor EffectRGBA
  | EPVCurve (Array CurvePoint)
  | EPVData String           -- ^ JSON-encoded data
  | EPVNull

derive instance eqEffectParameterValue :: Eq EffectParameterValue

instance showEffectParameterValue :: Show EffectParameterValue where
  show (EPVNumber n) = "(EPVNumber " <> show n <> ")"
  show (EPVString s) = "(EPVString " <> show s <> ")"
  show (EPVBoolean b) = "(EPVBoolean " <> show b <> ")"
  show (EPVPoint2D _) = "(EPVPoint2D ...)"
  show (EPVPoint3D _) = "(EPVPoint3D ...)"
  show (EPVColor _) = "(EPVColor ...)"
  show (EPVCurve _) = "(EPVCurve ...)"
  show (EPVData _) = "(EPVData ...)"
  show EPVNull = "EPVNull"

-- | Option for a dropdown parameter.
type EffectDropdownOption =
  { label :: String
  , value :: EffectParameterValue
  }

-- | Definition of an effect parameter (template).
type EffectParameterDef =
  { name :: String
  , parameterType :: EffectParameterType
  , defaultValue :: EffectParameterValue
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Maybe (Array EffectDropdownOption)
  , animatable :: Boolean
  , group :: Maybe String
  }

-- | Default parameter definition.
defaultEffectParameterDef :: String -> EffectParameterType -> EffectParameterValue -> EffectParameterDef
defaultEffectParameterDef name paramType defaultVal =
  { name
  , parameterType: paramType
  , defaultValue: defaultVal
  , min: Nothing
  , max: Nothing
  , step: Nothing
  , options: Nothing
  , animatable: true
  , group: Nothing
  }

-- | Instance of an effect parameter with current value.
type EffectParameter =
  { id :: String
  , name :: String
  , parameterType :: EffectParameterType
  , value :: EffectParameterValue
  , defaultValue :: EffectParameterValue
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Maybe (Array EffectDropdownOption)
  , animatable :: Boolean
  , group :: Maybe String
  }

-- | Default effect parameter.
defaultEffectParameter :: String -> String -> EffectParameterType -> EffectParameterValue -> EffectParameter
defaultEffectParameter id name paramType defaultVal =
  { id
  , name
  , parameterType: paramType
  , value: defaultVal
  , defaultValue: defaultVal
  , min: Nothing
  , max: Nothing
  , step: Nothing
  , options: Nothing
  , animatable: true
  , group: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // effect // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for an effect.
newtype EffectId = EffectId String

derive instance eqEffectId :: Eq EffectId
derive instance ordEffectId :: Ord EffectId

instance showEffectId :: Show EffectId where
  show (EffectId s) = "(EffectId " <> s <> ")"

-- | Smart constructor for EffectId.
mkEffectId :: String -> Maybe EffectId
mkEffectId "" = Nothing
mkEffectId s = Just (EffectId s)

-- | An effect definition with parameters.
type Effect =
  { id :: EffectId
  , name :: String
  , category :: EffectCategory
  , enabled :: Boolean
  , expanded :: Boolean           -- ^ UI expanded state
  , parameters :: Array EffectParameter
  , fragmentShader :: Maybe String  -- ^ Custom GLSL shader
  }

-- | Default effect.
defaultEffect :: EffectId -> String -> EffectCategory -> Effect
defaultEffect id name category =
  { id
  , name
  , category
  , enabled: true
  , expanded: true
  , parameters: []
  , fragmentShader: Nothing
  }

-- | Check if effect is enabled.
effectEnabled :: Effect -> Boolean
effectEnabled eff = eff.enabled

-- | Instance of an effect on a layer.
type EffectInstance =
  { id :: EffectId
  , effectKey :: String           -- ^ Reference to effect definition
  , name :: String
  , category :: EffectCategory
  , enabled :: Boolean
  , expanded :: Boolean
  , parameters :: Array AnimatablePropertyId  -- ^ Property IDs for animation
  }

-- | Default effect instance.
defaultEffectInstance :: EffectId -> String -> String -> EffectCategory -> EffectInstance
defaultEffectInstance id effectKey name category =
  { id
  , effectKey
  , name
  , category
  , enabled: true
  , expanded: true
  , parameters: []
  }

-- | Effect instance with mesh deformation capabilities.
type MeshDeformEffectInstance =
  { instance :: EffectInstance
  , pins :: Array WarpPin
  , cachedMeshId :: Maybe String
  , meshDirty :: Boolean
  }

-- | Definition of an effect type (template).
type EffectDefinition =
  { name :: String
  , category :: EffectCategory
  , description :: String
  , parameters :: Array EffectParameterDef
  , fragmentShader :: Maybe String
  }

-- | Category information for UI.
type EffectCategoryInfo =
  { label :: String
  , icon :: String
  , description :: String
  }
