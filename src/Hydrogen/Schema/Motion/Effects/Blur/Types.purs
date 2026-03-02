-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // blur // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for blur effects.
-- |
-- | This module contains shared enumerations and validation types used
-- | across all blur effect implementations.

module Hydrogen.Schema.Motion.Effects.Blur.Types
  ( -- * Blur Dimension
    BlurDimension(BDHorizontal, BDVertical, BDBoth)
  , allBlurDimensions
  , blurDimensionToString
  , blurDimensionFromString
  , combineDimensions
  
  -- * Radial Blur Type
  , RadialBlurType(RBTSpin, RBTZoom)
  , allRadialBlurTypes
  , radialBlurTypeToString
  , radialBlurTypeFromString
  
  -- * Antialiasing Quality
  , AntialiasingQuality(AAQLow, AAQMedium, AAQHigh)
  , allAntialiasingQualities
  , antialiasingQualityToString
  , antialiasingQualityFromString
  
  -- * Iris Shape
  , IrisShape(IrisTriangle, IrisSquare, IrisPentagon, IrisHexagon, IrisHeptagon, IrisOctagon, IrisDecagon, IrisCircle)
  , irisShapeToString
  , irisShapeFromString
  
  -- * Depth Map Channel
  , DepthMapChannel(DepthLuminance, DepthRed, DepthGreen, DepthBlue, DepthAlpha)
  
  -- * Smart Blur Types
  , SmartBlurMode(SBMNormal, SBMEdgeOnly, SBMOverlay)
  , SmartBlurQuality(SBQLow, SBQMedium, SBQHigh)
  
  -- * Validation
  , BlurValidationError(BlurOutOfRange, InvalidIterations, InvalidCenter)
  
  -- * Internal Utilities
  , clampInt
  , wrapAngle
  , lerpNum
  , lerpAngle
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  , (-)
  , (*)
  , (+)
  , (/)
  , (<)
  , (>)
  , (>=)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // blur // dimension
-- ═════════════════════════════════════════════════════════════════════════════

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

-- | All blur dimensions for enumeration
allBlurDimensions :: Array BlurDimension
allBlurDimensions = [ BDHorizontal, BDVertical, BDBoth ]

blurDimensionToString :: BlurDimension -> String
blurDimensionToString BDHorizontal = "horizontal"
blurDimensionToString BDVertical = "vertical"
blurDimensionToString BDBoth = "both"

blurDimensionFromString :: String -> Maybe BlurDimension
blurDimensionFromString "horizontal" = Just BDHorizontal
blurDimensionFromString "vertical" = Just BDVertical
blurDimensionFromString "both" = Just BDBoth
blurDimensionFromString _ = Nothing

-- | Combine blur dimensions - if either is Both, result is Both.
combineDimensions :: BlurDimension -> BlurDimension -> BlurDimension
combineDimensions BDBoth _ = BDBoth
combineDimensions _ BDBoth = BDBoth
combineDimensions BDHorizontal BDVertical = BDBoth
combineDimensions BDVertical BDHorizontal = BDBoth
combineDimensions a _ = a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // radial // blur // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of radial blur.
data RadialBlurType
  = RBTSpin   -- ^ Rotational blur around center
  | RBTZoom   -- ^ Zoom blur from center

derive instance eqRadialBlurType :: Eq RadialBlurType
derive instance ordRadialBlurType :: Ord RadialBlurType

instance showRadialBlurType :: Show RadialBlurType where
  show RBTSpin = "RBTSpin"
  show RBTZoom = "RBTZoom"

-- | All radial blur types for enumeration
allRadialBlurTypes :: Array RadialBlurType
allRadialBlurTypes = [ RBTSpin, RBTZoom ]

radialBlurTypeToString :: RadialBlurType -> String
radialBlurTypeToString RBTSpin = "spin"
radialBlurTypeToString RBTZoom = "zoom"

radialBlurTypeFromString :: String -> Maybe RadialBlurType
radialBlurTypeFromString "spin" = Just RBTSpin
radialBlurTypeFromString "zoom" = Just RBTZoom
radialBlurTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // antialiasing // quality
-- ═════════════════════════════════════════════════════════════════════════════

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

-- | All antialiasing quality levels for enumeration
allAntialiasingQualities :: Array AntialiasingQuality
allAntialiasingQualities = [ AAQLow, AAQMedium, AAQHigh ]

antialiasingQualityToString :: AntialiasingQuality -> String
antialiasingQualityToString AAQLow = "low"
antialiasingQualityToString AAQMedium = "medium"
antialiasingQualityToString AAQHigh = "high"

antialiasingQualityFromString :: String -> Maybe AntialiasingQuality
antialiasingQualityFromString "low" = Just AAQLow
antialiasingQualityFromString "medium" = Just AAQMedium
antialiasingQualityFromString "high" = Just AAQHigh
antialiasingQualityFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // iris // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Iris shape for camera lens blur (bokeh shape).
data IrisShape
  = IrisTriangle     -- ^ 3-sided
  | IrisSquare       -- ^ 4-sided
  | IrisPentagon     -- ^ 5-sided
  | IrisHexagon      -- ^ 6-sided (most common)
  | IrisHeptagon     -- ^ 7-sided
  | IrisOctagon      -- ^ 8-sided
  | IrisDecagon      -- ^ 10-sided
  | IrisCircle       -- ^ Perfect circle (infinite sides)

derive instance eqIrisShape :: Eq IrisShape
derive instance ordIrisShape :: Ord IrisShape

instance showIrisShape :: Show IrisShape where
  show IrisTriangle = "Triangle"
  show IrisSquare = "Square"
  show IrisPentagon = "Pentagon"
  show IrisHexagon = "Hexagon"
  show IrisHeptagon = "Heptagon"
  show IrisOctagon = "Octagon"
  show IrisDecagon = "Decagon"
  show IrisCircle = "Circle"

irisShapeToString :: IrisShape -> String
irisShapeToString = show

irisShapeFromString :: String -> Maybe IrisShape
irisShapeFromString "Triangle" = Just IrisTriangle
irisShapeFromString "Square" = Just IrisSquare
irisShapeFromString "Pentagon" = Just IrisPentagon
irisShapeFromString "Hexagon" = Just IrisHexagon
irisShapeFromString "Heptagon" = Just IrisHeptagon
irisShapeFromString "Octagon" = Just IrisOctagon
irisShapeFromString "Decagon" = Just IrisDecagon
irisShapeFromString "Circle" = Just IrisCircle
irisShapeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // depth // map // channel
-- ═════════════════════════════════════════════════════════════════════════════

-- | Depth map channel selection.
data DepthMapChannel
  = DepthLuminance   -- ^ Use luminance
  | DepthRed         -- ^ Use red channel
  | DepthGreen       -- ^ Use green channel
  | DepthBlue        -- ^ Use blue channel
  | DepthAlpha       -- ^ Use alpha channel

derive instance eqDepthMapChannel :: Eq DepthMapChannel
derive instance ordDepthMapChannel :: Ord DepthMapChannel

instance showDepthMapChannel :: Show DepthMapChannel where
  show DepthLuminance = "Luminance"
  show DepthRed = "Red"
  show DepthGreen = "Green"
  show DepthBlue = "Blue"
  show DepthAlpha = "Alpha"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // smart // blur // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smart Blur mode.
data SmartBlurMode
  = SBMNormal      -- ^ Standard blur with edge preservation
  | SBMEdgeOnly    -- ^ Show only detected edges (white on black)
  | SBMOverlay     -- ^ Overlay edges on blurred result

derive instance eqSmartBlurMode :: Eq SmartBlurMode
derive instance ordSmartBlurMode :: Ord SmartBlurMode

instance showSmartBlurMode :: Show SmartBlurMode where
  show SBMNormal = "Normal"
  show SBMEdgeOnly = "Edge Only"
  show SBMOverlay = "Overlay Edge"

-- | Smart Blur quality.
data SmartBlurQuality
  = SBQLow     -- ^ Fast, lower quality
  | SBQMedium  -- ^ Balanced
  | SBQHigh    -- ^ Best quality

derive instance eqSmartBlurQuality :: Eq SmartBlurQuality
derive instance ordSmartBlurQuality :: Ord SmartBlurQuality

instance showSmartBlurQuality :: Show SmartBlurQuality where
  show SBQLow = "Low"
  show SBQMedium = "Medium"
  show SBQHigh = "High"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation errors for blur effects.
data BlurValidationError
  = BlurOutOfRange String Number Number Number  -- ^ field, value, min, max
  | InvalidIterations Int
  | InvalidCenter Number Number

derive instance eqBlurValidationError :: Eq BlurValidationError

instance showBlurValidationError :: Show BlurValidationError where
  show (BlurOutOfRange field val minV maxV) =
    field <> " value " <> show val <> " out of range [" <> 
    show minV <> ", " <> show maxV <> "]"
  show (InvalidIterations n) =
    "iterations " <> show n <> " must be between 1 and 10"
  show (InvalidCenter x y) =
    "center (" <> show x <> ", " <> show y <> ") must be in [0, 1]"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // internal utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp an Int to a range.
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal val
  | val < minVal = minVal
  | val > maxVal = maxVal
  | otherwise = val

-- | Wrap angle to 0-360 range.
wrapAngle :: Number -> Number
wrapAngle angle =
  let normalized = angle - 360.0 * floor (angle / 360.0)
  in if normalized < 0.0 then normalized + 360.0 else normalized

-- | Floor function for wrapping.
floor :: Number -> Number
floor x = 
  let truncated = if x >= 0.0 then x else x - 1.0
  in truncated - (truncated - x)

-- | Interpolate between two numbers.
lerpNum :: Number -> Number -> Number -> Number
lerpNum t a b = a + t * (b - a)

-- | Interpolate between two angles (shortest path).
lerpAngle :: Number -> Number -> Number -> Number
lerpAngle t from to =
  let diff = to - from
      -- Adjust for shortest path around circle
      adjustedDiff = 
        if diff > 180.0 then diff - 360.0
        else if diff < (-180.0) then diff + 360.0
        else diff
  in wrapAngle (from + t * adjustedDiff)
