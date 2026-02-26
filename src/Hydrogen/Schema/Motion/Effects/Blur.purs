-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // blur
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blur effect enums for motion graphics.
-- |
-- | Defines blur dimensions, radial blur types, and antialiasing quality.

module Hydrogen.Schema.Motion.Effects.Blur
  ( -- * Blur Dimension
    BlurDimension(..)
  , allBlurDimensions
  , blurDimensionToString
  , blurDimensionFromString
  
    -- * Radial Blur Type
  , RadialBlurType(..)
  , allRadialBlurTypes
  , radialBlurTypeToString
  , radialBlurTypeFromString
  
    -- * Antialiasing Quality
  , AntialiasingQuality(..)
  , allAntialiasingQualities
  , antialiasingQualityToString
  , antialiasingQualityFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // blur // dimension
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // radial // blur // type
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // antialiasing // quality
-- ═══════════════════════════════════════════════════════════════════════════════

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
