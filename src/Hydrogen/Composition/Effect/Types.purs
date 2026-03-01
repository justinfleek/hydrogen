-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // composition // effect // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Effect Types — The sum type for all visual effects.
-- |
-- | This module defines the Effect ADT and EffectCategory enumeration.
-- | All effect spec types are imported from their respective category modules.

module Hydrogen.Composition.Effect.Types
  ( Effect(..)
  , EffectCategory(..)
  , effectCategory
  , effectLabel
  , categoryLabel
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  )

import Hydrogen.Composition.Effect.Blur
  ( GaussianBlurSpec
  , DirectionalBlurSpec
  , RadialBlurSpec
  , BoxBlurSpec
  , SharpenSpec
  )

import Hydrogen.Composition.Effect.Color
  ( BrightnessContrastSpec
  , HueSaturationSpec
  , LevelsSpec
  , CurvesSpec
  , ColorBalanceSpec
  , TintSpec
  , VignetteSpec
  , ExposureSpec
  )

import Hydrogen.Composition.Effect.Distort
  ( DisplacementSpec
  , WarpSpec
  , BulgeSpec
  , RippleSpec
  , TwirlSpec
  )

import Hydrogen.Composition.Effect.Stylize
  ( GlowSpec
  , DropShadowSpec
  , InnerShadowSpec
  , EmbossSpec
  , EdgeDetectSpec
  , PosterizeSpec
  )

import Hydrogen.Composition.Effect.Noise
  ( NoiseOverlaySpec
  , GrainSpec
  )

import Hydrogen.Composition.Effect.StylizeEffects
  ( RGBSplitSpec
  , ScanlinesSpec
  , VHSSpec
  , GlitchSpec
  , PixelateSpec
  , HalftoneSpec
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // effect category
-- ═══════════════════════════════════════════════════════════════════════════════

data EffectCategory
  = CategoryBlur
  | CategoryColor
  | CategoryDistort
  | CategoryStylize
  | CategoryNoise
  | CategoryTime

derive instance eqEffectCategory :: Eq EffectCategory

instance showEffectCategory :: Show EffectCategory where
  show CategoryBlur = "blur"
  show CategoryColor = "color"
  show CategoryDistort = "distort"
  show CategoryStylize = "stylize"
  show CategoryNoise = "noise"
  show CategoryTime = "time"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // effect type
-- ═══════════════════════════════════════════════════════════════════════════════

data Effect
  -- Blur/Sharpen
  = EffectGaussianBlur GaussianBlurSpec
  | EffectDirectionalBlur DirectionalBlurSpec
  | EffectRadialBlur RadialBlurSpec
  | EffectBoxBlur BoxBlurSpec
  | EffectSharpen SharpenSpec
  -- Color
  | EffectBrightnessContrast BrightnessContrastSpec
  | EffectHueSaturation HueSaturationSpec
  | EffectLevels LevelsSpec
  | EffectCurves CurvesSpec
  | EffectColorBalance ColorBalanceSpec
  | EffectTint TintSpec
  | EffectVignette VignetteSpec
  | EffectExposure ExposureSpec
  -- Distort
  | EffectDisplacement DisplacementSpec
  | EffectWarp WarpSpec
  | EffectBulge BulgeSpec
  | EffectRipple RippleSpec
  | EffectTwirl TwirlSpec
  -- Stylize
  | EffectGlow GlowSpec
  | EffectDropShadow DropShadowSpec
  | EffectInnerShadow InnerShadowSpec
  | EffectEmboss EmbossSpec
  | EffectEdgeDetect EdgeDetectSpec
  | EffectPosterize PosterizeSpec
  -- Noise
  | EffectNoiseOverlay NoiseOverlaySpec
  | EffectGrain GrainSpec
  -- Stylize Effects
  | EffectRGBSplit RGBSplitSpec
  | EffectScanlines ScanlinesSpec
  | EffectVHS VHSSpec
  | EffectGlitch GlitchSpec
  | EffectPixelate PixelateSpec
  | EffectHalftone HalftoneSpec

derive instance eqEffect :: Eq Effect

instance showEffect :: Show Effect where
  show (EffectGaussianBlur _) = "GaussianBlur"
  show (EffectDirectionalBlur _) = "DirectionalBlur"
  show (EffectRadialBlur _) = "RadialBlur"
  show (EffectBoxBlur _) = "BoxBlur"
  show (EffectSharpen _) = "Sharpen"
  show (EffectBrightnessContrast _) = "BrightnessContrast"
  show (EffectHueSaturation _) = "HueSaturation"
  show (EffectLevels _) = "Levels"
  show (EffectCurves _) = "Curves"
  show (EffectColorBalance _) = "ColorBalance"
  show (EffectTint _) = "Tint"
  show (EffectVignette _) = "Vignette"
  show (EffectExposure _) = "Exposure"
  show (EffectDisplacement _) = "Displacement"
  show (EffectWarp _) = "Warp"
  show (EffectBulge _) = "Bulge"
  show (EffectRipple _) = "Ripple"
  show (EffectTwirl _) = "Twirl"
  show (EffectGlow _) = "Glow"
  show (EffectDropShadow _) = "DropShadow"
  show (EffectInnerShadow _) = "InnerShadow"
  show (EffectEmboss _) = "Emboss"
  show (EffectEdgeDetect _) = "EdgeDetect"
  show (EffectPosterize _) = "Posterize"
  show (EffectNoiseOverlay _) = "NoiseOverlay"
  show (EffectGrain _) = "Grain"
  show (EffectRGBSplit _) = "RGBSplit"
  show (EffectScanlines _) = "Scanlines"
  show (EffectVHS _) = "VHS"
  show (EffectGlitch _) = "Glitch"
  show (EffectPixelate _) = "Pixelate"
  show (EffectHalftone _) = "Halftone"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // category lookup
-- ═══════════════════════════════════════════════════════════════════════════════

effectCategory :: Effect -> EffectCategory
effectCategory (EffectGaussianBlur _) = CategoryBlur
effectCategory (EffectDirectionalBlur _) = CategoryBlur
effectCategory (EffectRadialBlur _) = CategoryBlur
effectCategory (EffectBoxBlur _) = CategoryBlur
effectCategory (EffectSharpen _) = CategoryBlur
effectCategory (EffectBrightnessContrast _) = CategoryColor
effectCategory (EffectHueSaturation _) = CategoryColor
effectCategory (EffectLevels _) = CategoryColor
effectCategory (EffectCurves _) = CategoryColor
effectCategory (EffectColorBalance _) = CategoryColor
effectCategory (EffectTint _) = CategoryColor
effectCategory (EffectVignette _) = CategoryColor
effectCategory (EffectExposure _) = CategoryColor
effectCategory (EffectDisplacement _) = CategoryDistort
effectCategory (EffectWarp _) = CategoryDistort
effectCategory (EffectBulge _) = CategoryDistort
effectCategory (EffectRipple _) = CategoryDistort
effectCategory (EffectTwirl _) = CategoryDistort
effectCategory (EffectGlow _) = CategoryStylize
effectCategory (EffectDropShadow _) = CategoryStylize
effectCategory (EffectInnerShadow _) = CategoryStylize
effectCategory (EffectEmboss _) = CategoryStylize
effectCategory (EffectEdgeDetect _) = CategoryStylize
effectCategory (EffectPosterize _) = CategoryStylize
effectCategory (EffectNoiseOverlay _) = CategoryNoise
effectCategory (EffectGrain _) = CategoryNoise
effectCategory (EffectRGBSplit _) = CategoryStylize
effectCategory (EffectScanlines _) = CategoryStylize
effectCategory (EffectVHS _) = CategoryStylize
effectCategory (EffectGlitch _) = CategoryStylize
effectCategory (EffectPixelate _) = CategoryStylize
effectCategory (EffectHalftone _) = CategoryStylize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get display label for an effect.
effectLabel :: Effect -> String
effectLabel = show

-- | Get display label for an effect category.
categoryLabel :: EffectCategory -> String
categoryLabel = show
