-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // blur
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blur Effects — Complete blur effect types for motion graphics.
-- |
-- | ## After Effects Parity
-- |
-- | Includes full property records for:
-- | - Gaussian Blur
-- | - Box Blur
-- | - Fast Blur
-- | - Directional Blur
-- | - Radial Blur
-- | - Camera Lens Blur
-- | - Compound Blur
-- | - Bilateral Blur (edge-preserving)
-- | - Smart Blur (edge-preserving, simplified)
-- | - Channel Blur (per-channel)
-- | - Sharpen
-- | - Unsharp Mask
-- |
-- | All blur amounts are in pixels.
-- |
-- | This is a leader module that re-exports from submodules.

module Hydrogen.Schema.Motion.Effects.Blur
  ( -- * Blur Dimension
    module Hydrogen.Schema.Motion.Effects.Blur.Types
  
  -- * Gaussian Blur
  , module Hydrogen.Schema.Motion.Effects.Blur.Gaussian
  
  -- * Box Blur
  , module Hydrogen.Schema.Motion.Effects.Blur.Box
  
  -- * Directional Blur
  , module Hydrogen.Schema.Motion.Effects.Blur.Directional
  
  -- * Radial Blur
  , module Hydrogen.Schema.Motion.Effects.Blur.Radial
  
  -- * Camera Lens Blur
  , module Hydrogen.Schema.Motion.Effects.Blur.CameraLens
  
  -- * Edge-Preserving Blurs
  , module Hydrogen.Schema.Motion.Effects.Blur.EdgePreserving
  
  -- * Channel Blur
  , module Hydrogen.Schema.Motion.Effects.Blur.Channel
  
  -- * Sharpen
  , module Hydrogen.Schema.Motion.Effects.Blur.Sharpen
  
  -- * Miscellaneous
  , module Hydrogen.Schema.Motion.Effects.Blur.Misc
  ) where

import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( BlurDimension(BDHorizontal, BDVertical, BDBoth)
  , allBlurDimensions
  , blurDimensionToString
  , blurDimensionFromString
  , combineDimensions
  , RadialBlurType(RBTSpin, RBTZoom)
  , allRadialBlurTypes
  , radialBlurTypeToString
  , radialBlurTypeFromString
  , AntialiasingQuality(AAQLow, AAQMedium, AAQHigh)
  , allAntialiasingQualities
  , antialiasingQualityToString
  , antialiasingQualityFromString
  , IrisShape(IrisTriangle, IrisSquare, IrisPentagon, IrisHexagon, IrisHeptagon, IrisOctagon, IrisDecagon, IrisCircle)
  , irisShapeToString
  , irisShapeFromString
  , DepthMapChannel(DepthLuminance, DepthRed, DepthGreen, DepthBlue, DepthAlpha)
  , SmartBlurMode(SBMNormal, SBMEdgeOnly, SBMOverlay)
  , SmartBlurQuality(SBQLow, SBQMedium, SBQHigh)
  , BlurValidationError(BlurOutOfRange, InvalidIterations, InvalidCenter)
  )

import Hydrogen.Schema.Motion.Effects.Blur.Gaussian
  ( GaussianBlurEffect
  , defaultGaussianBlur
  , mkGaussianBlur
  , isGaussianNeutral
  , hasVisibleBlur
  , validateGaussianBlur
  , validateAllGaussianBlurs
  , gaussianBlurToString
  , compareBlurIntensity
  , isStrongerBlur
  , isWeakerBlur
  , combineGaussianBlurs
  , scaleGaussianBlur
  , lerpGaussianBlur
  , mapBlurAmount
  , CombinableGaussian(CombinableGaussian)
  , toCombinableGaussian
  , fromCombinableGaussian
  )

import Hydrogen.Schema.Motion.Effects.Blur.Box
  ( BoxBlurEffect
  , defaultBoxBlur
  , mkBoxBlur
  , isBoxNeutral
  , validateBoxBlur
  , boxBlurToString
  )

import Hydrogen.Schema.Motion.Effects.Blur.Directional
  ( DirectionalBlurEffect
  , defaultDirectionalBlur
  , mkDirectionalBlur
  , isDirectionalNeutral
  , directionalBlurToString
  , negateDirectionalBlur
  , scaleDirectionalBlur
  , lerpDirectionalBlur
  )

import Hydrogen.Schema.Motion.Effects.Blur.Radial
  ( RadialBlurEffect
  , defaultRadialBlur
  , mkRadialBlur
  , isRadialNeutral
  , validateRadialBlur
  , radialBlurToString
  )

import Hydrogen.Schema.Motion.Effects.Blur.CameraLens
  ( CameraLensBlurEffect
  , defaultCameraLensBlur
  , mkCameraLensBlur
  , isCameraLensNeutral
  , validateCameraLensBlur
  )

import Hydrogen.Schema.Motion.Effects.Blur.EdgePreserving
  ( BilateralBlurEffect
  , defaultBilateralBlur
  , mkBilateralBlur
  , isBilateralNeutral
  , bilateralBlurToString
  , SmartBlurEffect
  , defaultSmartBlur
  , mkSmartBlur
  , isSmartBlurNeutral
  )

import Hydrogen.Schema.Motion.Effects.Blur.Channel
  ( ChannelBlurEffect
  , defaultChannelBlur
  , mkChannelBlur
  , isChannelBlurNeutral
  , hasChannelDifference
  , isUniformChannelBlur
  , channelBlurToString
  , invertChannelBlur
  , applyToAllChannels
  , normalizeChannelBlur
  , mapChannelBlurs
  )

import Hydrogen.Schema.Motion.Effects.Blur.Sharpen
  ( SharpenEffect
  , defaultSharpen
  , mkSharpen
  , isSharpenNeutral
  , sharpenToString
  , UnsharpMaskEffect
  , defaultUnsharpMask
  , mkUnsharpMask
  , isUnsharpMaskNeutral
  , unsharpMaskToString
  )

import Hydrogen.Schema.Motion.Effects.Blur.Misc
  ( CompoundBlurEffect
  , defaultCompoundBlur
  , mkCompoundBlur
  , FastBlurEffect
  , defaultFastBlur
  , mkFastBlur
  )
