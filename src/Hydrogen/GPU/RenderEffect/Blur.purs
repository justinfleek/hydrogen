-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // render-effect/blur
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blur effects for the RenderEffect system.
-- |
-- | Provides four blur variants optimized for different use cases:
-- | - **Gaussian**: Classic soft blur for backgrounds, defocus
-- | - **Directional**: Motion blur in a specific direction
-- | - **Radial**: Spin/zoom blur from a center point
-- | - **Zoom**: Motion zoom blur for focus effects

module Hydrogen.GPU.RenderEffect.Blur
  ( -- * Blur Effect Type
    BlurEffect(BlurGaussian, BlurDirectional, BlurRadial, BlurZoom)
   
  -- * Blur Variants
  , GaussianBlur(GaussianBlur)
  , DirectionalBlur(DirectionalBlur)
  , RadialBlur(RadialBlur)
  , ZoomBlur(ZoomBlur)
   
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.ComputeKernel
  ( BlurQuality
  , RadialBlurType
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // blur effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blur effect variants
-- |
-- | Each blur type maps to optimized GPU compute kernels. Quality settings
-- | control the kernel size vs performance tradeoff.
data BlurEffect
  = BlurGaussian GaussianBlur
  | BlurDirectional DirectionalBlur
  | BlurRadial RadialBlur
  | BlurZoom ZoomBlur

derive instance eqBlurEffect :: Eq BlurEffect

instance showBlurEffect :: Show BlurEffect where
  show (BlurGaussian g) = "(BlurGaussian " <> show g <> ")"
  show (BlurDirectional d) = "(BlurDirectional " <> show d <> ")"
  show (BlurRadial r) = "(BlurRadial " <> show r <> ")"
  show (BlurZoom z) = "(BlurZoom " <> show z <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // blur variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gaussian blur — classic soft blur
-- |
-- | Implements a separable Gaussian kernel for efficient O(n) blur.
-- | Quality setting controls kernel size: Low=9, Medium=17, High=33.
newtype GaussianBlur = GaussianBlur
  { radius :: Number         -- Blur radius in pixels (0-100)
  , quality :: BlurQuality   -- Quality/performance tradeoff
  }

derive instance eqGaussianBlur :: Eq GaussianBlur

instance showGaussianBlur :: Show GaussianBlur where
  show (GaussianBlur b) = "(GaussianBlur radius:" <> show b.radius <> ")"

-- | Directional blur — motion in a direction
-- |
-- | Samples along a line in the specified direction. Used for motion blur,
-- | wind effects, and directional speed lines.
newtype DirectionalBlur = DirectionalBlur
  { angle :: Number          -- Direction in degrees (0-360)
  , distance :: Number       -- Blur distance in pixels
  , quality :: BlurQuality
  }

derive instance eqDirectionalBlur :: Eq DirectionalBlur

instance showDirectionalBlur :: Show DirectionalBlur where
  show (DirectionalBlur b) = "(DirectionalBlur angle:" <> show b.angle <> ")"

-- | Radial blur — spin/zoom from center
-- |
-- | Two modes:
-- | - **Spin**: Circular motion blur (rotation effect)
-- | - **Zoom**: Radial motion blur (explosion/implosion effect)
newtype RadialBlur = RadialBlur
  { centerX :: Number        -- Center X (0.0-1.0 normalized)
  , centerY :: Number        -- Center Y (0.0-1.0 normalized)
  , amount :: Number         -- Blur amount (0-100)
  , blurType :: RadialBlurType
  }

derive instance eqRadialBlur :: Eq RadialBlur

instance showRadialBlur :: Show RadialBlur where
  show (RadialBlur b) = "(RadialBlur amount:" <> show b.amount <> ")"

-- | Zoom blur — radial motion blur
-- |
-- | Simplified zoom blur for common use cases. For full control,
-- | use RadialBlur with RadialTypeZoom.
newtype ZoomBlur = ZoomBlur
  { centerX :: Number
  , centerY :: Number
  , strength :: Number       -- Zoom strength (0-100)
  }

derive instance eqZoomBlur :: Eq ZoomBlur

instance showZoomBlur :: Show ZoomBlur where
  show (ZoomBlur b) = "(ZoomBlur strength:" <> show b.strength <> ")"
