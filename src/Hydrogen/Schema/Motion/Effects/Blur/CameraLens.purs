-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // motion // blur // cameralens
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera Lens Blur Effect — realistic depth-of-field blur.
-- |
-- | Simulates optical lens bokeh with iris shape control.

module Hydrogen.Schema.Motion.Effects.Blur.CameraLens
  ( -- * Camera Lens Blur Effect
    CameraLensBlurEffect
  , defaultCameraLensBlur
  , mkCameraLensBlur
  
  -- * Queries
  , isCameraLensNeutral
  
  -- * Validation
  , validateCameraLensBlur
  ) where

import Prelude
  ( (==)
  , (<)
  , (>)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( IrisShape(IrisHexagon)
  , DepthMapChannel(DepthLuminance)
  , BlurValidationError(BlurOutOfRange)
  , wrapAngle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // camera lens // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera Lens Blur effect — realistic depth-of-field blur.
-- |
-- | Simulates optical lens bokeh with iris shape control.
type CameraLensBlurEffect =
  { blurRadius :: Number          -- ^ Blur amount in pixels (0-500)
  , irisShape :: IrisShape        -- ^ Shape of out-of-focus highlights
  , irisRotation :: Number        -- ^ Rotation of iris shape in degrees (0-360)
  , irisRoundness :: Number       -- ^ Roundness of iris (0-100, 100 = circle)
  , irisAspectRatio :: Number     -- ^ Aspect ratio (0.5-2.0)
  , irisDiffractionFringe :: Number  -- ^ Edge fringing (0-100)
  , highlightGain :: Number       -- ^ Boost bright areas (0-100)
  , highlightThreshold :: Number  -- ^ Threshold for highlight boost (0-255)
  , highlightSaturation :: Number -- ^ Saturation of highlights (0-100)
  , useDepthMap :: Boolean        -- ^ Use depth map for variable blur
  , depthMapChannel :: DepthMapChannel -- ^ Which channel for depth
  , blurFocalDistance :: Number   -- ^ Focal distance when using depth map (0-100)
  }

defaultCameraLensBlur :: CameraLensBlurEffect
defaultCameraLensBlur =
  { blurRadius: 0.0
  , irisShape: IrisHexagon
  , irisRotation: 0.0
  , irisRoundness: 0.0
  , irisAspectRatio: 1.0
  , irisDiffractionFringe: 0.0
  , highlightGain: 0.0
  , highlightThreshold: 255.0
  , highlightSaturation: 100.0
  , useDepthMap: false
  , depthMapChannel: DepthLuminance
  , blurFocalDistance: 0.0
  }

mkCameraLensBlur :: Number -> IrisShape -> Number -> Number -> CameraLensBlurEffect
mkCameraLensBlur radius shape rotation roundness =
  { blurRadius: clampNumber 0.0 500.0 radius
  , irisShape: shape
  , irisRotation: wrapAngle rotation
  , irisRoundness: clampNumber 0.0 100.0 roundness
  , irisAspectRatio: 1.0
  , irisDiffractionFringe: 0.0
  , highlightGain: 0.0
  , highlightThreshold: 255.0
  , highlightSaturation: 100.0
  , useDepthMap: false
  , depthMapChannel: DepthLuminance
  , blurFocalDistance: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

isCameraLensNeutral :: CameraLensBlurEffect -> Boolean
isCameraLensNeutral effect = effect.blurRadius == 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate Camera Lens blur parameters.
validateCameraLensBlur :: CameraLensBlurEffect -> Maybe BlurValidationError
validateCameraLensBlur effect
  | effect.blurRadius < 0.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 500.0)
  | effect.blurRadius > 500.0 = Just (BlurOutOfRange "blurRadius" effect.blurRadius 0.0 500.0)
  | effect.irisRoundness < 0.0 = Just (BlurOutOfRange "irisRoundness" effect.irisRoundness 0.0 100.0)
  | effect.irisRoundness > 100.0 = Just (BlurOutOfRange "irisRoundness" effect.irisRoundness 0.0 100.0)
  | effect.irisAspectRatio < 0.5 = Just (BlurOutOfRange "irisAspectRatio" effect.irisAspectRatio 0.5 2.0)
  | effect.irisAspectRatio > 2.0 = Just (BlurOutOfRange "irisAspectRatio" effect.irisAspectRatio 0.5 2.0)
  | otherwise = Nothing
