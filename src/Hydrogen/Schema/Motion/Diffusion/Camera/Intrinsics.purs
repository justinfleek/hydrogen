-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // diffusion // camera // intrinsics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera intrinsic parameters for lens and sensor characteristics.
-- |
-- | This module provides the CameraIntrinsics type representing internal
-- | camera parameters like focal length, sensor size, field of view,
-- | and aspect ratio.

module Hydrogen.Schema.Motion.Diffusion.Camera.Intrinsics
  ( -- * Camera Intrinsics
    CameraIntrinsics(CameraIntrinsics)
  , mkCameraIntrinsics
  , isValidCameraIntrinsics
  , isValidSensorSize
  , defaultCameraIntrinsics
  
  -- * Constants
  , cameraMaxFocalLength
  , cameraMaxSensorSize
  , cameraMaxFOV
  , cameraMaxAspectRatio
  , cameraMaxRotationDegrees
  , cameraMaxTimestamp
  , quaternionNormalizationTolerance
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<=)
  , (>)
  , (&&)
  , (<>)
  , ($)
  , not
  , otherwise
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // camera // intrinsics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera intrinsic parameters.
-- |
-- | Defines the internal characteristics of the camera lens and sensor.
newtype CameraIntrinsics = CameraIntrinsics
  { focalLength :: Number           -- ^ Focal length in mm
  , sensorWidth :: Maybe Number     -- ^ Sensor width in mm (optional)
  , sensorHeight :: Maybe Number    -- ^ Sensor height in mm (optional)
  , fov :: Number                   -- ^ Field of view in degrees
  , aspectRatio :: Number           -- ^ Aspect ratio (width / height)
  }

derive instance eqCameraIntrinsics :: Eq CameraIntrinsics

instance showCameraIntrinsics :: Show CameraIntrinsics where
  show (CameraIntrinsics ci) =
    "CameraIntrinsics(f=" <> show ci.focalLength <> 
    "mm, fov=" <> show ci.fov <> 
    "deg, ar=" <> show ci.aspectRatio <> ")"

-- | Validate sensor size (optional parameter).
isValidSensorSize :: Maybe Number -> Boolean
isValidSensorSize Nothing = true
isValidSensorSize (Just s) = s > 0.0 && s <= cameraMaxSensorSize

-- | Smart constructor for camera intrinsics with validation.
mkCameraIntrinsics 
  :: Number 
  -> Maybe Number 
  -> Maybe Number 
  -> Number 
  -> Number 
  -> Maybe CameraIntrinsics
mkCameraIntrinsics focalLength sensorWidth sensorHeight fov aspectRatio
  | focalLength <= 0.0 = Nothing
  | focalLength > cameraMaxFocalLength = Nothing
  | not (isValidSensorSize sensorWidth) = Nothing
  | not (isValidSensorSize sensorHeight) = Nothing
  | fov <= 0.0 = Nothing
  | fov > cameraMaxFOV = Nothing
  | aspectRatio <= 0.0 = Nothing
  | aspectRatio > cameraMaxAspectRatio = Nothing
  | otherwise = Just $ CameraIntrinsics 
      { focalLength, sensorWidth, sensorHeight, fov, aspectRatio }

-- | Validate camera intrinsics.
isValidCameraIntrinsics :: CameraIntrinsics -> Boolean
isValidCameraIntrinsics (CameraIntrinsics ci) =
  ci.focalLength > 0.0 && ci.focalLength <= cameraMaxFocalLength &&
  isValidSensorSize ci.sensorWidth &&
  isValidSensorSize ci.sensorHeight &&
  ci.fov > 0.0 && ci.fov <= cameraMaxFOV &&
  ci.aspectRatio > 0.0 && ci.aspectRatio <= cameraMaxAspectRatio

-- | Default camera intrinsics.
-- |
-- | Approximates a 50mm lens on a full-frame sensor.
defaultCameraIntrinsics :: CameraIntrinsics
defaultCameraIntrinsics = CameraIntrinsics
  { focalLength: 50.0
  , sensorWidth: Just 36.0
  , sensorHeight: Just 24.0
  , fov: 46.8
  , aspectRatio: 1.5
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum focal length in mm.
cameraMaxFocalLength :: Number
cameraMaxFocalLength = 10000.0

-- | Maximum sensor size in mm.
cameraMaxSensorSize :: Number
cameraMaxSensorSize = 100.0

-- | Maximum field of view in degrees.
cameraMaxFOV :: Number
cameraMaxFOV = 180.0

-- | Maximum aspect ratio.
cameraMaxAspectRatio :: Number
cameraMaxAspectRatio = 10.0

-- | Maximum rotation in degrees.
cameraMaxRotationDegrees :: Number
cameraMaxRotationDegrees = 360.0

-- | Maximum timestamp in seconds (24 hours).
cameraMaxTimestamp :: Number
cameraMaxTimestamp = 86400.0

-- | Tolerance for quaternion normalization validation.
quaternionNormalizationTolerance :: Number
quaternionNormalizationTolerance = 0.1
