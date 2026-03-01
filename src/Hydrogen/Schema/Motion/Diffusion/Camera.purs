-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // diffusion // camera
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera export format types for motion-controlled video generation.
-- |
-- | This module provides types for camera motion exports across different
-- | video generation models and 3D software formats.
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Schemas.Exports.CameraSchema` from the
-- | Haskell backend, ensuring type-level compatibility for serialization.
-- |
-- | ## Supported Formats
-- |
-- | - MotionCtrl - Original camera control model
-- | - WanMove - Alibaba's Wan trajectory system
-- | - Uni3C - Universal 3D camera control
-- | - CameraCtrl - Alternative camera control
-- | - Blender - Blender Python export
-- | - FBX - Autodesk FBX format
-- |
-- | ## Coordinate Systems
-- |
-- | - OpenGL: Y-up, right-handed
-- | - OpenCV: Y-down, right-handed  
-- | - Blender: Z-up, right-handed
-- | - Unity: Y-up, left-handed
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - Camera.Types - CameraFormat, CoordinateSystem, EulerOrder, CameraInterpolation
-- | - Camera.Position - Position3D and spatial operations
-- | - Camera.Intrinsics - CameraIntrinsics and constants

module Hydrogen.Schema.Motion.Diffusion.Camera
  ( module Hydrogen.Schema.Motion.Diffusion.Camera.Types
  , module Hydrogen.Schema.Motion.Diffusion.Camera.Position
  , module Hydrogen.Schema.Motion.Diffusion.Camera.Intrinsics
  ) where

import Hydrogen.Schema.Motion.Diffusion.Camera.Types
  ( CameraFormat(CameraMotionCtrl, CameraWanMove, CameraUni3C, CameraCameraCtrl, CameraBlender, CameraFBX)
  , cameraFormatToString
  , cameraFormatFromString
  , allCameraFormats
  , defaultCameraFormat
  , firstCameraFormat
  , lastCameraFormat
  , filterCameraFormats
  , mapCameraFormats
  , CoordinateSystem(CoordOpenGL, CoordOpenCV, CoordBlender, CoordUnity)
  , coordinateSystemToString
  , coordinateSystemFromString
  , allCoordinateSystems
  , defaultCoordinateSystem
  , firstCoordinateSystem
  , lastCoordinateSystem
  , isRightHanded
  , isYUp
  , isZUp
  , filterCoordinateSystems
  , mapCoordinateSystems
  , EulerOrder(EulerXYZ, EulerYXZ, EulerZXY, EulerZYX, EulerXZY, EulerYZX)
  , eulerOrderToString
  , eulerOrderFromString
  , allEulerOrders
  , defaultEulerOrder
  , firstEulerOrder
  , lastEulerOrder
  , filterEulerOrders
  , mapEulerOrders
  , CameraInterpolation(InterpLinear, InterpBezier, InterpSpline)
  , cameraInterpolationToString
  , cameraInterpolationFromString
  , allCameraInterpolations
  , defaultCameraInterpolation
  , firstCameraInterpolation
  , lastCameraInterpolation
  , filterCameraInterpolations
  , mapCameraInterpolations
  )

import Hydrogen.Schema.Motion.Diffusion.Camera.Position
  ( Position3D(Position3D)
  , mkPosition3D
  , originPosition3D
  , translatePosition3D
  , scalePosition3D
  , distanceSquared3D
  , distance3D
  , minPosition3D
  , maxPosition3D
  , lerpPosition3D
  , isInsideBounds3D
  , isOutsideBounds3D
  , arePositionsEqual
  , isCloserThan
  )

import Hydrogen.Schema.Motion.Diffusion.Camera.Intrinsics
  ( CameraIntrinsics(CameraIntrinsics)
  , mkCameraIntrinsics
  , isValidCameraIntrinsics
  , isValidSensorSize
  , defaultCameraIntrinsics
  , cameraMaxFocalLength
  , cameraMaxSensorSize
  , cameraMaxFOV
  , cameraMaxAspectRatio
  , cameraMaxRotationDegrees
  , cameraMaxTimestamp
  , quaternionNormalizationTolerance
  )
