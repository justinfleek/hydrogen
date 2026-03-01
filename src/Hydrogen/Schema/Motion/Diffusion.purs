-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // diffusion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Diffusion model types for AI-generated content.
-- |
-- | This module is the leader module for the Diffusion subsystem, re-exporting
-- | all types from subdirectory modules for convenient access.
-- |
-- | ## Architecture
-- |
-- | The Diffusion module provides types for defining AI-generated content
-- | layers in LATTICE compositions. It supports multiple diffusion model
-- | families for image, video, 3D, and motion generation.
-- |
-- | ## Submodules
-- |
-- | - **Model** — Diffusion model enumeration types (ImageModel, VideoModel, etc.)
-- | - **WanMove** — Wan trajectory and motion pattern types
-- | - **TTM** — Time-to-Move multi-layer motion mask types
-- | - **Camera** — Camera export formats and coordinate systems
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Diffusion
-- |   ( DiffusionModel(..)
-- |   , VideoModel(..)
-- |   , WanMoveTrajectory
-- |   , TTMExport
-- |   , CameraFormat(..)
-- |   )
-- | ```

module Hydrogen.Schema.Motion.Diffusion
  ( -- * Re-exports from Model
    module Hydrogen.Schema.Motion.Diffusion.Model
    
  -- * Re-exports from WanMove (excluding isValidMetadata conflict)
  , module WanMove
  
  -- * Re-exports from TTM (qualified as TTM, excluding translateTrajectory conflict)
  , module TTM
  
  -- * Re-exports from Camera
  , module Hydrogen.Schema.Motion.Diffusion.Camera
  ) where

import Hydrogen.Schema.Motion.Diffusion.Model
  ( ImageModel(..)
  , imageModelToString
  , imageModelFromString
  , isImageModelFast
  , isImageModelHighQuality
  , allImageModels
  , firstImageModel
  , lastImageModel
  , filterImageModels
  , mapImageModels
  , VideoModel(..)
  , videoModelToString
  , videoModelFromString
  , videoModelMaxFrames
  , videoModelMaxResolution
  , allVideoModels
  , firstVideoModel
  , lastVideoModel
  , filterVideoModels
  , mapVideoModels
  , videoModelsWithMinFrames
  , videoModelsWithMinResolution
  , Model3D(..)
  , model3DToString
  , model3DFromString
  , all3DModels
  , first3DModel
  , last3DModel
  , map3DModels
  , EditModel(..)
  , editModelToString
  , editModelFromString
  , allEditModels
  , firstEditModel
  , lastEditModel
  , mapEditModels
  , MotionModel(..)
  , motionModelToString
  , motionModelFromString
  , allMotionModels
  , firstMotionModel
  , lastMotionModel
  , mapMotionModels
  , DiffusionModel(..)
  , diffusionModelToString
  , diffusionModelFromString
  , diffusionModelCategory
  , lookupAndTransform
  , ModelCategory(..)
  )

import Hydrogen.Schema.Motion.Diffusion.WanMove
  ( FlowPattern(..)
  , flowPatternToString
  , flowPatternFromString
  , allFlowPatterns
  , defaultFlowPattern
  , lastFlowPattern
  , flowPatternStrings
  , MorphShapeType(..)
  , morphShapeTypeToString
  , morphShapeTypeFromString
  , allMorphShapeTypes
  , defaultMorphShapeType
  , MorphEasing(..)
  , morphEasingToString
  , morphEasingFromString
  , allMorphEasings
  , defaultMorphEasing
  , ShapeEasing(..)
  , shapeEasingToString
  , shapeEasingFromString
  , allShapeEasings
  , defaultShapeEasing
  , AttractorType(..)
  , attractorTypeToString
  , attractorTypeFromString
  , allAttractorTypes
  , defaultAttractorType
  , attractorTypeStrings
  , DataMapping(..)
  , dataMappingToString
  , dataMappingFromString
  , allDataMappings
  , defaultDataMapping
  , ForceFalloff(..)
  , forceFalloffToString
  , forceFalloffFromString
  , allForceFalloffs
  , defaultForceFalloff
  , InitialDistribution(..)
  , initialDistributionToString
  , initialDistributionFromString
  , allInitialDistributions
  , defaultInitialDistribution
  , ShapeType(..)
  , shapeTypeToString
  , shapeTypeFromString
  , allShapeTypes
  , defaultShapeType
  , lastShapeType
  , shapeTypeStrings
  , TrackPoint(..)
  , mkTrackPoint
  , isValidTrackPoint
  , WanMoveMetadata(..)
  , mkWanMoveMetadata
  , WanMoveTrajectory(..)
  , mkWanMoveTrajectory
  , wanMoveMaxDimension
  , wanMoveMaxPoints
  , wanMoveMaxFrames
  , wanMoveMaxFPS
  , mapTrackPoints
  , flipTrajectoryVertical
  , flipTrajectoryHorizontal
  , trackPointDistanceSquared
  ) as WanMove

import Hydrogen.Schema.Motion.Diffusion.TTM
  ( TTMModel(..)
  , ttmModelToString
  , ttmModelFromString
  , allTTMModels
  , defaultTTMModel
  , firstTTMModel
  , lastTTMModel
  , ttmMaxFrames
  , ttmMaxDimension
  , ttmMaxLayers
  , ttmMaxTweakIndex
  , ttmMaxInferenceSteps
  , TrajectoryPoint(..)
  , mkTrajectoryPoint
  , isValidTrajectoryPoint
  , trajectoryPointAtFrame
  , trajectoryFirstPoint
  , trajectoryLastPoint
  , TTMLayerExport(..)
  , mkTTMLayerExport
  , isValidLayerExport
  , TTMModelConfig(..)
  , mkTTMModelConfig
  , isValidModelConfig
  , defaultModelConfig
  , TTMMetadata(..)
  , mkTTMMetadata
  , isValidMetadata
  , metadataLayerCount
  , TTMExport(..)
  , mkTTMExport
  , isValidExport
  , mapTrajectoryPoints
  , translateTrajectory
  , scaleTrajectory
  , trajectoryLength
  , layerTrajectoryBounds
  ) as TTM

import Hydrogen.Schema.Motion.Diffusion.Camera
  ( CameraFormat(..)
  , cameraFormatToString
  , cameraFormatFromString
  , allCameraFormats
  , defaultCameraFormat
  , firstCameraFormat
  , lastCameraFormat
  , filterCameraFormats
  , mapCameraFormats
  , CoordinateSystem(..)
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
  , EulerOrder(..)
  , eulerOrderToString
  , eulerOrderFromString
  , allEulerOrders
  , defaultEulerOrder
  , firstEulerOrder
  , lastEulerOrder
  , filterEulerOrders
  , mapEulerOrders
  , CameraInterpolation(..)
  , cameraInterpolationToString
  , cameraInterpolationFromString
  , allCameraInterpolations
  , defaultCameraInterpolation
  , firstCameraInterpolation
  , lastCameraInterpolation
  , filterCameraInterpolations
  , mapCameraInterpolations
  , Position3D(..)
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
  , CameraIntrinsics(..)
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
