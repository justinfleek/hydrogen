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
  ( ImageModel(IMFlux2Dev, IMFlux2Pro, IMFlux2Schnell, IMZImage, IMQwenImage2509, IMSDXL, IMSD3, IMDalle3, IMMidjourney, IMIdeogram2)
  , imageModelToString
  , imageModelFromString
  , isImageModelFast
  , isImageModelHighQuality
  , allImageModels
  , firstImageModel
  , lastImageModel
  , filterImageModels
  , mapImageModels
  , VideoModel(VMWan22, VMWan21, VMCogVideoX, VMCogVideoX5B, VMSVD, VMSVDXT, VMATI, VMRunway, VMKling, VMPika, VMLuma, VMHunyuanVideo)
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
  , Model3D(M3DHunyuan3D, M3DTrellis2, M3DTripoSR, M3DLGMesh, M3DInstant3D, M3DZero123Plus, M3DMeshAnything)
  , model3DToString
  , model3DFromString
  , all3DModels
  , first3DModel
  , last3DModel
  , map3DModels
  , EditModel(EMQwenImageEdit2511, EMZImageEdit, EMInstructPix2Pix, EMSDEdit, EMControlNetInpaint, EMFluxFill)
  , editModelToString
  , editModelFromString
  , allEditModels
  , firstEditModel
  , lastEditModel
  , mapEditModels
  , MotionModel(MMMotionCtrl, MMUni3C, MMWanMove, MMTimeToMove, MMCameraCtrl, MMAnimateDiff, MMDragAnything)
  , motionModelToString
  , motionModelFromString
  , allMotionModels
  , firstMotionModel
  , lastMotionModel
  , mapMotionModels
  , DiffusionModel(DMImage, DMVideo, DM3D, DMEdit, DMMotion)
  , diffusionModelToString
  , diffusionModelFromString
  , diffusionModelCategory
  , lookupAndTransform
  , ModelCategory(MCImage, MCVideo, MC3D, MCEdit, MCMotion)
  )

import Hydrogen.Schema.Motion.Diffusion.WanMove
  ( FlowPattern(FlowSpiral, FlowWave, FlowExplosion, FlowVortex, FlowDataRiver, FlowMorph, FlowSwarm)
  , flowPatternToString
  , flowPatternFromString
  , allFlowPatterns
  , defaultFlowPattern
  , lastFlowPattern
  , flowPatternStrings
  , MorphShapeType(MorphCircle, MorphGrid, MorphText, MorphCustom)
  , morphShapeTypeToString
  , morphShapeTypeFromString
  , allMorphShapeTypes
  , defaultMorphShapeType
  , MorphEasing(MEasingLinear, MEasingEaseIn, MEasingEaseOut, MEasingEaseInOut)
  , morphEasingToString
  , morphEasingFromString
  , allMorphEasings
  , defaultMorphEasing
  , ShapeEasing(SEasingLinear, SEasingEaseIn, SEasingEaseOut, SEasingEaseInOut, SEasingElastic, SEasingBounce)
  , shapeEasingToString
  , shapeEasingFromString
  , allShapeEasings
  , defaultShapeEasing
  , AttractorType(AttractorLorenz, AttractorRossler, AttractorAizawa, AttractorThomas, AttractorHalvorsen)
  , attractorTypeToString
  , attractorTypeFromString
  , allAttractorTypes
  , defaultAttractorType
  , attractorTypeStrings
  , DataMapping(MapSpeed, MapDirection, MapAmplitude, MapPhase, MapSize)
  , dataMappingToString
  , dataMappingFromString
  , allDataMappings
  , defaultDataMapping
  , ForceFalloff(FalloffLinear, FalloffQuadratic, FalloffNone)
  , forceFalloffToString
  , forceFalloffFromString
  , allForceFalloffs
  , defaultForceFalloff
  , InitialDistribution(DistRandom, DistGrid, DistEdge, DistCenter)
  , initialDistributionToString
  , initialDistributionFromString
  , allInitialDistributions
  , defaultInitialDistribution
  , ShapeType(ShapeCircle, ShapeGrid, ShapeText, ShapeHeart, ShapeStar, ShapeSpiral, ShapeRandom, ShapeCustom)
  , shapeTypeToString
  , shapeTypeFromString
  , allShapeTypes
  , defaultShapeType
  , lastShapeType
  , shapeTypeStrings
  , TrackPoint(TrackPoint)
  , mkTrackPoint
  , isValidTrackPoint
  , WanMoveMetadata(WanMoveMetadata)
  , mkWanMoveMetadata
  , WanMoveTrajectory(WanMoveTrajectory)
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
  ( TTMModel(TTMWan, TTMCogVideoX, TTMSVD)
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
  , TrajectoryPoint(TrajectoryPoint)
  , mkTrajectoryPoint
  , isValidTrajectoryPoint
  , trajectoryPointAtFrame
  , trajectoryFirstPoint
  , trajectoryLastPoint
  , TTMLayerExport(TTMLayerExport)
  , mkTTMLayerExport
  , isValidLayerExport
  , TTMModelConfig(TTMModelConfig)
  , mkTTMModelConfig
  , isValidModelConfig
  , defaultModelConfig
  , TTMMetadata(TTMMetadata)
  , mkTTMMetadata
  , isValidMetadata
  , metadataLayerCount
  , TTMExport(TTMExport)
  , mkTTMExport
  , isValidExport
  , mapTrajectoryPoints
  , translateTrajectory
  , scaleTrajectory
  , trajectoryLength
  , layerTrajectoryBounds
  ) as TTM

import Hydrogen.Schema.Motion.Diffusion.Camera
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
  , Position3D(Position3D)
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
  , CameraIntrinsics(CameraIntrinsics)
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
