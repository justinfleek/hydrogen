-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // diffusion // ttm
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Time-to-Move (TTM) export format types.
-- |
-- | TTM is a multi-layer motion mask system for video generation that uses
-- | trajectory data and motion masks to guide object movement in generated
-- | videos. This module provides types for defining TTM exports.
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Schemas.Exports.TTMSchema` from the
-- | Haskell backend, ensuring type-level compatibility for serialization.
-- |
-- | ## Model Support
-- |
-- | - Wan (Alibaba) - Primary target
-- | - CogVideoX (Tsinghua)
-- | - SVD (Stability AI)
-- |
-- | ## Constants
-- |
-- | - Max frames: 100000
-- | - Max dimension: 16384px
-- | - Max layers: 1000
-- | - Max tweak index: 100.0
-- | - Max inference steps: 1000

module Hydrogen.Schema.Motion.Diffusion.TTM
  ( -- * TTM Model
    TTMModel(TTMWan, TTMCogVideoX, TTMSVD)
  , ttmModelToString
  , ttmModelFromString
  , allTTMModels
  , defaultTTMModel
  , firstTTMModel
  , lastTTMModel
  
  -- * Constants
  , ttmMaxFrames
  , ttmMaxDimension
  , ttmMaxLayers
  , ttmMaxTweakIndex
  , ttmMaxInferenceSteps
  
  -- * Trajectory Point
  , TrajectoryPoint(TrajectoryPoint)
  , mkTrajectoryPoint
  , isValidTrajectoryPoint
  , trajectoryPointAtFrame
  , trajectoryFirstPoint
  , trajectoryLastPoint
  
  -- * Layer Export
  , TTMLayerExport(TTMLayerExport)
  , mkTTMLayerExport
  , isValidLayerExport
  
  -- * Model Configuration
  , TTMModelConfig(TTMModelConfig)
  , mkTTMModelConfig
  , isValidModelConfig
  , defaultModelConfig
  
  -- * Metadata
  , TTMMetadata(TTMMetadata)
  , mkTTMMetadata
  , isValidMetadata
  , metadataLayerCount
  
  -- * TTM Export
  , TTMExport(TTMExport)
  , mkTTMExport
  , isValidExport
  
  -- * Utilities
  , mapTrajectoryPoints
  , translateTrajectory
  , scaleTrajectory
  , trajectoryLength
  , layerTrajectoryBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Bounded
  , compare
  , (==)
  , (/=)
  , (<=)
  , (>=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (&&)
  , (<>)
  , ($)
  , not
  , otherwise
  , bottom
  , top
  , show
  , map
  , min
  , max
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (length, foldl, head, last, tail) as Array
import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // ttm // model
-- ═════════════════════════════════════════════════════════════════════════════

-- | TTM target model options.
-- |
-- | Different video generation models have different requirements for
-- | trajectory format and inference parameters.
data TTMModel
  = TTMWan        -- ^ Wan model (Alibaba) - primary target
  | TTMCogVideoX  -- ^ CogVideoX model (Tsinghua)
  | TTMSVD        -- ^ Stable Video Diffusion

derive instance eqTTMModel :: Eq TTMModel
derive instance ordTTMModel :: Ord TTMModel

instance boundedTTMModel :: Bounded TTMModel where
  bottom = TTMWan
  top = TTMSVD

instance showTTMModel :: Show TTMModel where
  show = ttmModelToString

-- | Convert TTM model to string identifier.
ttmModelToString :: TTMModel -> String
ttmModelToString TTMWan = "wan"
ttmModelToString TTMCogVideoX = "cogvideox"
ttmModelToString TTMSVD = "svd"

-- | Parse TTM model from string.
ttmModelFromString :: String -> Maybe TTMModel
ttmModelFromString "wan" = Just TTMWan
ttmModelFromString "cogvideox" = Just TTMCogVideoX
ttmModelFromString "svd" = Just TTMSVD
ttmModelFromString _ = Nothing

-- | All TTM models for enumeration.
allTTMModels :: Array TTMModel
allTTMModels =
  [ TTMWan
  , TTMCogVideoX
  , TTMSVD
  ]

-- | Default TTM model.
defaultTTMModel :: TTMModel
defaultTTMModel = bottom

-- | First TTM model in enumeration order.
firstTTMModel :: TTMModel
firstTTMModel = bottom

-- | Last TTM model in enumeration order.
lastTTMModel :: TTMModel
lastTTMModel = top

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum number of frames per export.
ttmMaxFrames :: Int
ttmMaxFrames = 100000

-- | Maximum dimension (width or height) in pixels.
ttmMaxDimension :: Int
ttmMaxDimension = 16384

-- | Maximum number of layers per export.
ttmMaxLayers :: Int
ttmMaxLayers = 1000

-- | Maximum tweak index value.
ttmMaxTweakIndex :: Number
ttmMaxTweakIndex = 100.0

-- | Maximum inference steps.
ttmMaxInferenceSteps :: Int
ttmMaxInferenceSteps = 1000

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // trajectory // point
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single trajectory point with frame number and 2D coordinates.
-- |
-- | Coordinates are in pixel space within the frame dimensions.
newtype TrajectoryPoint = TrajectoryPoint
  { frame :: Int
  , x :: Number
  , y :: Number
  }

derive instance eqTrajectoryPoint :: Eq TrajectoryPoint

instance ordTrajectoryPoint :: Ord TrajectoryPoint where
  compare (TrajectoryPoint p1) (TrajectoryPoint p2) =
    compare p1.frame p2.frame

instance showTrajectoryPoint :: Show TrajectoryPoint where
  show (TrajectoryPoint p) = 
    "Point(f" <> show p.frame <> ": " <> show p.x <> ", " <> show p.y <> ")"

-- | Smart constructor for trajectory point with validation.
mkTrajectoryPoint :: Int -> Number -> Number -> Int -> Int -> Maybe TrajectoryPoint
mkTrajectoryPoint frame x y width height
  | frame < 0 = Nothing
  | frame > ttmMaxFrames = Nothing
  | x < 0.0 = Nothing
  | y < 0.0 = Nothing
  | x > Int.toNumber width = Nothing
  | y > Int.toNumber height = Nothing
  | otherwise = Just $ TrajectoryPoint { frame, x, y }

-- | Check if a trajectory point is valid.
isValidTrajectoryPoint :: Int -> Int -> TrajectoryPoint -> Boolean
isValidTrajectoryPoint width height (TrajectoryPoint p) =
  p.frame >= 0 && p.frame <= ttmMaxFrames &&
  p.x >= 0.0 && p.x <= Int.toNumber width &&
  p.y >= 0.0 && p.y <= Int.toNumber height

-- | Get the first point in a trajectory.
trajectoryFirstPoint :: Array TrajectoryPoint -> Maybe TrajectoryPoint
trajectoryFirstPoint = Array.head

-- | Get the last point in a trajectory.
trajectoryLastPoint :: Array TrajectoryPoint -> Maybe TrajectoryPoint
trajectoryLastPoint = Array.last

-- | Get trajectory point at a specific frame (linear interpolation).
-- |
-- | Returns Nothing if frame is outside trajectory range.
trajectoryPointAtFrame :: Array TrajectoryPoint -> Int -> Maybe TrajectoryPoint
trajectoryPointAtFrame points targetFrame =
  case findBracket points targetFrame of
    Nothing -> Nothing
    Just { before, after } ->
      if before.frame == targetFrame
        then Just (TrajectoryPoint before)
        else if after.frame == targetFrame
          then Just (TrajectoryPoint after)
          else Just $ interpolate before after targetFrame
  where
    findBracket :: Array TrajectoryPoint -> Int -> Maybe { before :: { frame :: Int, x :: Number, y :: Number }, after :: { frame :: Int, x :: Number, y :: Number } }
    findBracket pts f = findBracketImpl pts f Nothing
    
    findBracketImpl :: Array TrajectoryPoint -> Int -> Maybe { before :: { frame :: Int, x :: Number, y :: Number }, after :: { frame :: Int, x :: Number, y :: Number } } -> Maybe { before :: { frame :: Int, x :: Number, y :: Number }, after :: { frame :: Int, x :: Number, y :: Number } }
    findBracketImpl pts f acc = 
      case Array.head pts of
        Nothing -> acc
        Just (TrajectoryPoint p) ->
          if p.frame <= f
            then 
              let newAcc = case acc of
                    Nothing -> Just { before: p, after: p }
                    Just a -> Just { before: p, after: a.after }
                  remainingPts = case Array.tail pts of
                    Nothing -> []
                    Just rest -> rest
              in findBracketImpl remainingPts f newAcc
            else
              case acc of
                Nothing -> Nothing
                Just a -> Just { before: a.before, after: p }
    
    interpolate :: { frame :: Int, x :: Number, y :: Number } -> { frame :: Int, x :: Number, y :: Number } -> Int -> TrajectoryPoint
    interpolate p1 p2 f =
      let t = Int.toNumber (f - p1.frame) / Int.toNumber (p2.frame - p1.frame)
          x = p1.x + t * (p2.x - p1.x)
          y = p1.y + t * (p2.y - p1.y)
      in TrajectoryPoint { frame: f, x, y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layer // export
-- ═════════════════════════════════════════════════════════════════════════════

-- | TTM layer export data.
-- |
-- | Each layer has an ID, name, motion mask (base64 PNG), trajectory,
-- | and per-frame visibility flags.
newtype TTMLayerExport = TTMLayerExport
  { layerId :: String
  , layerName :: String
  , motionMask :: String          -- ^ Base64-encoded PNG
  , trajectory :: Array TrajectoryPoint
  , visibility :: Array Boolean   -- ^ Per-frame visibility
  }

derive instance eqTTMLayerExport :: Eq TTMLayerExport

instance showTTMLayerExport :: Show TTMLayerExport where
  show (TTMLayerExport l) = 
    "TTMLayer(" <> l.layerName <> ", " <> 
    show (Array.length l.trajectory) <> " points)"

-- | Smart constructor for layer export with validation.
mkTTMLayerExport 
  :: String 
  -> String 
  -> String 
  -> Array TrajectoryPoint 
  -> Array Boolean 
  -> Maybe TTMLayerExport
mkTTMLayerExport layerId layerName motionMask trajectory visibility
  | layerId == "" = Nothing
  | layerName == "" = Nothing
  | motionMask == "" = Nothing
  | Array.length trajectory /= Array.length visibility = Nothing
  | Array.length trajectory > ttmMaxFrames = Nothing
  | otherwise = Just $ TTMLayerExport 
      { layerId, layerName, motionMask, trajectory, visibility }

-- | Validate a layer export.
isValidLayerExport :: TTMLayerExport -> Boolean
isValidLayerExport (TTMLayerExport l) =
  l.layerId /= "" &&
  l.layerName /= "" &&
  l.motionMask /= "" &&
  Array.length l.trajectory == Array.length l.visibility &&
  Array.length l.trajectory <= ttmMaxFrames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // model // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | TTM model inference configuration.
-- |
-- | Controls how the model processes the motion guidance.
newtype TTMModelConfig = TTMModelConfig
  { model :: TTMModel
  , tweakIndex :: Number        -- ^ Motion strength (0-100)
  , tstrongIndex :: Number      -- ^ Temporal strength (0-100)
  , inferenceSteps :: Int       -- ^ Number of diffusion steps
  }

derive instance eqTTMModelConfig :: Eq TTMModelConfig

instance showTTMModelConfig :: Show TTMModelConfig where
  show (TTMModelConfig c) =
    "TTMConfig(" <> show c.model <> ", tweak=" <> show c.tweakIndex <> 
    ", steps=" <> show c.inferenceSteps <> ")"

-- | Smart constructor for model config with validation.
mkTTMModelConfig 
  :: TTMModel 
  -> Number 
  -> Number 
  -> Int 
  -> Maybe TTMModelConfig
mkTTMModelConfig model tweakIndex tstrongIndex inferenceSteps
  | tweakIndex < 0.0 = Nothing
  | tweakIndex > ttmMaxTweakIndex = Nothing
  | tstrongIndex < 0.0 = Nothing
  | tstrongIndex > ttmMaxTweakIndex = Nothing
  | inferenceSteps <= 0 = Nothing
  | inferenceSteps > ttmMaxInferenceSteps = Nothing
  | otherwise = Just $ TTMModelConfig 
      { model, tweakIndex, tstrongIndex, inferenceSteps }

-- | Validate model configuration.
isValidModelConfig :: TTMModelConfig -> Boolean
isValidModelConfig (TTMModelConfig c) =
  c.tweakIndex >= 0.0 && c.tweakIndex <= ttmMaxTweakIndex &&
  c.tstrongIndex >= 0.0 && c.tstrongIndex <= ttmMaxTweakIndex &&
  c.inferenceSteps > 0 && c.inferenceSteps <= ttmMaxInferenceSteps

-- | Default model configuration.
-- |
-- | Wan model with moderate motion strength and 20 inference steps.
defaultModelConfig :: TTMModelConfig
defaultModelConfig = TTMModelConfig
  { model: TTMWan
  , tweakIndex: 50.0
  , tstrongIndex: 50.0
  , inferenceSteps: 20
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | TTM export metadata.
-- |
-- | Contains dimensions and layer/frame counts for the export.
newtype TTMMetadata = TTMMetadata
  { layerCount :: Int
  , frameCount :: Int
  , width :: Int
  , height :: Int
  }

derive instance eqTTMMetadata :: Eq TTMMetadata

instance showTTMMetadata :: Show TTMMetadata where
  show (TTMMetadata m) =
    "TTMMetadata(" <> show m.layerCount <> " layers, " <>
    show m.frameCount <> " frames, " <>
    show m.width <> "x" <> show m.height <> ")"

-- | Smart constructor for metadata with validation.
mkTTMMetadata :: Int -> Int -> Int -> Int -> Maybe TTMMetadata
mkTTMMetadata layerCount frameCount width height
  | layerCount <= 0 = Nothing
  | layerCount > ttmMaxLayers = Nothing
  | frameCount <= 0 = Nothing
  | frameCount > ttmMaxFrames = Nothing
  | width <= 0 = Nothing
  | width > ttmMaxDimension = Nothing
  | height <= 0 = Nothing
  | height > ttmMaxDimension = Nothing
  | otherwise = Just $ TTMMetadata { layerCount, frameCount, width, height }

-- | Validate metadata.
isValidMetadata :: TTMMetadata -> Boolean
isValidMetadata (TTMMetadata m) =
  m.layerCount > 0 && m.layerCount <= ttmMaxLayers &&
  m.frameCount > 0 && m.frameCount <= ttmMaxFrames &&
  m.width > 0 && m.width <= ttmMaxDimension &&
  m.height > 0 && m.height <= ttmMaxDimension

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // ttm // export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete TTM export structure.
-- |
-- | Contains reference image, layers, combined motion mask, and configuration.
newtype TTMExport = TTMExport
  { referenceImage :: String          -- ^ Base64 or file path
  , lastFrame :: Maybe String         -- ^ Optional last frame for temporal context
  , layers :: Array TTMLayerExport
  , combinedMotionMask :: String      -- ^ Combined mask from all layers
  , modelConfig :: TTMModelConfig
  , metadata :: TTMMetadata
  }

derive instance eqTTMExport :: Eq TTMExport

instance showTTMExport :: Show TTMExport where
  show (TTMExport e) =
    "TTMExport(" <> show e.metadata <> ", " <> show e.modelConfig <> ")"

-- | Extract layer count from metadata.
metadataLayerCount :: TTMMetadata -> Int
metadataLayerCount (TTMMetadata m) = m.layerCount

-- | Smart constructor for TTM export with validation.
mkTTMExport 
  :: String 
  -> Maybe String 
  -> Array TTMLayerExport 
  -> String 
  -> TTMModelConfig 
  -> TTMMetadata 
  -> Maybe TTMExport
mkTTMExport referenceImage lastFrame layers combinedMotionMask modelConfig metadata
  | referenceImage == "" = Nothing
  | combinedMotionMask == "" = Nothing
  | not (isValidModelConfig modelConfig) = Nothing
  | not (isValidMetadata metadata) = Nothing
  | Array.length layers /= metadataLayerCount metadata = Nothing
  | otherwise = Just $ TTMExport 
      { referenceImage, lastFrame, layers, combinedMotionMask, modelConfig, metadata }

-- | Validate complete TTM export.
isValidExport :: TTMExport -> Boolean
isValidExport (TTMExport e) =
  e.referenceImage /= "" &&
  e.combinedMotionMask /= "" &&
  isValidModelConfig e.modelConfig &&
  isValidMetadata e.metadata &&
  Array.length e.layers == metadataLayerCount e.metadata &&
  allLayersValid e.layers
  where
    allLayersValid :: Array TTMLayerExport -> Boolean
    allLayersValid exportLayers = Array.foldl (\acc l -> acc && isValidLayerExport l) true exportLayers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over all trajectory points in a layer.
mapTrajectoryPoints 
  :: (TrajectoryPoint -> TrajectoryPoint) 
  -> TTMLayerExport 
  -> TTMLayerExport
mapTrajectoryPoints f (TTMLayerExport l) =
  TTMLayerExport l { trajectory = map f l.trajectory }

-- | Translate all trajectory points by an offset.
translateTrajectory :: Number -> Number -> TTMLayerExport -> TTMLayerExport
translateTrajectory dx dy = mapTrajectoryPoints translate
  where
    translate (TrajectoryPoint p) = 
      TrajectoryPoint { frame: p.frame, x: p.x + dx, y: p.y + dy }

-- | Scale all trajectory points by a factor.
scaleTrajectory :: Number -> Number -> TTMLayerExport -> TTMLayerExport
scaleTrajectory sx sy = mapTrajectoryPoints scale
  where
    scale (TrajectoryPoint p) = 
      TrajectoryPoint { frame: p.frame, x: p.x * sx, y: p.y * sy }

-- | Calculate the total path length of a trajectory.
trajectoryLength :: Array TrajectoryPoint -> Number
trajectoryLength points = 
  case Array.head points of
    Nothing -> 0.0
    Just first -> 
      let result = Array.foldl accum { prev: first, total: 0.0 } points
      in result.total
  where
    accum :: { prev :: TrajectoryPoint, total :: Number } -> TrajectoryPoint -> { prev :: TrajectoryPoint, total :: Number }
    accum acc curr = { prev: curr, total: acc.total + distance acc.prev curr }
    
    distance :: TrajectoryPoint -> TrajectoryPoint -> Number
    distance (TrajectoryPoint p1) (TrajectoryPoint p2) =
      let dx = p1.x - p2.x
          dy = p1.y - p2.y
      in sqrtApprox (dx * dx + dy * dy)
    
    -- Approximation using Newton-Raphson (3 iterations)
    sqrtApprox :: Number -> Number
    sqrtApprox n
      | n <= 0.0 = 0.0
      | otherwise = 
          let x0 = n / 2.0
              x1 = (x0 + n / x0) / 2.0
              x2 = (x1 + n / x1) / 2.0
              x3 = (x2 + n / x2) / 2.0
          in x3

-- | Get the bounding box of a layer's trajectory.
-- |
-- | Returns (minX, minY, maxX, maxY) or Nothing for empty trajectory.
layerTrajectoryBounds :: TTMLayerExport -> Maybe { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
layerTrajectoryBounds (TTMLayerExport l) =
  case Array.head l.trajectory of
    Nothing -> Nothing
    Just (TrajectoryPoint first) ->
      Just $ Array.foldl updateBounds 
        { minX: first.x, minY: first.y, maxX: first.x, maxY: first.y }
        l.trajectory
  where
    updateBounds bounds (TrajectoryPoint p) =
      { minX: min bounds.minX p.x
      , minY: min bounds.minY p.y
      , maxX: max bounds.maxX p.x
      , maxY: max bounds.maxY p.y
      }
