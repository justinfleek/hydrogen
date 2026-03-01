-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // motion // layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer types and base layer data for motion graphics.
-- |
-- | A Layer is the fundamental unit of content in a Composition. Each layer
-- | has a specific type (Image, Video, Text, Shape, etc.) that determines
-- | its rendering behavior and animatable properties.
-- |
-- | ## Layer Types
-- |
-- | Supports 26+ layer types matching After Effects and LATTICE:
-- | - Media layers: Image, Video, Audio, Solid
-- | - Content layers: Text, Shape, Null
-- | - 3D layers: Camera, Light
-- | - Effects: Adjustment, Effect
-- | - Composition: PreComp, NestedComp
-- | - Specialized: Particle, Depth, Normal, Pose, Model, PointCloud
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Project` LayerType and LayerBase from the
-- | Haskell backend, ensuring type-level compatibility for serialization.

module Hydrogen.Schema.Motion.Layer
  ( -- * Layer Type
    LayerType(..)
  , layerTypeToString
  , layerTypeFromString
  , isLayerType3D
  , isLayerTypeMedia
  , isLayerTypeContent
  , isLayerTypeVector
  , isLayerTypeAudio
  , isLayerTypeData
  , isLayerTypeAnnotation
  , isLayerTypeTracking
  , isLayerTypeUtility
  , isLayerTypeColorGrading
  
  -- * Layer Identifier
  , LayerId(..)
  , mkLayerId
  
  -- * Layer Base
  , LayerBase(..)
  , defaultLayerBase
  , mkLayerBase
  
  -- * Layer Visibility
  , LayerVisibility(..)
  , layerVisibilityToString
  , layerVisibilityFromString
  
  -- * Quality Setting
  , SamplingQuality(..)
  , samplingQualityToString
  , samplingQualityFromString
  
  -- * Accessors
  , layerId
  , layerName
  , layerType
  , layerVisible
  , layerLocked
  , layerSolo
  , layerShy
  , layerEnabled
  , layerSelected
  , layerCollapsed
  , layerGuideLayer
  , layerIs3D
  , layerBlendMode
  , layerOpacity
  , layerStartFrame
  , layerEndFrame
  , layerInPoint
  , layerOutPoint
  , layerStretch
  , layerParentId
  , layerTrackMatteMode
  , layerTrackMatteLayerId
  , layerMotionBlur
  , layerQualitySetting
  , layerSamplingQuality
  , layerPreserveTransparency
  , layerFrameBlending
  , layerTimeRemapEnabled
  , layerCollapseTransformations
  , layerAutoOrient
  
  -- * Predicates
  , isLayerVisible
  , isLayerLocked
  , isLayerSolo
  , isLayerGuide
  , isLayerTimeRemapped
  , isLayerHidden
  , isLayerEditable
  , isLayerActive
  , isLayer3D
  , hasParent
  , hasTrackMatte
  
  -- * Layer Ordering
  , compareByStartFrame
  , compareByEndFrame
  , compareByName
  , earlierLayer
  , laterLayer
  , minStartFrame
  , maxEndFrame
  
  -- * Frame Arithmetic
  , layerDuration
  , layerTrimmedDuration
  , layerEffectiveDuration
  , isFrameInLayer
  , frameOffsetFromStart
  , layerDistance
  , reverseLayerTime
  
  -- * Modifiers
  , setOpacity
  , setVisible
  , setLocked
  , setSolo
  , setShy
  , setEnabled
  , set3D
  , setBlendMode
  , setName
  , setParent
  , setStartFrame
  , setEndFrame
  , setInPoint
  , setOutPoint
  , setStretch
  , setMotionBlur
  , setTrackMatteMode
  , setTrackMatteLayer
  , setAutoOrient
  , setCollapseTransformations
  , setTimeRemapEnabled
  
  -- * Fluent API
  , identityLayer
  , constLayer
  , flipLayerFn
  , applyTo
  
  -- * Pipeline Composition
  , composeTransforms
  , pipeTransforms
  
  -- * Layer Helpers
  , mapLayer
  , pureLayer
  , bindLayer
  , applyLayerFn
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , Ordering(LT, GT, EQ)
  , ($)
  , (#)
  , (<<<)
  , (>>>)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  , bind
  , identity
  , const
  , flip
  , apply
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Ord (abs)
import Data.String (length) as String
import Data.String.CodeUnits (toCharArray) as String
import Data.Array (index, length) as Array
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))
import Hydrogen.Schema.Motion.Composition 
  ( BlendMode(..)
  , TrackMatteMode(..)
  )
import Hydrogen.Schema.Motion.Camera3D.Enums (AutoOrientMode(..))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // layer // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a layer.
-- |
-- | Uses NonEmptyString semantics — must have at least one character.
newtype LayerId = LayerId String

derive instance eqLayerId :: Eq LayerId
derive instance ordLayerId :: Ord LayerId

instance showLayerId :: Show LayerId where
  show (LayerId id) = "Layer:" <> id

-- | Smart constructor for LayerId.
-- |
-- | Returns Nothing if the string is empty.
mkLayerId :: String -> Maybe LayerId
mkLayerId "" = Nothing
mkLayerId s = Just (LayerId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of layer content.
-- |
-- | Defines the rendering behavior and available animatable properties.
-- | Each variant corresponds to a specific content type in After Effects.
data LayerType
  -- Media layers
  = LTImage            -- Static image (PNG, JPG, SVG, etc.)
  | LTVideo            -- Video clip with duration
  | LTSolid            -- Solid color fill layer
  | LTAudio            -- Audio clip
  
  -- Content layers
  | LTText             -- Text/typography layer
  | LTShape            -- Vector shape layer
  | LTNull             -- Null object (no render, anchor point only)
  
  -- 3D layers
  | LTCamera           -- Camera for 3D composition
  | LTLight            -- Light source (point, spot, directional)
  
  -- Effect layers
  | LTAdjustment       -- Adjustment layer (effects below)
  | LTEffect           -- Effect layer
  
  -- Composition layers
  | LTPreComp         -- Pre-composition (collapsed nested timeline)
  | LTGroup           -- Group/layer folder
  | LTNestedComp      -- Nested composition reference
  
  -- Specialized layers
  | LTParticle        -- Particle system
  | LTDepth           -- Depth map layer
  | LTNormal          -- Normal map layer
  | LTGenerated       -- Procedurally generated content
  | LTMatte           -- Matte/garbage mask layer
  | LTControl         -- Control layer (for expressions)
  | LTSpline          -- Spline/path animation
  | LTPath            -- Path definition layer
  | LTPose            -- Pose/animation reference
  | LTModel           -- 3D model layer
  | LTPointCloud      -- Point cloud data
  | LTDepthflow       -- Depth flow animation
  
  -- Vector & Graphics layers
  | LTSVG             -- SVG vector graphics
  | LTVectorGraphic   -- Generic vector graphic (AI, EPS, PDF)
  | LTLottie          -- Lottie animation (JSON)
  | LTRive            -- Rive animation
  
  -- 3D & Spatial layers
  | LTMesh            -- 3D mesh geometry
  | LTEnvironment     -- Environment map (HDRI, cubemap)
  | LTVolume          -- Volumetric data (VDB, density fields)
  | LTSkeleton        -- Skeletal animation rig
  
  -- Color & Grading layers
  | LTHDR             -- HDR image layer
  | LTLUT             -- LUT (lookup table) layer
  | LTGradient        -- Gradient ramp layer
  
  -- Audio & Waveform layers
  | LTWaveform        -- Audio waveform visualization
  | LTSpectrogram     -- Audio spectrogram visualization
  | LTMIDI            -- MIDI data layer
  
  -- Data & Structured layers
  | LTCSV             -- CSV data layer
  | LTJSON            -- JSON data layer
  | LTGeoJSON         -- GeoJSON geographic data
  | LTData            -- Generic structured data
  
  -- Annotation & Metadata layers
  | LTMarker          -- Timeline markers
  | LTSubtitle        -- Subtitles/captions (SRT, VTT)
  | LTAnnotation      -- Visual annotations
  | LTComment         -- Comment/note layer
  
  -- Tracking & Motion layers  
  | LTTracker         -- Motion tracking data
  | LTMocha           -- Mocha planar tracking
  | LTStabilizer      -- Stabilization reference
  
  -- Compositing utility layers
  | LTReference       -- Reference image (non-rendering)
  | LTGrid            -- Grid overlay
  | LTGuide           -- Guide lines
  | LTMask            -- Mask layer (separate from matte)
  | LTRoto            -- Rotoscoping layer

derive instance eqLayerType :: Eq LayerType
derive instance ordLayerType :: Ord LayerType

instance showLayerType :: Show LayerType where
  show = layerTypeToString

-- | Convert layer type to string representation.
layerTypeToString :: LayerType -> String
layerTypeToString LTImage = "image"
layerTypeToString LTVideo = "video"
layerTypeToString LTSolid = "solid"
layerTypeToString LTAudio = "audio"
layerTypeToString LTText = "text"
layerTypeToString LTShape = "shape"
layerTypeToString LTNull = "null"
layerTypeToString LTCamera = "camera"
layerTypeToString LTLight = "light"
layerTypeToString LTAdjustment = "adjustment"
layerTypeToString LTEffect = "effect"
layerTypeToString LTPreComp = "precomp"
layerTypeToString LTGroup = "group"
layerTypeToString LTNestedComp = "nestedcomp"
layerTypeToString LTParticle = "particle"
layerTypeToString LTDepth = "depth"
layerTypeToString LTNormal = "normal"
layerTypeToString LTGenerated = "generated"
layerTypeToString LTMatte = "matte"
layerTypeToString LTControl = "control"
layerTypeToString LTSpline = "spline"
layerTypeToString LTPath = "path"
layerTypeToString LTPose = "pose"
layerTypeToString LTModel = "model"
layerTypeToString LTPointCloud = "pointcloud"
layerTypeToString LTDepthflow = "depthflow"
-- Vector & Graphics
layerTypeToString LTSVG = "svg"
layerTypeToString LTVectorGraphic = "vectorgraphic"
layerTypeToString LTLottie = "lottie"
layerTypeToString LTRive = "rive"
-- 3D & Spatial
layerTypeToString LTMesh = "mesh"
layerTypeToString LTEnvironment = "environment"
layerTypeToString LTVolume = "volume"
layerTypeToString LTSkeleton = "skeleton"
-- Color & Grading
layerTypeToString LTHDR = "hdr"
layerTypeToString LTLUT = "lut"
layerTypeToString LTGradient = "gradient"
-- Audio & Waveform
layerTypeToString LTWaveform = "waveform"
layerTypeToString LTSpectrogram = "spectrogram"
layerTypeToString LTMIDI = "midi"
-- Data & Structured
layerTypeToString LTCSV = "csv"
layerTypeToString LTJSON = "json"
layerTypeToString LTGeoJSON = "geojson"
layerTypeToString LTData = "data"
-- Annotation & Metadata
layerTypeToString LTMarker = "marker"
layerTypeToString LTSubtitle = "subtitle"
layerTypeToString LTAnnotation = "annotation"
layerTypeToString LTComment = "comment"
-- Tracking & Motion
layerTypeToString LTTracker = "tracker"
layerTypeToString LTMocha = "mocha"
layerTypeToString LTStabilizer = "stabilizer"
-- Compositing utility
layerTypeToString LTReference = "reference"
layerTypeToString LTGrid = "grid"
layerTypeToString LTGuide = "guide"
layerTypeToString LTMask = "mask"
layerTypeToString LTRoto = "roto"

-- | Parse layer type from string.
layerTypeFromString :: String -> Maybe LayerType
layerTypeFromString "image" = Just LTImage
layerTypeFromString "video" = Just LTVideo
layerTypeFromString "solid" = Just LTSolid
layerTypeFromString "audio" = Just LTAudio
layerTypeFromString "text" = Just LTText
layerTypeFromString "shape" = Just LTShape
layerTypeFromString "null" = Just LTNull
layerTypeFromString "camera" = Just LTCamera
layerTypeFromString "light" = Just LTLight
layerTypeFromString "adjustment" = Just LTAdjustment
layerTypeFromString "effect" = Just LTEffect
layerTypeFromString "precomp" = Just LTPreComp
layerTypeFromString "group" = Just LTGroup
layerTypeFromString "nestedcomp" = Just LTNestedComp
layerTypeFromString "particle" = Just LTParticle
layerTypeFromString "depth" = Just LTDepth
layerTypeFromString "normal" = Just LTNormal
layerTypeFromString "generated" = Just LTGenerated
layerTypeFromString "matte" = Just LTMatte
layerTypeFromString "control" = Just LTControl
layerTypeFromString "spline" = Just LTSpline
layerTypeFromString "path" = Just LTPath
layerTypeFromString "pose" = Just LTPose
layerTypeFromString "model" = Just LTModel
layerTypeFromString "pointcloud" = Just LTPointCloud
layerTypeFromString "depthflow" = Just LTDepthflow
-- Vector & Graphics
layerTypeFromString "svg" = Just LTSVG
layerTypeFromString "vectorgraphic" = Just LTVectorGraphic
layerTypeFromString "lottie" = Just LTLottie
layerTypeFromString "rive" = Just LTRive
-- 3D & Spatial
layerTypeFromString "mesh" = Just LTMesh
layerTypeFromString "environment" = Just LTEnvironment
layerTypeFromString "volume" = Just LTVolume
layerTypeFromString "skeleton" = Just LTSkeleton
-- Color & Grading
layerTypeFromString "hdr" = Just LTHDR
layerTypeFromString "lut" = Just LTLUT
layerTypeFromString "gradient" = Just LTGradient
-- Audio & Waveform
layerTypeFromString "waveform" = Just LTWaveform
layerTypeFromString "spectrogram" = Just LTSpectrogram
layerTypeFromString "midi" = Just LTMIDI
-- Data & Structured
layerTypeFromString "csv" = Just LTCSV
layerTypeFromString "json" = Just LTJSON
layerTypeFromString "geojson" = Just LTGeoJSON
layerTypeFromString "data" = Just LTData
-- Annotation & Metadata
layerTypeFromString "marker" = Just LTMarker
layerTypeFromString "subtitle" = Just LTSubtitle
layerTypeFromString "annotation" = Just LTAnnotation
layerTypeFromString "comment" = Just LTComment
-- Tracking & Motion
layerTypeFromString "tracker" = Just LTTracker
layerTypeFromString "mocha" = Just LTMocha
layerTypeFromString "stabilizer" = Just LTStabilizer
-- Compositing utility
layerTypeFromString "reference" = Just LTReference
layerTypeFromString "grid" = Just LTGrid
layerTypeFromString "guide" = Just LTGuide
layerTypeFromString "mask" = Just LTMask
layerTypeFromString "roto" = Just LTRoto
layerTypeFromString _ = Nothing

-- | Check if layer type requires 3D rendering.
isLayerType3D :: LayerType -> Boolean
isLayerType3D LTCamera = true
isLayerType3D LTLight = true
isLayerType3D LTModel = true
isLayerType3D LTPointCloud = true
isLayerType3D LTDepthflow = true
isLayerType3D LTMesh = true
isLayerType3D LTEnvironment = true
isLayerType3D LTVolume = true
isLayerType3D LTSkeleton = true
isLayerType3D _ = false

-- | Check if layer type is media (image/video/audio).
isLayerTypeMedia :: LayerType -> Boolean
isLayerTypeMedia LTImage = true
isLayerTypeMedia LTVideo = true
isLayerTypeMedia LTAudio = true
isLayerTypeMedia LTSolid = true
isLayerTypeMedia _ = false

-- | Check if layer type is content (text/shape).
isLayerTypeContent :: LayerType -> Boolean
isLayerTypeContent LTText = true
isLayerTypeContent LTShape = true
isLayerTypeContent LTNull = true
isLayerTypeContent _ = false

-- | Check if layer type is vector graphics.
isLayerTypeVector :: LayerType -> Boolean
isLayerTypeVector LTShape = true
isLayerTypeVector LTSVG = true
isLayerTypeVector LTVectorGraphic = true
isLayerTypeVector LTLottie = true
isLayerTypeVector LTRive = true
isLayerTypeVector LTPath = true
isLayerTypeVector LTSpline = true
isLayerTypeVector _ = false

-- | Check if layer type is audio-related.
isLayerTypeAudio :: LayerType -> Boolean
isLayerTypeAudio LTAudio = true
isLayerTypeAudio LTWaveform = true
isLayerTypeAudio LTSpectrogram = true
isLayerTypeAudio LTMIDI = true
isLayerTypeAudio _ = false

-- | Check if layer type is data/structured content.
isLayerTypeData :: LayerType -> Boolean
isLayerTypeData LTCSV = true
isLayerTypeData LTJSON = true
isLayerTypeData LTGeoJSON = true
isLayerTypeData LTData = true
isLayerTypeData _ = false

-- | Check if layer type is annotation/metadata.
isLayerTypeAnnotation :: LayerType -> Boolean
isLayerTypeAnnotation LTMarker = true
isLayerTypeAnnotation LTSubtitle = true
isLayerTypeAnnotation LTAnnotation = true
isLayerTypeAnnotation LTComment = true
isLayerTypeAnnotation _ = false

-- | Check if layer type is tracking/motion data.
isLayerTypeTracking :: LayerType -> Boolean
isLayerTypeTracking LTTracker = true
isLayerTypeTracking LTMocha = true
isLayerTypeTracking LTStabilizer = true
isLayerTypeTracking LTPose = true
isLayerTypeTracking _ = false

-- | Check if layer type is compositing utility.
isLayerTypeUtility :: LayerType -> Boolean
isLayerTypeUtility LTReference = true
isLayerTypeUtility LTGrid = true
isLayerTypeUtility LTGuide = true
isLayerTypeUtility LTMask = true
isLayerTypeUtility LTRoto = true
isLayerTypeUtility LTMatte = true
isLayerTypeUtility LTNull = true
isLayerTypeUtility _ = false

-- | Check if layer type is color/grading related.
isLayerTypeColorGrading :: LayerType -> Boolean
isLayerTypeColorGrading LTHDR = true
isLayerTypeColorGrading LTLUT = true
isLayerTypeColorGrading LTGradient = true
isLayerTypeColorGrading LTAdjustment = true
isLayerTypeColorGrading _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // layer // visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer visibility state.
-- |
-- | Combines visible, locked, solo, and shy flags into a single state.
data LayerVisibility = LayerVisibility
  { visible :: Boolean    -- Layer is rendered
  , locked :: Boolean     -- Layer cannot be edited
  , solo :: Boolean      -- Only solo layers render (when any solo active)
  , shy :: Boolean       -- Layer hidden in UI (not timeline)
  }

derive instance eqLayerVisibility :: Eq LayerVisibility

instance showLayerVisibility :: Show LayerVisibility where
  show (LayerVisibility v) = 
    "Visibility(" <> 
    (if v.visible then "V" else "-") <>
    (if v.locked then "L" else "-") <>
    (if v.solo then "S" else "-") <>
    (if v.shy then "H" else "-") <>
    ")"
    
-- | Convert visibility state to string (for serialization).
layerVisibilityToString :: LayerVisibility -> String
layerVisibilityToString (LayerVisibility v) =
  (if v.visible then "1" else "0") <>
  (if v.locked then "1" else "0") <>
  (if v.solo then "1" else "0") <>
  (if v.shy then "1" else "0")

-- | Parse visibility state from 4-character string.
layerVisibilityFromString :: String -> Maybe LayerVisibility
layerVisibilityFromString s
  | String.length s /= 4 = Nothing
  | otherwise = Just $ LayerVisibility
      { visible: fromMaybe '0' (safeCharAt 0 s) == '1'
      , locked: fromMaybe '0' (safeCharAt 1 s) == '1'
      , solo: fromMaybe '0' (safeCharAt 2 s) == '1'
      , shy: fromMaybe '0' (safeCharAt 3 s) == '1'
      }

-- | Safe character index for string - returns Nothing if out of bounds.
safeCharAt :: Int -> String -> Maybe Char
safeCharAt i s = 
  let
    chars :: Array Char
    chars = String.toCharArray s
    len = Array.length chars
  in
    if i < 0 || i >= len then Nothing else Array.index chars i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // sampling // quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sampling quality for raster effects and motion blur.
data SamplingQuality
  = SQDraft          -- Low quality, fast rendering
  | SQStandard       -- Standard quality
  | SQHigh           -- High quality
  | SQBest           -- Best quality, slow rendering

derive instance eqSamplingQuality :: Eq SamplingQuality
derive instance ordSamplingQuality :: Ord SamplingQuality

instance showSamplingQuality :: Show SamplingQuality where
  show = samplingQualityToString

-- | Convert sampling quality to string.
samplingQualityToString :: SamplingQuality -> String
samplingQualityToString SQDraft = "draft"
samplingQualityToString SQStandard = "standard"
samplingQualityToString SQHigh = "high"
samplingQualityToString SQBest = "best"

-- | Parse sampling quality from string.
samplingQualityFromString :: String -> Maybe SamplingQuality
samplingQualityFromString "draft" = Just SQDraft
samplingQualityFromString "standard" = Just SQStandard
samplingQualityFromString "high" = Just SQHigh
samplingQualityFromString "best" = Just SQBest
samplingQualityFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // base
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base layer properties common to all layer types.
-- |
-- | This record contains the animatable and non-animatable properties
-- | that every layer has, regardless of its type.
-- |
-- | ## Invariants
-- |
-- | - startFrame <= endFrame (layer has non-negative duration)
-- | - inPoint >= 0
-- | - outPoint >= inPoint
-- | - opacity is 0-100 (enforced by Percentage type)
-- | - stretch > 0 (time stretching factor)
newtype LayerBase = LayerBase
  { id :: LayerId
  , name :: String
  , layerType :: LayerType
  , visible :: Boolean
  , locked :: Boolean
  , solo :: Boolean
  , shy :: Boolean
  , enabled :: Boolean
  , selected :: Boolean
  , collapsed :: Boolean
  , guideLayer :: Boolean
  , is3D :: Boolean
  , blendMode :: BlendMode
  , opacity :: Number         -- 0-100
  , startFrame :: Frames      -- Layer start in composition
  , endFrame :: Frames        -- Layer end in composition
  , inPoint :: Frames         -- Trim in point
  , outPoint :: Frames        -- Trim out point
  , stretch :: Number         -- Time stretch factor (1.0 = normal)
  , parentId :: Maybe LayerId
  , trackMatteMode :: TrackMatteMode
  , trackMatteLayerId :: Maybe LayerId
  , motionBlur :: Boolean
  , qualitySetting :: Maybe String
  , samplingQuality :: Maybe SamplingQuality
  , preserveTransparency :: Boolean
  , frameBlending :: Boolean
  , timeRemapEnabled :: Boolean
  , collapseTransformations :: Boolean  -- ^ Collapse transformations / Continuously rasterize
  , autoOrient :: AutoOrientMode        -- ^ Auto-orientation mode for layer
  }

derive instance eqLayerBase :: Eq LayerBase

instance showLayerBase :: Show LayerBase where
  show (LayerBase l) = 
    "Layer(" <> l.name <> " @ " <> show l.startFrame <> "-" <> show l.endFrame <> ")"

-- | Default layer base values.
-- |
-- | Creates a default layer at frame 0 with standard settings.
defaultLayerBase :: LayerId -> String -> LayerType -> LayerBase
defaultLayerBase id name lt = LayerBase
  { id: id
  , name: name
  , layerType: lt
  , visible: true
  , locked: false
  , solo: false
  , shy: false
  , enabled: true
  , selected: false
  , collapsed: false
  , guideLayer: false
  , is3D: false
  , blendMode: BMNormal
  , opacity: 100.0
  , startFrame: Frames 0.0
  , endFrame: Frames 300.0    -- 10 seconds at 30fps
  , inPoint: Frames 0.0
  , outPoint: Frames 300.0
  , stretch: 1.0
  , parentId: Nothing
  , trackMatteMode: TMNone
  , trackMatteLayerId: Nothing
  , motionBlur: false
  , qualitySetting: Nothing
  , samplingQuality: Nothing
  , preserveTransparency: false
  , frameBlending: false
  , timeRemapEnabled: false
  , collapseTransformations: false
  , autoOrient: AOMOff
  }

-- | Smart constructor for LayerBase with validation.
-- |
-- | Returns Nothing if parameters are invalid.
mkLayerBase 
  :: LayerId 
  -> String 
  -> LayerType 
  -> Frames   -- startFrame
  -> Frames   -- endFrame
  -> Maybe LayerBase
mkLayerBase id name lt (Frames start) (Frames end)
  | start > end = Nothing
  | start < 0.0 = Nothing
  | otherwise = Just $ LayerBase
      { id: id
      , name: name
      , layerType: lt
      , visible: true
      , locked: false
      , solo: false
      , shy: false
      , enabled: true
      , selected: false
      , collapsed: false
      , guideLayer: false
      , is3D: isLayerType3D lt
      , blendMode: BMNormal
      , opacity: 100.0
      , startFrame: Frames start
      , endFrame: Frames end
      , inPoint: Frames start
      , outPoint: Frames end
      , stretch: 1.0
      , parentId: Nothing
      , trackMatteMode: TMNone
      , trackMatteLayerId: Nothing
      , motionBlur: false
      , qualitySetting: Nothing
      , samplingQuality: Nothing
      , preserveTransparency: false
      , frameBlending: false
      , timeRemapEnabled: false
      , collapseTransformations: false
      , autoOrient: AOMOff
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get layer ID.
layerId :: LayerBase -> LayerId
layerId (LayerBase l) = l.id

-- | Get layer name.
layerName :: LayerBase -> String
layerName (LayerBase l) = l.name

-- | Get layer type.
layerType :: LayerBase -> LayerType
layerType (LayerBase l) = l.layerType

-- | Get layer visibility.
layerVisible :: LayerBase -> Boolean
layerVisible (LayerBase l) = l.visible

-- | Get layer locked state.
layerLocked :: LayerBase -> Boolean
layerLocked (LayerBase l) = l.locked

-- | Get layer solo state.
layerSolo :: LayerBase -> Boolean
layerSolo (LayerBase l) = l.solo

-- | Get layer shy state.
layerShy :: LayerBase -> Boolean
layerShy (LayerBase l) = l.shy

-- | Get layer enabled state.
layerEnabled :: LayerBase -> Boolean
layerEnabled (LayerBase l) = l.enabled

-- | Get layer selected state.
layerSelected :: LayerBase -> Boolean
layerSelected (LayerBase l) = l.selected

-- | Get layer collapsed state.
layerCollapsed :: LayerBase -> Boolean
layerCollapsed (LayerBase l) = l.collapsed

-- | Get guide layer state.
layerGuideLayer :: LayerBase -> Boolean
layerGuideLayer (LayerBase l) = l.guideLayer

-- | Get layer 3D state.
layerIs3D :: LayerBase -> Boolean
layerIs3D (LayerBase l) = l.is3D

-- | Get layer blend mode.
layerBlendMode :: LayerBase -> BlendMode
layerBlendMode (LayerBase l) = l.blendMode

-- | Get layer opacity.
layerOpacity :: LayerBase -> Number
layerOpacity (LayerBase l) = l.opacity

-- | Get layer start frame.
layerStartFrame :: LayerBase -> Frames
layerStartFrame (LayerBase l) = l.startFrame

-- | Get layer end frame.
layerEndFrame :: LayerBase -> Frames
layerEndFrame (LayerBase l) = l.endFrame

-- | Get layer in point.
layerInPoint :: LayerBase -> Frames
layerInPoint (LayerBase l) = l.inPoint

-- | Get layer out point.
layerOutPoint :: LayerBase -> Frames
layerOutPoint (LayerBase l) = l.outPoint

-- | Get layer stretch factor.
layerStretch :: LayerBase -> Number
layerStretch (LayerBase l) = l.stretch

-- | Get layer parent ID.
layerParentId :: LayerBase -> Maybe LayerId
layerParentId (LayerBase l) = l.parentId

-- | Get track matte mode.
layerTrackMatteMode :: LayerBase -> TrackMatteMode
layerTrackMatteMode (LayerBase l) = l.trackMatteMode

-- | Get track matte layer ID.
layerTrackMatteLayerId :: LayerBase -> Maybe LayerId
layerTrackMatteLayerId (LayerBase l) = l.trackMatteLayerId

-- | Get motion blur enabled state.
layerMotionBlur :: LayerBase -> Boolean
layerMotionBlur (LayerBase l) = l.motionBlur

-- | Get quality setting.
layerQualitySetting :: LayerBase -> Maybe String
layerQualitySetting (LayerBase l) = l.qualitySetting

-- | Get sampling quality.
layerSamplingQuality :: LayerBase -> Maybe SamplingQuality
layerSamplingQuality (LayerBase l) = l.samplingQuality

-- | Get preserve transparency state.
layerPreserveTransparency :: LayerBase -> Boolean
layerPreserveTransparency (LayerBase l) = l.preserveTransparency

-- | Get frame blending state.
layerFrameBlending :: LayerBase -> Boolean
layerFrameBlending (LayerBase l) = l.frameBlending

-- | Get time remap enabled state.
layerTimeRemapEnabled :: LayerBase -> Boolean
layerTimeRemapEnabled (LayerBase l) = l.timeRemapEnabled

-- | Get collapse transformations state.
-- |
-- | When enabled on a pre-comp layer, renders at composition resolution
-- | instead of pre-comp resolution. When enabled on a vector layer (shape,
-- | text), continuously rasterizes at current scale.
layerCollapseTransformations :: LayerBase -> Boolean
layerCollapseTransformations (LayerBase l) = l.collapseTransformations

-- | Get auto-orient mode.
-- |
-- | Controls automatic layer orientation:
-- | - Off: No auto-orientation
-- | - Along Path: Layer orients along motion path tangent
-- | - Towards POI: Layer always faces point of interest
layerAutoOrient :: LayerBase -> AutoOrientMode
layerAutoOrient (LayerBase l) = l.autoOrient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if layer is visible.
isLayerVisible :: LayerBase -> Boolean
isLayerVisible l = layerVisible l && layerEnabled l

-- | Check if layer is locked.
isLayerLocked :: LayerBase -> Boolean
isLayerLocked = layerLocked

-- | Check if layer is solo.
isLayerSolo :: LayerBase -> Boolean
isLayerSolo = layerSolo

-- | Check if layer is a guide layer.
isLayerGuide :: LayerBase -> Boolean
isLayerGuide = layerGuideLayer

-- | Check if time remapping is enabled.
isLayerTimeRemapped :: LayerBase -> Boolean
isLayerTimeRemapped = layerTimeRemapEnabled

-- | Check if layer is hidden (not visible or not enabled).
isLayerHidden :: LayerBase -> Boolean
isLayerHidden l = not (isLayerVisible l)

-- | Check if layer is editable (visible and not locked).
isLayerEditable :: LayerBase -> Boolean
isLayerEditable l = isLayerVisible l && not (isLayerLocked l)

-- | Check if layer is active (visible, enabled, not shy).
isLayerActive :: LayerBase -> Boolean
isLayerActive l = layerVisible l && layerEnabled l && not (layerShy l)

-- | Check if layer is a 3D layer type or has 3D enabled.
isLayer3D :: LayerBase -> Boolean
isLayer3D l = layerIs3D l || isLayerType3D (layerType l)

-- | Check if layer has parent.
hasParent :: LayerBase -> Boolean
hasParent l = case layerParentId l of
  Just _ -> true
  Nothing -> false

-- | Check if layer has track matte.
hasTrackMatte :: LayerBase -> Boolean
hasTrackMatte l = layerTrackMatteMode l /= TMNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layer // ordering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare layers by start frame (for timeline ordering).
compareByStartFrame :: LayerBase -> LayerBase -> Ordering
compareByStartFrame a b = compare (layerStartFrame a) (layerStartFrame b)

-- | Compare layers by end frame.
compareByEndFrame :: LayerBase -> LayerBase -> Ordering
compareByEndFrame a b = compare (layerEndFrame a) (layerEndFrame b)

-- | Compare layers by name (alphabetical).
compareByName :: LayerBase -> LayerBase -> Ordering
compareByName a b = compare (layerName a) (layerName b)

-- | Get the layer that starts earlier.
earlierLayer :: LayerBase -> LayerBase -> LayerBase
earlierLayer a b = case compareByStartFrame a b of
  LT -> a
  _  -> b

-- | Get the layer that starts later.
laterLayer :: LayerBase -> LayerBase -> LayerBase
laterLayer a b = case compareByStartFrame a b of
  GT -> a
  _  -> b

-- | Get minimum start frame of two layers.
minStartFrame :: LayerBase -> LayerBase -> Frames
minStartFrame a b = min (layerStartFrame a) (layerStartFrame b)

-- | Get maximum end frame of two layers.
maxEndFrame :: LayerBase -> LayerBase -> Frames
maxEndFrame a b = max (layerEndFrame a) (layerEndFrame b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // frame // arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get layer duration in frames.
layerDuration :: LayerBase -> Frames
layerDuration l = 
  let Frames start = layerStartFrame l
      Frames end = layerEndFrame l
  in Frames (end - start)

-- | Get trimmed duration (outPoint - inPoint).
layerTrimmedDuration :: LayerBase -> Frames
layerTrimmedDuration l =
  let Frames inPt = layerInPoint l
      Frames outPt = layerOutPoint l
  in Frames (outPt - inPt)

-- | Get effective duration accounting for stretch.
layerEffectiveDuration :: LayerBase -> Frames
layerEffectiveDuration l =
  let Frames dur = layerTrimmedDuration l
      str = layerStretch l
  in Frames (dur * str)

-- | Check if a frame is within the layer's time range.
isFrameInLayer :: Frames -> LayerBase -> Boolean
isFrameInLayer (Frames f) l =
  let Frames start = layerStartFrame l
      Frames end = layerEndFrame l
  in f >= start && f < end

-- | Get frame offset from layer start.
frameOffsetFromStart :: Frames -> LayerBase -> Frames
frameOffsetFromStart (Frames f) l =
  let Frames start = layerStartFrame l
  in Frames (f - start)

-- | Get distance between two layers' start frames.
layerDistance :: LayerBase -> LayerBase -> Frames
layerDistance a b =
  let Frames startA = layerStartFrame a
      Frames startB = layerStartFrame b
  in Frames (abs (startA - startB))

-- | Reverse layer time (for reverse playback).
-- |
-- | Negates the stretch factor, swaps in/out points.
reverseLayerTime :: LayerBase -> LayerBase
reverseLayerTime (LayerBase l) = LayerBase l
  { stretch = negate l.stretch
  , inPoint = l.outPoint
  , outPoint = l.inPoint
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer // modify
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set layer opacity (0-100).
setOpacity :: Number -> LayerBase -> LayerBase
setOpacity op (LayerBase l) = LayerBase l { opacity = op }

-- | Set layer visibility.
setVisible :: Boolean -> LayerBase -> LayerBase
setVisible v (LayerBase l) = LayerBase l { visible = v }

-- | Set layer locked state.
setLocked :: Boolean -> LayerBase -> LayerBase
setLocked v (LayerBase l) = LayerBase l { locked = v }

-- | Set layer solo state.
setSolo :: Boolean -> LayerBase -> LayerBase
setSolo v (LayerBase l) = LayerBase l { solo = v }

-- | Set layer shy state.
setShy :: Boolean -> LayerBase -> LayerBase
setShy v (LayerBase l) = LayerBase l { shy = v }

-- | Set layer enabled state.
setEnabled :: Boolean -> LayerBase -> LayerBase
setEnabled v (LayerBase l) = LayerBase l { enabled = v }

-- | Set layer 3D state.
set3D :: Boolean -> LayerBase -> LayerBase
set3D v (LayerBase l) = LayerBase l { is3D = v }

-- | Set layer blend mode.
setBlendMode :: BlendMode -> LayerBase -> LayerBase
setBlendMode bm (LayerBase l) = LayerBase l { blendMode = bm }

-- | Set layer name.
setName :: String -> LayerBase -> LayerBase
setName n (LayerBase l) = LayerBase l { name = n }

-- | Set layer parent.
setParent :: Maybe LayerId -> LayerBase -> LayerBase
setParent p (LayerBase l) = LayerBase l { parentId = p }

-- | Set layer start frame.
setStartFrame :: Frames -> LayerBase -> LayerBase
setStartFrame f (LayerBase l) = LayerBase l { startFrame = f }

-- | Set layer end frame.
setEndFrame :: Frames -> LayerBase -> LayerBase
setEndFrame f (LayerBase l) = LayerBase l { endFrame = f }

-- | Set layer in point.
setInPoint :: Frames -> LayerBase -> LayerBase
setInPoint f (LayerBase l) = LayerBase l { inPoint = f }

-- | Set layer out point.
setOutPoint :: Frames -> LayerBase -> LayerBase
setOutPoint f (LayerBase l) = LayerBase l { outPoint = f }

-- | Set layer stretch factor.
setStretch :: Number -> LayerBase -> LayerBase
setStretch s (LayerBase l) = LayerBase l { stretch = s }

-- | Set motion blur enabled.
setMotionBlur :: Boolean -> LayerBase -> LayerBase
setMotionBlur v (LayerBase l) = LayerBase l { motionBlur = v }

-- | Set track matte mode.
setTrackMatteMode :: TrackMatteMode -> LayerBase -> LayerBase
setTrackMatteMode tm (LayerBase l) = LayerBase l { trackMatteMode = tm }

-- | Set track matte layer.
setTrackMatteLayer :: Maybe LayerId -> LayerBase -> LayerBase
setTrackMatteLayer lid (LayerBase l) = LayerBase l { trackMatteLayerId = lid }

-- | Set auto-orient mode.
setAutoOrient :: AutoOrientMode -> LayerBase -> LayerBase
setAutoOrient ao (LayerBase l) = LayerBase l { autoOrient = ao }

-- | Set collapse transformations / continuously rasterize.
setCollapseTransformations :: Boolean -> LayerBase -> LayerBase
setCollapseTransformations v (LayerBase l) = LayerBase l { collapseTransformations = v }

-- | Set time remap enabled.
setTimeRemapEnabled :: Boolean -> LayerBase -> LayerBase
setTimeRemapEnabled v (LayerBase l) = LayerBase l { timeRemapEnabled = v }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // fluent // api // chains
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity transform — returns layer unchanged.
-- |
-- | Useful as a no-op in conditional pipelines:
-- | ```purescript
-- | layer # (if condition then setOpacity 50.0 else identityLayer)
-- | ```
identityLayer :: LayerBase -> LayerBase
identityLayer = identity

-- | Constant layer — ignores input, returns fixed layer.
-- |
-- | Useful for replacement in pipelines:
-- | ```purescript
-- | layers # map (constLayer defaultLayer)
-- | ```
constLayer :: LayerBase -> LayerBase -> LayerBase
constLayer = const

-- | Flip a two-argument layer function.
-- |
-- | ```purescript
-- | -- Instead of: setOpacity 50.0 layer
-- | -- Write: flip setOpacity layer 50.0
-- | ```
flipLayerFn :: forall a. (a -> LayerBase -> LayerBase) -> LayerBase -> a -> LayerBase
flipLayerFn = flip

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // pipeline // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compose two layer transformations (right to left).
-- |
-- | ```purescript
-- | makeInvisibleAndLocked = setLocked true <<< setVisible false
-- | ```
composeTransforms 
  :: (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase)
composeTransforms = (<<<)

-- | Compose two layer transformations (left to right).
-- |
-- | ```purescript
-- | makeInvisibleThenLock = setVisible false >>> setLocked true
-- | ```
pipeTransforms 
  :: (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase)
pipeTransforms = (>>>)

-- | Apply a transformation to a layer using fluent syntax.
-- |
-- | ```purescript
-- | layer 
-- |   # setOpacity 50.0
-- |   # setBlendMode BMMultiply
-- |   # setVisible true
-- | ```
applyTo :: forall a b. a -> (a -> b) -> b
applyTo = (#)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // layer // list // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a transformation to a layer.
-- |
-- | This is just function application, but named for clarity in pipelines:
-- | ```purescript
-- | mapLayer (setOpacity 50.0) layer
-- | ```
mapLayer :: (LayerBase -> LayerBase) -> LayerBase -> LayerBase
mapLayer f l = f l

-- | Lift a value into a layer context (identity).
-- |
-- | For LayerBase, this is identity — the value IS the layer.
-- | Useful for consistency in generic code.
pureLayer :: LayerBase -> LayerBase
pureLayer l = l

-- | Sequence two Maybe layer operations.
-- |
-- | ```purescript
-- | -- Get parent, then get that parent's opacity
-- | getParentOpacity :: LayerBase -> (LayerId -> Maybe LayerBase) -> Maybe Number
-- | getParentOpacity layer lookupLayer = 
-- |   bindLayer (layerParentId layer) lookupLayer
-- | ```
bindLayer :: forall a. Maybe a -> (a -> Maybe LayerBase) -> Maybe LayerBase
bindLayer ma f = bind ma f

-- | Apply a Maybe function to a Maybe layer.
-- |
-- | Useful for conditional transformations:
-- | ```purescript
-- | applyMaybeTransform :: Maybe (LayerBase -> LayerBase) -> Maybe LayerBase -> Maybe LayerBase
-- | applyMaybeTransform mf ml = applyLayerFn mf ml
-- | ```
applyLayerFn :: forall a b. Maybe (a -> b) -> Maybe a -> Maybe b
applyLayerFn mf ma = apply mf ma