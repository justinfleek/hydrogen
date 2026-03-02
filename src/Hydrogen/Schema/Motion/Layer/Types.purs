-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // layer // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer type enumeration and category predicates.
-- |
-- | Defines the complete vocabulary of layer types for motion graphics,
-- | matching professional motion graphics and LATTICE backend conventions.
-- |
-- | ## Layer Categories
-- |
-- | Layers are organized into functional categories:
-- | - **Media**: Image, Video, Audio, Solid — source footage layers
-- | - **Content**: Text, Shape, Null — user-created content
-- | - **3D**: Camera, Light, Mesh, Environment — 3D rendering
-- | - **Effects**: Adjustment, Effect — visual processing
-- | - **Composition**: PreComp, Group, NestedComp — organization
-- | - **Vector**: SVG, Lottie, Rive, Path — vector graphics
-- | - **Audio**: Waveform, Spectrogram, MIDI — audio visualization
-- | - **Data**: CSV, JSON, GeoJSON — structured data
-- | - **Annotation**: Marker, Subtitle, Comment — metadata
-- | - **Tracking**: Tracker, PlanarTracking, Stabilizer — motion analysis
-- | - **Utility**: Reference, Grid, Guide, Mask — helpers
-- | - **Color Grading**: HDR, LUT, Gradient — color processing
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Project.LayerType` from the Haskell backend.
-- | Every LayerType has:
-- | - String serialization (for JSON/YAML)
-- | - Category membership predicates
-- | - 3D/2D classification

module Hydrogen.Schema.Motion.Layer.Types
  ( -- * Layer Type
    LayerType(..)
  , layerTypeToString
  , layerTypeFromString
  
  -- * Category Predicates
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
  , isLayerTypeComposition
  , isLayerTypeEffect
  
  -- * Rendering Classification
  , requiresGPU
  , requiresAudioEngine
  , isRenderLayer
  , isHelperLayer
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (||)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layer // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of layer content.
-- |
-- | Defines the rendering behavior and available animatable properties.
-- | Each variant corresponds to a specific content type in motion graphics software.
data LayerType
  -- Media layers
  = LTImage            -- ^ Static image (PNG, JPG, SVG, etc.)
  | LTVideo            -- ^ Video clip with duration
  | LTSolid            -- ^ Solid color fill layer
  | LTAudio            -- ^ Audio clip
  
  -- Content layers
  | LTText             -- ^ Text/typography layer
  | LTShape            -- ^ Vector shape layer
  | LTNull             -- ^ Null object (no render, anchor point only)
  
  -- 3D layers
  | LTCamera           -- ^ Camera for 3D composition
  | LTLight            -- ^ Light source (point, spot, directional)
  
  -- Effect layers
  | LTAdjustment       -- ^ Adjustment layer (effects below)
  | LTEffect           -- ^ Effect layer
  
  -- Composition layers
  | LTPreComp         -- ^ Pre-composition (collapsed nested timeline)
  | LTGroup           -- ^ Group/layer folder
  | LTNestedComp      -- ^ Nested composition reference
  
  -- Specialized layers
  | LTParticle        -- ^ Particle system
  | LTDepth           -- ^ Depth map layer
  | LTNormal          -- ^ Normal map layer
  | LTGenerated       -- ^ Procedurally generated content
  | LTMatte           -- ^ Matte/garbage mask layer
  | LTControl         -- ^ Control layer (for expressions)
  | LTSpline          -- ^ Spline/path animation
  | LTPath            -- ^ Path definition layer
  | LTPose            -- ^ Pose/animation reference
  | LTModel           -- ^ 3D model layer
  | LTPointCloud      -- ^ Point cloud data
  | LTDepthflow       -- ^ Depth flow animation
  
  -- Vector & Graphics layers
  | LTSVG             -- ^ SVG vector graphics
  | LTVectorGraphic   -- ^ Generic vector graphic (AI, EPS, PDF)
  | LTLottie          -- ^ Lottie animation (JSON)
  | LTRive            -- ^ Rive animation
  
  -- 3D & Spatial layers
  | LTMesh            -- ^ 3D mesh geometry
  | LTEnvironment     -- ^ Environment map (HDRI, cubemap)
  | LTVolume          -- ^ Volumetric data (VDB, density fields)
  | LTSkeleton        -- ^ Skeletal animation rig
  
  -- Color & Grading layers
  | LTHDR             -- ^ HDR image layer
  | LTLUT             -- ^ LUT (lookup table) layer
  | LTGradient        -- ^ Gradient ramp layer
  
  -- Audio & Waveform layers
  | LTWaveform        -- ^ Audio waveform visualization
  | LTSpectrogram     -- ^ Audio spectrogram visualization
  | LTMIDI            -- ^ MIDI data layer
  
  -- Data & Structured layers
  | LTCSV             -- ^ CSV data layer
  | LTJSON            -- ^ JSON data layer
  | LTGeoJSON         -- ^ GeoJSON geographic data
  | LTData            -- ^ Generic structured data
  
  -- Annotation & Metadata layers
  | LTMarker          -- ^ Timeline markers
  | LTSubtitle        -- ^ Subtitles/captions (SRT, VTT)
  | LTAnnotation      -- ^ Visual annotations
  | LTComment         -- ^ Comment/note layer
  
  -- Tracking & Motion layers  
  | LTTracker         -- ^ Motion tracking data
  | LTPlanarTracking  -- ^ Planar tracking (surface/perspective tracking)
  | LTStabilizer      -- ^ Stabilization reference
  
  -- Compositing utility layers
  | LTReference       -- ^ Reference image (non-rendering)
  | LTGrid            -- ^ Grid overlay
  | LTGuide           -- ^ Guide lines
  | LTMask            -- ^ Mask layer (separate from matte)
  | LTRoto            -- ^ Rotoscoping layer

derive instance eqLayerType :: Eq LayerType
derive instance ordLayerType :: Ord LayerType

instance showLayerType :: Show LayerType where
  show = layerTypeToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // serialization
-- ═════════════════════════════════════════════════════════════════════════════

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
layerTypeToString LTPlanarTracking = "planartracking"
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
layerTypeFromString "planartracking" = Just LTPlanarTracking
layerTypeFromString "stabilizer" = Just LTStabilizer
-- Compositing utility
layerTypeFromString "reference" = Just LTReference
layerTypeFromString "grid" = Just LTGrid
layerTypeFromString "guide" = Just LTGuide
layerTypeFromString "mask" = Just LTMask
layerTypeFromString "roto" = Just LTRoto
layerTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // category // predicates
-- ═════════════════════════════════════════════════════════════════════════════

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
isLayerTypeTracking LTPlanarTracking = true
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

-- | Check if layer type is a composition container.
isLayerTypeComposition :: LayerType -> Boolean
isLayerTypeComposition LTPreComp = true
isLayerTypeComposition LTGroup = true
isLayerTypeComposition LTNestedComp = true
isLayerTypeComposition _ = false

-- | Check if layer type is an effect processor.
isLayerTypeEffect :: LayerType -> Boolean
isLayerTypeEffect LTAdjustment = true
isLayerTypeEffect LTEffect = true
isLayerTypeEffect _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // rendering // classification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if layer type requires GPU rendering.
-- |
-- | These layer types need WebGL or similar for efficient rendering:
-- | - 3D layers (mesh, volume, environment)
-- | - Particle systems
-- | - Complex vector animations (Lottie, Rive)
requiresGPU :: LayerType -> Boolean
requiresGPU lt = isLayerType3D lt 
  || lt == LTParticle 
  || lt == LTLottie 
  || lt == LTRive
  || lt == LTGenerated

-- | Check if layer type requires audio engine.
-- |
-- | These layer types need Web Audio API or similar for processing.
requiresAudioEngine :: LayerType -> Boolean
requiresAudioEngine = isLayerTypeAudio

-- | Check if layer type produces visible output.
-- |
-- | Some layers are helpers (null, control, reference) that don't render.
isRenderLayer :: LayerType -> Boolean
isRenderLayer LTNull = false
isRenderLayer LTControl = false
isRenderLayer LTReference = false
isRenderLayer LTGuide = false
isRenderLayer LTMarker = false
isRenderLayer LTComment = false
isRenderLayer _ = true

-- | Check if layer type is a helper (non-rendering).
-- |
-- | Inverse of isRenderLayer for semantic clarity.
isHelperLayer :: LayerType -> Boolean
isHelperLayer LTNull = true
isHelperLayer LTControl = true
isHelperLayer LTReference = true
isHelperLayer LTGuide = true
isHelperLayer LTMarker = true
isHelperLayer LTComment = true
isHelperLayer _ = false
