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
-- | Supports 56 layer types matching professional motion graphics and LATTICE:
-- | - Media layers: Image, Video, Audio, Solid
-- | - Content layers: Text, Shape, Null
-- | - 3D layers: Camera, Light, Mesh, Environment, Volume
-- | - Effects: Adjustment, Effect
-- | - Composition: PreComp, Group, NestedComp
-- | - Vector: SVG, Lottie, Rive, VectorGraphic
-- | - Audio: Waveform, Spectrogram, MIDI
-- | - Data: CSV, JSON, GeoJSON
-- | - Annotation: Marker, Subtitle, Comment
-- | - Tracking: Tracker, Mocha, Stabilizer
-- | - Utility: Reference, Grid, Guide, Mask, Roto
-- | - Color Grading: HDR, LUT, Gradient
-- |
-- | ## Architecture
-- |
-- | This is the leader module that re-exports all Layer submodules:
-- | - `Layer.Types`: LayerType enum and category predicates
-- | - `Layer.Base`: LayerBase record, LayerId, constructors, accessors
-- | - `Layer.Operations`: Modifiers, predicates, frame arithmetic, ordering
-- |
-- | Mirrors `Lattice.Project` LayerType and LayerBase from the Haskell backend,
-- | ensuring type-level compatibility for serialization.

module Hydrogen.Schema.Motion.Layer
  ( -- * Re-exports from Types
    module Types
    
  -- * Re-exports from Base
  , module Base
  
  -- * Re-exports from Operations
  , module Operations
  ) where

import Hydrogen.Schema.Motion.Layer.Types
  ( LayerType(..)
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
  , isLayerTypeComposition
  , isLayerTypeEffect
  , requiresGPU
  , requiresAudioEngine
  , isRenderLayer
  , isHelperLayer
  ) as Types

import Hydrogen.Schema.Motion.Layer.Base
  ( LayerId(..)
  , mkLayerId
  , LayerVisibility(..)
  , layerVisibilityToString
  , layerVisibilityFromString
  , defaultVisibility
  , hiddenVisibility
  , lockedVisibility
  , soloVisibility
  , SamplingQuality(..)
  , samplingQualityToString
  , samplingQualityFromString
  , LayerBase(..)
  , defaultLayerBase
  , mkLayerBase
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
  ) as Base

import Hydrogen.Schema.Motion.Layer.Operations
  ( isLayerVisible
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
  , compareByStartFrame
  , compareByEndFrame
  , compareByName
  , earlierLayer
  , laterLayer
  , minStartFrame
  , maxEndFrame
  , layerDuration
  , layerTrimmedDuration
  , layerEffectiveDuration
  , isFrameInLayer
  , frameOffsetFromStart
  , layerDistance
  , reverseLayerTime
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
  , identityLayer
  , constLayer
  , flipLayerFn
  , applyTo
  , composeTransforms
  , pipeTransforms
  , mapLayer
  , pureLayer
  , bindLayer
  , applyLayerFn
  ) as Operations
