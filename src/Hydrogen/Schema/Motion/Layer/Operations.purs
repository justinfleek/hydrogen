-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // layer // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Layer operations: modifiers, predicates, frame arithmetic, ordering.

module Hydrogen.Schema.Motion.Layer.Operations
  ( -- * Predicates
    isLayerVisible
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
  ( class Semigroup
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
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , negate
  , identity
  , const
  , flip
  , apply
  , pure
  , bind
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Ord (abs)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))
import Hydrogen.Schema.Motion.Composition (BlendMode, TrackMatteMode(TMNone))
import Hydrogen.Schema.Motion.Camera3D.Enums (AutoOrientMode)
import Hydrogen.Schema.Motion.Layer.Types (LayerType, isLayerType3D)
import Hydrogen.Schema.Motion.Layer.Base
  ( LayerBase(LayerBase)
  , LayerId
  , layerName
  , layerVisible
  , layerLocked
  , layerSolo
  , layerShy
  , layerEnabled
  , layerGuideLayer
  , layerIs3D
  , layerType
  , layerParentId
  , layerTrackMatteMode
  , layerTimeRemapEnabled
  , layerStartFrame
  , layerEndFrame
  , layerInPoint
  , layerOutPoint
  , layerStretch
  )

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
--                                                                  // modifiers
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
--                                                                // fluent // api
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity transform — returns layer unchanged.
identityLayer :: LayerBase -> LayerBase
identityLayer = identity

-- | Constant layer — ignores input, returns fixed layer.
constLayer :: LayerBase -> LayerBase -> LayerBase
constLayer = const

-- | Flip a two-argument layer function.
flipLayerFn :: forall a. (a -> LayerBase -> LayerBase) -> LayerBase -> a -> LayerBase
flipLayerFn = flip

-- | Apply a transformation to a layer using fluent syntax.
applyTo :: forall a b. a -> (a -> b) -> b
applyTo = (#)

-- | Compose two layer transformations (right to left).
composeTransforms 
  :: (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase)
composeTransforms = (<<<)

-- | Compose two layer transformations (left to right).
pipeTransforms 
  :: (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase) 
  -> (LayerBase -> LayerBase)
pipeTransforms = (>>>)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layer // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a transformation to a layer.
mapLayer :: (LayerBase -> LayerBase) -> LayerBase -> LayerBase
mapLayer f l = f l

-- | Lift a value into a layer context (identity).
pureLayer :: LayerBase -> LayerBase
pureLayer l = l

-- | Sequence two Maybe layer operations.
bindLayer :: forall a. Maybe a -> (a -> Maybe LayerBase) -> Maybe LayerBase
bindLayer ma f = bind ma f

-- | Apply a Maybe function to a Maybe layer.
applyLayerFn :: forall a b. Maybe (a -> b) -> Maybe a -> Maybe b
applyLayerFn mf ma = apply mf ma
