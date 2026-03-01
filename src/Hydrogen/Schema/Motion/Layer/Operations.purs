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
  , getLayerType
  , layerTypeId
  , hasParent
  , hasTrackMatte
    -- * Layer Equality
  , sameLayerTiming
  , sameLayerType
  , sameLayerVisibility
  , sameLayerState
    -- * Layer Ordering
  , compareByStartFrame
  , compareByEndFrame
  , compareByName
  , compareByDuration
  , compareByOpacity
  , earlierLayer
  , laterLayer
  , simultaneousLayers
  , minStartFrame
  , maxEndFrame
    -- * Frame Arithmetic
  , layerDuration
  , layerTrimmedDuration
  , layerEffectiveDuration
  , isFrameInLayer
  , frameOffsetFromStart
  , frameOffsetFromEnd
  , layerDistance
  , layerOverlap
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
  , shiftLayerTime
    -- * LayerTransform Monoid
  , LayerTransform(..)
  , runTransform
  , mkTransform
  , emptyTransform
  , combineTransforms
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
  , liftLayer
  , transformWith
    -- * Debug
  , showLayerDebug
  ) where

import Prelude
  ( class Semigroup
  , class Monoid
  , class Show
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
  , show
  , mempty
  , append
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Ord (abs)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))
import Hydrogen.Schema.Motion.Composition (BlendMode, TrackMatteMode(TMNone))
import Hydrogen.Schema.Motion.Camera3D.Enums (AutoOrientMode)
import Hydrogen.Schema.Motion.Layer.Types 
  ( LayerType
  , isLayerType3D
  , layerTypeToString
  )
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
  , layerOpacity
  , layerParentId
  , layerTrackMatteMode
  , layerTimeRemapEnabled
  , layerStartFrame
  , layerEndFrame
  , layerInPoint
  , layerOutPoint
  , layerStretch
  , layerBlendMode
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

-- | Get the layer type.
getLayerType :: LayerBase -> LayerType
getLayerType = layerType

-- | Get layer type as string identifier.
layerTypeId :: LayerBase -> String
layerTypeId l = layerTypeToString (layerType l)

-- | Check if layer has parent.
hasParent :: LayerBase -> Boolean
hasParent l = case layerParentId l of
  Just _ -> true
  Nothing -> false

-- | Check if layer has track matte.
hasTrackMatte :: LayerBase -> Boolean
hasTrackMatte l = layerTrackMatteMode l /= TMNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layer // equality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two layers have the same timing (start, end, in, out, stretch).
sameLayerTiming :: LayerBase -> LayerBase -> Boolean
sameLayerTiming a b =
  layerStartFrame a == layerStartFrame b &&
  layerEndFrame a == layerEndFrame b &&
  layerInPoint a == layerInPoint b &&
  layerOutPoint a == layerOutPoint b &&
  layerStretch a == layerStretch b

-- | Check if two layers have the same type.
sameLayerType :: LayerBase -> LayerBase -> Boolean
sameLayerType a b = layerType a == layerType b

-- | Check if two layers have the same visibility state.
sameLayerVisibility :: LayerBase -> LayerBase -> Boolean
sameLayerVisibility a b =
  layerVisible a == layerVisible b &&
  layerLocked a == layerLocked b &&
  layerSolo a == layerSolo b &&
  layerShy a == layerShy b &&
  layerEnabled a == layerEnabled b

-- | Check if two layers have equivalent state (type, timing, visibility).
sameLayerState :: LayerBase -> LayerBase -> Boolean
sameLayerState a b =
  sameLayerType a b &&
  sameLayerTiming a b &&
  sameLayerVisibility a b

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

-- | Compare layers by duration.
compareByDuration :: LayerBase -> LayerBase -> Ordering
compareByDuration a b = compare (layerDuration a) (layerDuration b)

-- | Compare layers by opacity.
compareByOpacity :: LayerBase -> LayerBase -> Ordering
compareByOpacity a b = compare (layerOpacity a) (layerOpacity b)

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

-- | Check if two layers start at the same frame.
simultaneousLayers :: LayerBase -> LayerBase -> Boolean
simultaneousLayers a b = case compareByStartFrame a b of
  EQ -> true
  _  -> false

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

-- | Get frame offset from layer end (negative if before end).
frameOffsetFromEnd :: Frames -> LayerBase -> Frames
frameOffsetFromEnd (Frames f) l =
  let Frames end = layerEndFrame l
  in Frames (f - end)

-- | Get distance between two layers' start frames.
layerDistance :: LayerBase -> LayerBase -> Frames
layerDistance a b =
  let Frames startA = layerStartFrame a
      Frames startB = layerStartFrame b
  in Frames (abs (startA - startB))

-- | Calculate overlap duration between two layers.
-- |
-- | Returns Frames 0 if layers don't overlap.
layerOverlap :: LayerBase -> LayerBase -> Frames
layerOverlap a b =
  let Frames startA = layerStartFrame a
      Frames endA = layerEndFrame a
      Frames startB = layerStartFrame b
      Frames endB = layerEndFrame b
      overlapStart = max startA startB
      overlapEnd = min endA endB
      overlap = overlapEnd - overlapStart
  in if overlap >= 0.0 then Frames overlap else Frames 0.0

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

-- | Shift layer timing by a number of frames.
-- |
-- | Positive values move the layer later in the timeline.
-- | Negative values move the layer earlier.
-- | Both startFrame and endFrame are adjusted together.
shiftLayerTime :: Number -> LayerBase -> LayerBase
shiftLayerTime offset (LayerBase l) = 
  let Frames start = l.startFrame
      Frames end = l.endFrame
  in LayerBase l 
    { startFrame = Frames $ start + offset
    , endFrame = Frames $ end + offset
    }

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

-- | Lift a layer into Maybe context.
-- |
-- | Useful for composing with functions that may fail.
liftLayer :: LayerBase -> Maybe LayerBase
liftLayer l = pure l

-- | Apply a transform, returning the result with function application.
-- |
-- | Uses explicit ($) for clarity in complex expressions.
transformWith :: (LayerBase -> LayerBase) -> LayerBase -> LayerBase
transformWith f l = f $ l

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // layer // transform // monoid
-- ═════════════════════════════════════════════════════════════════════════════

-- | LayerTransform — a newtype for layer transformations with Monoid instance.
-- |
-- | Layer transformations form a monoid under composition:
-- | - Identity: `identityLayer` (no change)
-- | - Combine: `(<<<)` (right-to-left composition)
-- |
-- | This enables composing transform pipelines algebraically:
-- | ```purescript
-- | pipeline :: LayerTransform
-- | pipeline = mkTransform (setOpacity 50.0) 
-- |         <> mkTransform (setVisible true)
-- |         <> mkTransform (set3D true)
-- | 
-- | result = runTransform pipeline layer
-- | ```
newtype LayerTransform = LayerTransform (LayerBase -> LayerBase)

-- | Run a LayerTransform on a layer.
runTransform :: LayerTransform -> LayerBase -> LayerBase
runTransform (LayerTransform f) l = f l

-- | Create a LayerTransform from a layer function.
mkTransform :: (LayerBase -> LayerBase) -> LayerTransform
mkTransform = LayerTransform

instance semigroupLayerTransform :: Semigroup LayerTransform where
  append (LayerTransform f) (LayerTransform g) = LayerTransform (f <<< g)

instance monoidLayerTransform :: Monoid LayerTransform where
  mempty = LayerTransform identity

instance showLayerTransform :: Show LayerTransform where
  show _ = "(LayerTransform <function>)"

-- | The empty (identity) transform — applies no changes.
-- |
-- | This is the monoid identity: `emptyTransform <> t == t == t <> emptyTransform`
emptyTransform :: LayerTransform
emptyTransform = mempty

-- | Combine two transforms into one (left-to-right application).
-- |
-- | `combineTransforms a b` applies `a` first, then `b`.
-- | This uses the Semigroup instance explicitly.
combineTransforms :: LayerTransform -> LayerTransform -> LayerTransform
combineTransforms a b = append a b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a debug string for a layer with full details.
-- |
-- | Follows the Show Debug Convention: output is structured and parseable,
-- | includes all relevant state for debugging at billion-agent scale.
-- |
-- | Example output:
-- | ```
-- | (LayerDebug 
-- |   name:"Background" 
-- |   type:solid 
-- |   frames:0.0-300.0 
-- |   visible:true locked:false 3d:false
-- |   opacity:100.0 
-- |   blend:normal)
-- | ```
showLayerDebug :: LayerBase -> String
showLayerDebug l =
  "(LayerDebug " <>
  "name:" <> show (layerName l) <> " " <>
  "type:" <> layerTypeToString (layerType l) <> " " <>
  "frames:" <> showFrameRange l <> " " <>
  "visible:" <> show (layerVisible l) <> " " <>
  "locked:" <> show (layerLocked l) <> " " <>
  "3d:" <> show (isLayer3D l) <> " " <>
  "opacity:" <> show (layerOpacity l) <> " " <>
  "blend:" <> show (layerBlendMode l) <>
  ")"
  where
    showFrameRange :: LayerBase -> String
    showFrameRange layer = 
      let Frames start = layerStartFrame layer
          Frames end = layerEndFrame layer
      in show start <> "-" <> show end
