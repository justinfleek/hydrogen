-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // animated-transform // evaluation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Evaluation — Functions for evaluating animated values at specific frames.
-- |
-- | ## Design Philosophy
-- |
-- | Evaluation is the process of computing concrete values from animated
-- | properties at a specific point in time (frame). This module provides:
-- |
-- | - Single value evaluation (evaluateAt)
-- | - Full transform evaluation (2D and 3D)
-- | - Keyframe interpolation with speed graph support
-- |
-- | ## Dependencies
-- |
-- | - AnimatedTransform.Core (AnimatableValue, SpeedGraph, evaluateSpeedGraph)
-- | - AnimatedTransform.Properties (all property types)
-- | - AnimatedTransform.Transform (AnimatedTransform2D, AnimatedTransform3D)
-- | - Schema.Dimension.Temporal (Frames)
-- | - Schema.Motion.Easing (evaluate, linear)

module Hydrogen.Schema.Motion.AnimatedTransform.Evaluation
  ( -- * Value Evaluation
    evaluateAt
  , evaluateKeyframes
  , applyInterpolation
  
  -- * Transform Evaluation
  , evaluateTransform2DAt
  , evaluateTransform3DAt
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Ord
  , compare
  , (==)
  , (<)
  , (>)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , otherwise
  )

import Data.Array (length, filter, sortBy, head, index)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Temporal (Frames(Frames), unwrapFrames)
import Hydrogen.Schema.Motion.Interpolation (FullInterpolationType)
import Hydrogen.Schema.Motion.Easing (evaluate, linear)

import Hydrogen.Schema.Motion.AnimatedTransform.Core
  ( AnimatableValue(AnimatableValue)
  , PropertyKeyframe
  , SpeedGraph
  , keyframeFrame
  , keyframeValue
  , keyframeInterpolation
  , evaluateSpeedGraph
  )

import Hydrogen.Schema.Motion.AnimatedTransform.Properties
  ( AnimatedPosition2D(AnimatedPosition2D)
  , AnimatedPosition3D(AnimatedPosition3D)
  , AnimatedScale2D(AnimatedScale2D)
  , AnimatedScale3D(AnimatedScale3D)
  , AnimatedRotation(AnimatedRotation)
  , AnimatedRotation3D(AnimatedRotation3D)
  , AnimatedAnchor2D(AnimatedAnchor2D)
  , AnimatedAnchor3D(AnimatedAnchor3D)
  , AnimatedOpacity(AnimatedOpacity)
  )

import Hydrogen.Schema.Motion.AnimatedTransform.Transform
  ( AnimatedTransform2D(AnimatedTransform2D)
  , AnimatedTransform3D(AnimatedTransform3D)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate an animatable value at a specific frame.
-- |
-- | If not animated, returns static value.
-- | If animated, interpolates between surrounding keyframes.
evaluateAt :: Frames -> AnimatableValue -> Number
evaluateAt frame (AnimatableValue av)
  | length av.keyframes == 0 = av.staticValue
  | otherwise = evaluateKeyframes frame av.keyframes av.speedGraph

-- | Interpolate between keyframes at frame.
evaluateKeyframes :: Frames -> Array PropertyKeyframe -> Maybe SpeedGraph -> Number
evaluateKeyframes frame keyframes maybeSpeedGraph =
  let
    -- Apply speed graph if present
    actualFrame = case maybeSpeedGraph of
      Just sg -> Frames $ evaluateSpeedGraph (unwrapFrames frame) sg
      Nothing -> frame
    
    frameNum = unwrapFrames actualFrame
    
    -- Find bracketing keyframes
    before = filter (\kf -> unwrapFrames (keyframeFrame kf) <= frameNum) keyframes
    after = filter (\kf -> unwrapFrames (keyframeFrame kf) > frameNum) keyframes
  in case { b: lastPoint (sortBy compare before), a: head (sortBy compare after) } of
    -- Before all keyframes: use first keyframe value
    { b: Nothing, a: Just kf } -> keyframeValue kf
    -- After all keyframes: use last keyframe value
    { b: Just kf, a: Nothing } -> keyframeValue kf
    -- Between keyframes: interpolate
    { b: Just kf1, a: Just kf2 } ->
      let
        f1 = unwrapFrames (keyframeFrame kf1)
        f2 = unwrapFrames (keyframeFrame kf2)
        t = if f2 == f1 then 0.0 else (frameNum - f1) / (f2 - f1)
        v1 = keyframeValue kf1
        v2 = keyframeValue kf2
        -- Apply easing based on interpolation type
        easedT = applyInterpolation t (keyframeInterpolation kf1)
      in v1 + easedT * (v2 - v1)
    -- No keyframes at all (shouldn't happen)
    _ -> 0.0

-- | Apply interpolation type to t value.
applyInterpolation :: Number -> FullInterpolationType -> Number
applyInterpolation t _ = 
  -- For now, use linear; full implementation would map to Easing
  evaluate linear t

-- | Get last point in array.
lastPoint :: forall a. Array a -> Maybe a
lastPoint arr = index arr (length arr - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // transform // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate 2D transform at frame, returning static values.
evaluateTransform2DAt :: Frames -> AnimatedTransform2D 
  -> { posX :: Number, posY :: Number, scaleX :: Number, scaleY :: Number
     , rotation :: Number, anchorX :: Number, anchorY :: Number, opacity :: Number }
evaluateTransform2DAt frame (AnimatedTransform2D t) =
  let
    (AnimatedPosition2D pos) = t.position
    (AnimatedScale2D scale) = t.scale
    (AnimatedRotation rot) = t.rotation
    (AnimatedAnchor2D anchor) = t.anchor
    (AnimatedOpacity op) = t.opacity
  in
    { posX: evaluateAt frame pos.x
    , posY: evaluateAt frame pos.y
    , scaleX: evaluateAt frame scale.x
    , scaleY: evaluateAt frame scale.y
    , rotation: evaluateAt frame rot.rotation
    , anchorX: evaluateAt frame anchor.x
    , anchorY: evaluateAt frame anchor.y
    , opacity: evaluateAt frame op.opacity
    }

-- | Evaluate 3D transform at frame.
evaluateTransform3DAt :: Frames -> AnimatedTransform3D
  -> { posX :: Number, posY :: Number, posZ :: Number
     , scaleX :: Number, scaleY :: Number, scaleZ :: Number
     , rotX :: Number, rotY :: Number, rotZ :: Number
     , orientX :: Number, orientY :: Number, orientZ :: Number
     , anchorX :: Number, anchorY :: Number, anchorZ :: Number
     , opacity :: Number }
evaluateTransform3DAt frame (AnimatedTransform3D t) =
  let
    (AnimatedPosition3D pos) = t.position
    (AnimatedScale3D scale) = t.scale
    (AnimatedRotation3D rot) = t.rotation
    (AnimatedAnchor3D anchor) = t.anchor
    (AnimatedOpacity op) = t.opacity
  in
    { posX: evaluateAt frame pos.x
    , posY: evaluateAt frame pos.y
    , posZ: evaluateAt frame pos.z
    , scaleX: evaluateAt frame scale.x
    , scaleY: evaluateAt frame scale.y
    , scaleZ: evaluateAt frame scale.z
    , rotX: evaluateAt frame rot.x
    , rotY: evaluateAt frame rot.y
    , rotZ: evaluateAt frame rot.z
    , orientX: evaluateAt frame rot.orientationX
    , orientY: evaluateAt frame rot.orientationY
    , orientZ: evaluateAt frame rot.orientationZ
    , anchorX: evaluateAt frame anchor.x
    , anchorY: evaluateAt frame anchor.y
    , anchorZ: evaluateAt frame anchor.z
    , opacity: evaluateAt frame op.opacity
    }
