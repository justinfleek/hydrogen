-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // animated-transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AnimatedTransform — Complete After Effects Transform Model.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides the COMPLETE transform model for motion graphics,
-- | matching After Effects' capabilities:
-- |
-- | - **Position** (X, Y, Z) — Object location, animatable along spline paths
-- | - **Rotation** (Z for 2D, X/Y/Z for 3D) — Object orientation with wrap
-- | - **Scale** (X, Y, Z) — Size as percentage, with flip via negative
-- | - **Anchor Point** — Transform origin relative to object bounds
-- | - **Opacity** — Visibility (0-100%)
-- |
-- | All properties are **animatable** with:
-- | - Keyframes at specific frame positions
-- | - Bezier tangent handles for easing
-- | - Spatial tangents for motion path curves (position only)
-- | - Speed graph control for temporal manipulation
-- | - Expressions for procedural animation
-- |
-- | ## Module Structure
-- |
-- | This is the leader module that re-exports from submodules:
-- |
-- | - **Core** — PropertyKeyframe, AnimatableValue, SpeedGraph, MotionPathMode
-- | - **Properties** — AnimatedPosition, Scale, Rotation, Anchor, Opacity
-- | - **Transform** — AnimatedTransform2D, AnimatedTransform3D
-- | - **Evaluation** — evaluateAt, evaluateTransform2DAt, evaluateTransform3DAt
-- | - **Keyframe** — addKeyframe, removeKeyframe, moveKeyframe, etc.
-- | - **Layer** — LayerDimensionality, RotationOrder, Parenting, NullObject
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.AnimatedTransform as AT
-- |
-- | -- Create default transform
-- | transform = AT.defaultAnimatedTransform2D
-- |
-- | -- Add keyframe to position X
-- | withKeyframe = AT.addPositionXKeyframe (frames 0.0) 100.0 transform
-- |
-- | -- Evaluate at frame 30
-- | posX = AT.evaluatePositionX (frames 30.0) withKeyframe
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Keyframe (Keyframe, KeyframeValue)
-- | - Schema.Motion.Easing (Easing, evaluate)
-- | - Schema.Motion.Interpolation (FullInterpolationType, BezierHandle)
-- | - Schema.Motion.Transform (Position2D, Position3D, Scale2D, etc.)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.AnimatedTransform
  ( -- * Re-exports from Core
    module Core
  
  -- * Re-exports from Properties
  , module Properties
  
  -- * Re-exports from Transform
  , module Transform
  
  -- * Re-exports from Evaluation
  , module Evaluation
  
  -- * Re-exports from Keyframe
  , module Keyframe
  
  -- * Re-exports from Layer
  , module Layer
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.AnimatedTransform.Core
  ( AnimatableValue(AnimatableValue)
  , PropertyKeyframe(PropertyKeyframe)
  , SpeedGraph(SpeedGraph)
  , SpeedGraphPoint(SpeedGraphPoint)
  , MotionPathMode
    ( MotionPathOff
    , MotionPathLinear
    , MotionPathBezier
    , MotionPathAutoOrient
    )
  , mkAnimatableValue
  , mkAnimatableValueStatic
  , isAnimated
  , hasExpression
  , getStaticValue
  , getKeyframes
  , mkPropertyKeyframe
  , keyframeFrame
  , keyframeValue
  , keyframeInterpolation
  , keyframeInHandle
  , keyframeOutHandle
  , keyframeSpatialIn
  , keyframeSpatialOut
  , defaultSpeedGraph
  , addSpeedGraphPoint
  , evaluateSpeedGraph
  ) as Core

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
  , defaultAnimatedPosition2D
  , defaultAnimatedPosition3D
  , separatePositionDimensions
  , combinePositionDimensions
  , getMotionPathMode
  , setMotionPathMode
  , enableAutoOrient
  , defaultAnimatedScale2D
  , defaultAnimatedScale3D
  , linkScaleDimensions
  , unlinkScaleDimensions
  , defaultAnimatedRotation
  , defaultAnimatedRotation3D
  , defaultAnimatedAnchor2D
  , defaultAnimatedAnchor3D
  , defaultAnimatedOpacity
  ) as Properties

import Hydrogen.Schema.Motion.AnimatedTransform.Transform
  ( AnimatedTransform2D(AnimatedTransform2D)
  , AnimatedTransform3D(AnimatedTransform3D)
  , defaultAnimatedTransform2D
  , identityAnimatedTransform2D
  , defaultAnimatedTransform3D
  , identityAnimatedTransform3D
  ) as Transform

import Hydrogen.Schema.Motion.AnimatedTransform.Evaluation
  ( evaluateAt
  , evaluateKeyframes
  , applyInterpolation
  , evaluateTransform2DAt
  , evaluateTransform3DAt
  ) as Evaluation

import Hydrogen.Schema.Motion.AnimatedTransform.Keyframe
  ( addKeyframe
  , removeKeyframe
  , moveKeyframe
  , updateKeyframeValue
  , updateKeyframeInterpolation
  ) as Keyframe

import Hydrogen.Schema.Motion.AnimatedTransform.Layer
  ( LayerDimensionality(Layer2D, Layer3D)
  , is3DLayer
  , enable3DLayer
  , disable3DLayer
  , RotationOrder
    ( RotationXYZ
    , RotationXZY
    , RotationYXZ
    , RotationYZX
    , RotationZXY
    , RotationZYX
    )
  , allRotationOrders
  , rotationOrderToString
  , defaultRotationOrder
  , LayerParent(NoParent, ParentLayer, ParentNull)
  , ParentLink(ParentLink)
  , mkParentLink
  , parentToLayer
  , parentToNull
  , clearParent
  , isParented
  , getParentId
  , inheritPosition
  , inheritScale
  , inheritRotation
  , LayerTransformState(LayerTransformState)
  , defaultLayerTransformState
  , setLayerParent
  , getEffectiveTransform2D
  , getEffectiveTransform3D
  , NullObject(NullObject)
  , mkNullObject
  , nullObjectTransform
  ) as Layer
