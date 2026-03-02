-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // spatial-keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spatial Keyframes — Motion path keyframes with bezier handles in 2D/3D space.
-- |
-- | ## Industry Standard
-- |
-- | In professional motion graphics software, position keyframes have TWO sets of bezier handles:
-- |
-- | 1. **Spatial Handles**: Control the SHAPE of the motion path
-- |    - Visible in the composition viewport as path tangents
-- |    - Define the curve the object travels through space
-- |
-- | 2. **Temporal Handles**: Control the SPEED along the path
-- |    - Visible in the Graph Editor (speed graph / value graph)
-- |    - Define how fast the object moves between keyframes
-- |
-- | ## Architecture
-- |
-- | ```
-- |                    +-------------------------------------+
-- |                    |         SPATIAL DOMAIN              |
-- |                    |   (Composition Viewport)            |
-- |                    |                                     |
-- |       inSpatial -->*----------------*<-- outSpatial      |
-- |                   KF1              KF2                   |
-- |                    |   motion path curve                 |
-- |                    +-------------------------------------+
-- |
-- |                    +-------------------------------------+
-- |                    |         TEMPORAL DOMAIN             |
-- |                    |   (Graph Editor)                    |
-- |                    |                                     |
-- |                    |         ,-------,                   |
-- |      inTemporal -->*--------'       '----*<-- outTemporal|
-- |                   KF1                   KF2              |
-- |                    |   speed curve (ease in/out)         |
-- |                    +-------------------------------------+
-- | ```
-- |
-- | ## Module Structure
-- |
-- | - **Handle**: SpatialHandle2D/3D, TemporalHandle
-- | - **Types**: KeyframeFlags, SpatialInterpolation, TemporalInterpolation, DimensionMode
-- | - **Keyframe**: SpatialKeyframe2D/3D types and operations
-- | - **Bezier**: Cubic bezier math and arc length calculation
-- | - **Path**: MotionPath2D/3D and SpeedGraph

module Hydrogen.Schema.Motion.SpatialKeyframe
  ( -- * Re-exports from Handle
    module Hydrogen.Schema.Motion.SpatialKeyframe.Handle
    
  -- * Re-exports from Types
  , module Hydrogen.Schema.Motion.SpatialKeyframe.Types
  
  -- * Re-exports from Keyframe
  , module Hydrogen.Schema.Motion.SpatialKeyframe.Keyframe
  
  -- * Re-exports from Bezier
  , module Hydrogen.Schema.Motion.SpatialKeyframe.Bezier
  
  -- * Re-exports from Path
  , module Hydrogen.Schema.Motion.SpatialKeyframe.Path
  ) where

import Hydrogen.Schema.Motion.SpatialKeyframe.Handle
  ( SpatialHandle2D
  , spatialHandle2D
  , spatialHandle2DZero
  , unwrapSpatialHandle2D
  , SpatialHandle3D
  , spatialHandle3D
  , spatialHandle3DZero
  , unwrapSpatialHandle3D
  , TemporalHandle
  , temporalHandle
  , temporalHandleLinear
  , temporalHandleEaseIn
  , temporalHandleEaseOut
  , temporalHandleEaseInOut
  , temporalHandleHold
  , unwrapTemporalHandle
  )

import Hydrogen.Schema.Motion.SpatialKeyframe.Types
  ( KeyframeFlags
  , defaultKeyframeFlags
  , setRoving
  , setLockToTime
  , setContinuousBezier
  , setAutoBezier
  , SpatialInterpolation(SILinear, SIBezier, SIAuto)
  , spatialInterpolationToString
  , spatialInterpolationFromString
  , TemporalInterpolation(TILinear, TIBezier, TIHold, TIAuto)
  , temporalInterpolationToString
  , temporalInterpolationFromString
  , DimensionMode(DMUnified, DMSeparated)
  , dimensionModeToString
  , dimensionModeFromString
  )

import Hydrogen.Schema.Motion.SpatialKeyframe.Keyframe
  ( SpatialKeyframe2D
  , spatialKeyframe2D
  , spatialKeyframe2DLinear
  , spatialKeyframe2DWithHandles
  , SpatialKeyframe3D
  , spatialKeyframe3D
  , spatialKeyframe3DLinear
  , spatialKeyframe3DWithHandles
  , keyframePosition2D
  , keyframePosition3D
  , keyframeFrame
  , keyframeSpatialIn2D
  , keyframeSpatialOut2D
  , keyframeSpatialIn3D
  , keyframeSpatialOut3D
  , keyframeTemporalIn
  , keyframeTemporalOut
  , keyframeFlags
  , setPosition2D
  , setPosition3D
  , setSpatialHandles2D
  , setSpatialHandles3D
  , setTemporalHandles
  , convertToRoving
  , convertToLinear
  , convertToBezier
  , convertToHold
  , convertToAuto
  )

import Hydrogen.Schema.Motion.SpatialKeyframe.Bezier
  ( cubicBezier
  , cubicBezierDerivative
  , evalBezier2D
  , evalBezier3D
  , applyTemporalEasing
  , solveForT
  , bezierArcLength2D
  , bezierArcLength3D
  , bezierSpeed2D
  , bezierSpeed3D
  )

import Hydrogen.Schema.Motion.SpatialKeyframe.Path
  ( MotionPath2D
  , motionPath2D
  , motionPath2DFromKeyframes
  , evaluateMotionPath2D
  , motionPathLength2D
  , MotionPath3D
  , motionPath3D
  , motionPath3DFromKeyframes
  , evaluateMotionPath3D
  , motionPathLength3D
  , SpeedGraph
  , speedGraph
  , speedAt
  , averageSpeed
  , maxSpeed
  , minSpeed
  )
