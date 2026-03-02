-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // spatial-keyframe // handle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Handles — Spatial and temporal control points for motion curves.
-- |
-- | ## Architecture
-- |
-- | - **SpatialHandle2D/3D**: Control motion path SHAPE in composition space
-- | - **TemporalHandle**: Control motion SPEED in graph editor
-- |
-- | These correspond to motion graphics dual-handle system where position
-- | keyframes have both spatial tangents (path shape) and temporal tangents
-- | (easing/speed curve).

module Hydrogen.Schema.Motion.SpatialKeyframe.Handle
  ( -- * Spatial Handle (2D)
    SpatialHandle2D
  , spatialHandle2D
  , spatialHandle2DZero
  , unwrapSpatialHandle2D
  
  -- * Spatial Handle (3D)
  , SpatialHandle3D
  , spatialHandle3D
  , spatialHandle3DZero
  , unwrapSpatialHandle3D
  
  -- * Temporal Handle
  , TemporalHandle
  , temporalHandle
  , temporalHandleLinear
  , temporalHandleEaseIn
  , temporalHandleEaseOut
  , temporalHandleEaseInOut
  , temporalHandleHold
  , unwrapTemporalHandle
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , show
  )

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // spatial // handle 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial bezier handle in 2D space.
-- |
-- | Defines the tangent direction and magnitude for motion path curves.
-- | Coordinates are relative to the keyframe position.
-- |
-- | ```
-- |           handle (dx, dy)
-- |              *
-- |             /
-- |            /
-- |           *---------->  keyframe position
-- | ```
newtype SpatialHandle2D = SpatialHandle2D
  { dx :: Number  -- ^ X offset from keyframe
  , dy :: Number  -- ^ Y offset from keyframe
  }

derive instance eqSpatialHandle2D :: Eq SpatialHandle2D
derive instance ordSpatialHandle2D :: Ord SpatialHandle2D

instance showSpatialHandle2D :: Show SpatialHandle2D where
  show (SpatialHandle2D h) = "Spatial2D(" <> show h.dx <> ", " <> show h.dy <> ")"

-- | Create a 2D spatial handle.
spatialHandle2D :: Number -> Number -> SpatialHandle2D
spatialHandle2D dx dy = SpatialHandle2D { dx, dy }

-- | Zero-length handle (linear interpolation).
spatialHandle2DZero :: SpatialHandle2D
spatialHandle2DZero = SpatialHandle2D { dx: 0.0, dy: 0.0 }

-- | Extract handle values.
unwrapSpatialHandle2D :: SpatialHandle2D -> { dx :: Number, dy :: Number }
unwrapSpatialHandle2D (SpatialHandle2D h) = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // spatial // handle 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial bezier handle in 3D space.
newtype SpatialHandle3D = SpatialHandle3D
  { dx :: Number
  , dy :: Number
  , dz :: Number
  }

derive instance eqSpatialHandle3D :: Eq SpatialHandle3D
derive instance ordSpatialHandle3D :: Ord SpatialHandle3D

instance showSpatialHandle3D :: Show SpatialHandle3D where
  show (SpatialHandle3D h) = 
    "Spatial3D(" <> show h.dx <> ", " <> show h.dy <> ", " <> show h.dz <> ")"

-- | Create a 3D spatial handle.
spatialHandle3D :: Number -> Number -> Number -> SpatialHandle3D
spatialHandle3D dx dy dz = SpatialHandle3D { dx, dy, dz }

-- | Zero-length handle (linear interpolation).
spatialHandle3DZero :: SpatialHandle3D
spatialHandle3DZero = SpatialHandle3D { dx: 0.0, dy: 0.0, dz: 0.0 }

-- | Extract handle values.
unwrapSpatialHandle3D :: SpatialHandle3D -> { dx :: Number, dy :: Number, dz :: Number }
unwrapSpatialHandle3D (SpatialHandle3D h) = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // temporal // handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal bezier handle for speed/easing control.
-- |
-- | Defines the easing curve in the graph editor.
-- | - `influence`: How far the handle extends (0-100%)
-- | - `speed`: Velocity at the keyframe (units/frame)
-- |
-- | In normalized form (for cubic bezier):
-- | - x: time influence (0.0 to 1.0)
-- | - y: value influence (can exceed 0-1 for overshoot)
newtype TemporalHandle = TemporalHandle
  { influence :: Number  -- ^ Influence percentage (0-100)
  , speed :: Number      -- ^ Speed at keyframe (units/frame)
  }

derive instance eqTemporalHandle :: Eq TemporalHandle
derive instance ordTemporalHandle :: Ord TemporalHandle

instance showTemporalHandle :: Show TemporalHandle where
  show (TemporalHandle h) = 
    "Temporal(inf:" <> show h.influence <> "%, spd:" <> show h.speed <> ")"

-- | Create a temporal handle.
temporalHandle :: Number -> Number -> TemporalHandle
temporalHandle inf spd = TemporalHandle 
  { influence: clampNumber 0.0 100.0 inf
  , speed: spd
  }

-- | Linear temporal handle (constant speed).
temporalHandleLinear :: TemporalHandle
temporalHandleLinear = TemporalHandle { influence: 0.0, speed: 0.0 }

-- | Ease-in preset (slow start).
temporalHandleEaseIn :: TemporalHandle
temporalHandleEaseIn = TemporalHandle { influence: 33.0, speed: 0.0 }

-- | Ease-out preset (slow end).
temporalHandleEaseOut :: TemporalHandle
temporalHandleEaseOut = TemporalHandle { influence: 33.0, speed: 0.0 }

-- | Ease-in-out preset (slow start and end).
temporalHandleEaseInOut :: TemporalHandle
temporalHandleEaseInOut = TemporalHandle { influence: 50.0, speed: 0.0 }

-- | Hold (instant change, no interpolation).
temporalHandleHold :: TemporalHandle
temporalHandleHold = TemporalHandle { influence: 0.0, speed: 0.0 }

-- | Extract handle values.
unwrapTemporalHandle :: TemporalHandle -> { influence :: Number, speed :: Number }
unwrapTemporalHandle (TemporalHandle h) = h
