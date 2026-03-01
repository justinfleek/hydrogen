-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // motion // path-motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMotion — Animate objects along spline paths.
-- |
-- | ## Design Philosophy
-- |
-- | PathMotion provides cinema-grade motion path animation like After Effects,
-- | Cinema 4D, and Illustrator. Objects follow paths with:
-- |
-- | - **Arc-length parameterization**: Uniform speed along path
-- | - **Easing integration**: Apply easing curves to path progress
-- | - **Orient to path**: Auto-rotate object to face movement direction
-- | - **Banking**: Tilt into turns like aircraft
-- | - **Time remapping**: Variable speed along path
-- |
-- | ## Motion Path Workflow
-- |
-- | 1. Create a path (Spline, NURBS, or Bezier)
-- | 2. Wrap in MotionPath with timing parameters
-- | 3. Evaluate at any frame to get position, rotation, scale
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.PathMotion as PM
-- | import Hydrogen.Schema.Geometry.Spline as Spline
-- |
-- | -- Create path from points
-- | path = Spline.catmullRomSpline points
-- |
-- | -- Create motion path (2 second duration at 30fps = 60 frames)
-- | motion = PM.motionPath path (PM.Duration 60) PM.easeInOut
-- |
-- | -- Get position at frame 30 (halfway)
-- | pos = PM.positionAtFrame 30 motion
-- |
-- | -- Get full transform (position + rotation)
-- | transform = PM.transformAtFrame 30 motion
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `PathMotion.Types` — Core type definitions
-- | - `PathMotion.Core` — Construction, configuration, accessors
-- | - `PathMotion.Evaluation` — Position, tangent, rotation, sampling
-- | - `PathMotion.Internal` — Helper functions (not re-exported)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Spline (CatmullRomSpline, BSpline)
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D for tangents)
-- | - Schema.Geometry.Angle (Degrees for rotation)
-- | - Schema.Motion.Easing (easing curves)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.PathMotion
  ( module Types
  , module Core
  , module Evaluation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.PathMotion.Types as Types
import Hydrogen.Schema.Motion.PathMotion.Core as Core
import Hydrogen.Schema.Motion.PathMotion.Evaluation as Evaluation
