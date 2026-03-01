-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // pathmotion // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMotion Types — Core type definitions for path-based animation.
-- |
-- | ## Exports
-- |
-- | - `PathSource` — Unified interface for different spline/path types
-- | - `OrientMode` — How to orient objects along the path
-- | - `MotionSample` — Complete sample at a point in time
-- | - `MotionPath` — Full motion path configuration
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D)
-- | - Schema.Geometry.Angle (Degrees)
-- | - Schema.Geometry.Spline (CatmullRomSpline, BSpline)
-- | - Schema.Motion.Easing (Easing)

module Hydrogen.Schema.Motion.PathMotion.Types
  ( -- * Path Source
    PathSource(..)
  
  -- * Orient Mode
  , OrientMode(..)
  
  -- * Motion Sample
  , MotionSample(..)
  , unwrapMotionSample
  
  -- * Motion Path
  , MotionPath(..)
  , unwrapMotionPath
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Array (length)

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D)
import Hydrogen.Schema.Geometry.Angle (Degrees)
import Hydrogen.Schema.Geometry.Spline (CatmullRomSpline, BSpline)
import Hydrogen.Schema.Motion.Easing (Easing)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // path source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source path for motion.
-- |
-- | Wraps different spline types into a unified interface.
data PathSource
  = CatmullRomSource CatmullRomSpline
  | BSplineSource BSpline
  | PointArraySource (Array Point2D)  -- Linear interpolation between points

derive instance eqPathSource :: Eq PathSource

instance showPathSource :: Show PathSource where
  show (CatmullRomSource _) = "CatmullRomSource"
  show (BSplineSource _) = "BSplineSource"
  show (PointArraySource pts) = "(PointArraySource " <> show (length pts) <> " points)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orient mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How to orient the object along the path.
data OrientMode
  = NoOrient           -- Keep original rotation
  | OrientToPath       -- Rotate to face movement direction
  | OrientToPathFlipped -- Rotate 180° from movement direction
  | OrientPerpendicular -- Rotate perpendicular to path
  | OrientCustomOffset Degrees  -- Rotate to path + custom offset

derive instance eqOrientMode :: Eq OrientMode

instance showOrientMode :: Show OrientMode where
  show NoOrient = "NoOrient"
  show OrientToPath = "OrientToPath"
  show OrientToPathFlipped = "OrientToPathFlipped"
  show OrientPerpendicular = "OrientPerpendicular"
  show (OrientCustomOffset d) = "(OrientCustomOffset " <> show d <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // motion sample
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete motion sample at a point in time.
newtype MotionSample = MotionSample
  { position :: Point2D
  , rotation :: Degrees
  , tangent :: Vector2D
  , progress :: Number    -- 0-1 normalized progress
  , arcLength :: Number   -- Distance along path
  , speed :: Number       -- Current speed (derivative of position)
  , bank :: Degrees       -- Banking angle for turns
  }

derive instance eqMotionSample :: Eq MotionSample

instance showMotionSample :: Show MotionSample where
  show (MotionSample s) = "(MotionSample pos:" <> show s.position 
    <> " rot:" <> show s.rotation <> " progress:" <> show s.progress <> ")"

-- | Unwrap MotionSample to access record fields.
unwrapMotionSample :: MotionSample -> 
  { position :: Point2D
  , rotation :: Degrees
  , tangent :: Vector2D
  , progress :: Number
  , arcLength :: Number
  , speed :: Number
  , bank :: Degrees
  }
unwrapMotionSample (MotionSample s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // motion path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion path configuration.
-- |
-- | Combines path geometry with timing and orientation settings.
newtype MotionPath = MotionPath
  { source :: PathSource
  , durationFrames :: Number      -- Total duration in frames
  , easing :: Easing              -- How progress maps to path position
  , orientMode :: OrientMode      -- How to rotate along path
  , bankAngle :: Degrees          -- Maximum banking angle for turns
  , bankSmoothing :: Number       -- 0-1, how much to smooth banking
  , loop :: Boolean               -- Whether to loop animation
  , pingPong :: Boolean           -- Whether to reverse at end
  , startOffset :: Number         -- 0-1, where to start on path
  , endOffset :: Number           -- 0-1, where to end on path
  , startFrame :: Number          -- Frame where animation begins
  }

derive instance eqMotionPath :: Eq MotionPath

instance showMotionPath :: Show MotionPath where
  show (MotionPath mp) = "(MotionPath dur:" <> show mp.durationFrames 
    <> " orient:" <> show mp.orientMode <> ")"

-- | Unwrap MotionPath to access record fields.
unwrapMotionPath :: MotionPath ->
  { source :: PathSource
  , durationFrames :: Number
  , easing :: Easing
  , orientMode :: OrientMode
  , bankAngle :: Degrees
  , bankSmoothing :: Number
  , loop :: Boolean
  , pingPong :: Boolean
  , startOffset :: Number
  , endOffset :: Number
  , startFrame :: Number
  }
unwrapMotionPath (MotionPath mp) = mp
