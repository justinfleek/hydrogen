-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // distributed // time-authority // frame-schedule
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deterministic frame scheduling for synchronized animation.
-- |
-- | ## Purpose
-- |
-- | When multiple agents render the same animation, they must agree on:
-- |
-- | - Which frame corresponds to which wall-clock time
-- | - Frame boundaries for consistent keyframe interpolation
-- | - Frame identity for caching and deduplication
-- |
-- | ## Determinism
-- |
-- | Given a shared schedule (epoch + fps), any agent can compute:
-- |
-- | - frameToTime: What wall-clock time does frame N occur?
-- | - timeToFrame: What frame number is wall-clock T in?
-- |
-- | Two agents with synchronized clocks will agree on current frame.

module Hydrogen.Distributed.TimeAuthority.FrameSchedule
  ( -- * Core Type Aliases
    FrameTime
  , FrameNumber
  
  -- * Frame Schedule
  , FrameSchedule
  , mkFrameSchedule
  , frameDuration
  , framesPerSecond
  , frameToTime
  , timeToFrame
  , nextFrameTime
  , framesSince
  
  -- * Deterministic Frame Identity
  , FrameId
  , mkFrameId
  , frameIdFromTime
  , compareFrameIds
  , sameFrame
  
  -- * Predicates
  , isValidSchedule
  , safeTimeToFrame
  ) where

import Prelude
  ( class Eq
  , Ordering(EQ)
  , compare
  , (==)
  , (>)
  , (-)
  , (+)
  , (/)
  , (*)
  , (&&)
  )

import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Distributed.TimeAuthority.Lamport (WallClock)

-- | Time in milliseconds (for frame timing)
type FrameTime = Number

-- | Frame number (monotonically increasing integer)
type FrameNumber = Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // frame scheduling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame schedule for deterministic timing
-- |
-- | Given a global start time and frame rate, any agent can compute
-- | the exact time of any frame number.
type FrameSchedule =
  { globalStart :: WallClock   -- Epoch for frame counting
  , fps :: Number              -- Target frames per second
  , frameDurationMs :: Number  -- 1000 / fps
  }

-- | Create frame schedule
mkFrameSchedule :: WallClock -> Number -> FrameSchedule
mkFrameSchedule globalStart fps =
  { globalStart
  , fps
  , frameDurationMs: 1000.0 / fps
  }

-- | Get frame duration in milliseconds
frameDuration :: FrameSchedule -> FrameTime
frameDuration sched = sched.frameDurationMs

-- | Get frames per second
framesPerSecond :: FrameSchedule -> Number
framesPerSecond sched = sched.fps

-- | Compute wall clock time for a frame number
frameToTime :: FrameSchedule -> FrameNumber -> WallClock
frameToTime sched frame = 
  sched.globalStart + (toNumber frame * sched.frameDurationMs)

-- | Compute frame number from wall clock time
timeToFrame :: FrameSchedule -> WallClock -> FrameNumber
timeToFrame sched time =
  floor ((time - sched.globalStart) / sched.frameDurationMs)

-- | Get time of next frame after given time
nextFrameTime :: FrameSchedule -> WallClock -> WallClock
nextFrameTime sched currentTime =
  let currentFrame = timeToFrame sched currentTime
  in frameToTime sched (currentFrame + 1)

-- | Count frames elapsed since a given time
framesSince :: FrameSchedule -> WallClock -> WallClock -> Int
framesSince sched startTime currentTime =
  timeToFrame sched currentTime - timeToFrame sched startTime

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // deterministic frame identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deterministic frame identifier
-- |
-- | Combines frame number with schedule identity for globally unique frame IDs.
-- | Two agents with the same schedule will generate identical frame IDs.
type FrameId =
  { frameNumber :: FrameNumber
  , scheduleEpoch :: WallClock
  , fps :: Number
  }

-- | Create frame ID
mkFrameId :: FrameNumber -> FrameSchedule -> FrameId
mkFrameId frameNumber sched =
  { frameNumber
  , scheduleEpoch: sched.globalStart
  , fps: sched.fps
  }

-- | Create frame ID from wall clock time
frameIdFromTime :: WallClock -> FrameSchedule -> FrameId
frameIdFromTime time sched = mkFrameId (timeToFrame sched time) sched

-- | Compare frame IDs
compareFrameIds :: FrameId -> FrameId -> Ordering
compareFrameIds a b =
  case compare a.scheduleEpoch b.scheduleEpoch of
    EQ -> case compare a.fps b.fps of
      EQ -> compare a.frameNumber b.frameNumber
      other -> other
    other -> other

-- | Check if two frame IDs reference the same frame
sameFrame :: FrameId -> FrameId -> Boolean
sameFrame a b =
  a.frameNumber == b.frameNumber &&
  a.scheduleEpoch == b.scheduleEpoch &&
  a.fps == b.fps

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if frame schedule is valid (positive fps)
isValidSchedule :: FrameSchedule -> Boolean
isValidSchedule sched = sched.fps > 0.0 && sched.frameDurationMs > 0.0

-- | Get frame number if schedule is valid
safeTimeToFrame :: FrameSchedule -> WallClock -> Maybe FrameNumber
safeTimeToFrame sched time =
  if isValidSchedule sched
    then Just (timeToFrame sched time)
    else Nothing
