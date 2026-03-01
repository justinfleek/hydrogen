-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // framestate // time
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Time — Temporal State for Animation Frames
-- |
-- | ## Purpose
-- |
-- | Tracks the temporal state needed for a render frame:
-- |
-- | - **current**: Current timestamp (ms since start)
-- | - **delta**: Time elapsed since last frame (for physics/animation)
-- | - **frame**: Frame counter for debugging and deterministic replay
-- | - **start**: Initial timestamp for elapsed-time calculations
-- | - **targetFPS**: Desired frame rate for budget calculations
-- |
-- | ## Why External Time State?
-- |
-- | At billion-agent scale, scattered timers create chaos:
-- |
-- | - Each agent's own timers → clock drift across swarm
-- | - No global time reference → coordination failures
-- | - Non-deterministic timing → unreplayable bugs
-- |
-- | With centralized TimeState:
-- |
-- | - One clock source → frame-perfect synchronization
-- | - All agents see same timestamp → deterministic behavior
-- | - Full serialization → replayable debugging

module Hydrogen.GPU.FrameState.Time
  ( -- * Time State
    TimeState
  , mkTimeState
  , advanceTime
  
  -- * Accessors
  , deltaMs
  , elapsedMs
  , frameNumber
  , fps
  
  -- * Re-export core types
  , module Types
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (/)
  , (>)
  )

import Hydrogen.GPU.FrameState.Types (FrameTime, FrameNumber) as Types
import Hydrogen.GPU.FrameState.Types (FrameTime, FrameNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // time state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal state for the current frame
-- |
-- | All times are in milliseconds. The delta is computed automatically
-- | by `advanceTime` as the difference between new and previous timestamps.
type TimeState =
  { current :: FrameTime       -- Current timestamp (ms since start)
  , delta :: FrameTime         -- Time since last frame (ms)
  , frame :: FrameNumber       -- Frame counter
  , start :: FrameTime         -- Timestamp when app started
  , targetFPS :: Number        -- Target frames per second
  }

-- | Create initial time state
-- |
-- | Initializes with zero delta (no previous frame) and frame 0.
-- | The targetFPS is used for frame budget calculations, not enforcement.
mkTimeState :: FrameTime -> Number -> TimeState
mkTimeState startTime targetFrameRate =
  { current: startTime
  , delta: 0.0
  , frame: 0
  , start: startTime
  , targetFPS: targetFrameRate
  }

-- | Advance time to a new timestamp
-- |
-- | Computes delta automatically and increments frame counter.
-- | This is the ONLY way to update TimeState — ensures monotonicity.
advanceTime :: FrameTime -> TimeState -> TimeState
advanceTime newTime state =
  { current: newTime
  , delta: newTime - state.current
  , frame: state.frame + 1
  , start: state.start
  , targetFPS: state.targetFPS
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get delta time in milliseconds
-- |
-- | Time elapsed since the previous frame. Use for physics/animation:
-- | `newPosition = oldPosition + velocity * deltaMs state`
deltaMs :: TimeState -> FrameTime
deltaMs state = state.delta

-- | Get elapsed time since start in milliseconds
-- |
-- | Total time since the app started. Useful for progress bars,
-- | session duration displays, and time-based triggers.
elapsedMs :: TimeState -> FrameTime
elapsedMs state = state.current - state.start

-- | Get current frame number
-- |
-- | Monotonically increasing counter starting at 0.
-- | Useful for debugging, replay, and frame-based effects.
frameNumber :: TimeState -> FrameNumber
frameNumber state = state.frame

-- | Calculate actual FPS from delta time
-- |
-- | Returns 0.0 if delta is zero (first frame or paused).
-- | This is the measured FPS, not the target FPS.
fps :: TimeState -> Number
fps state = if state.delta > 0.0 then 1000.0 / state.delta else 0.0
