-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // runtime // animate // spring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spring Animation
-- |
-- | Physics-based spring animations using damped harmonic oscillator model.
-- | Springs provide natural, interruptible motion that responds to velocity.
-- |
-- | Uses "pending start" pattern where startTime of -1.0 means "capture
-- | timestamp on first tick" - this allows spring animations to be created
-- | without knowing the current time.
module Hydrogen.Runtime.Animate.Spring
  ( -- * Spring State
    SpringState
  , springState
  , springTo
  , tickSpring
  
  -- * Value Access
  , springValue
  , springComplete
  , resetSpring
  ) where

import Prelude
  ( negate
  , ($)
  , (<)
  , (+)
  , (-)
  , (/)
  )

import Hydrogen.Motion.Spring (SpringConfig)
import Hydrogen.Motion.Spring as Spring

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // spring // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring animation state.
-- |
-- | Contains everything needed to evaluate a spring at any timestamp.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type SpringState =
  { config :: SpringConfig
  , from :: Number
  , to :: Number
  , startTime :: Number  -- -1.0 means "pending start"
  , currentValue :: Number
  , complete :: Boolean
  }

-- | Create initial spring state.
springState :: SpringConfig -> Number -> SpringState
springState config initialValue =
  { config
  , from: initialValue
  , to: initialValue
  , startTime: 0.0
  , currentValue: initialValue
  , complete: true  -- No animation in progress
  }

-- | Start spring animation toward a target value.
-- |
-- | Call this when you want to animate to a new value. The spring will
-- | start from its current position. Uses -1.0 as sentinel to indicate
-- | "capture timestamp on first tick".
springTo :: SpringState -> Number -> SpringState
springTo state target =
  { config: state.config
  , from: state.currentValue
  , to: target
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance spring animation to a new timestamp.
-- |
-- | Call this on each animation frame to update the current value.
-- | If startTime is -1.0, this tick captures the start time.
tickSpring :: Number -> SpringState -> SpringState
tickSpring timestamp state =
  case state.complete of
    true -> state
    false ->
      -- Handle pending start
      let
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp  -- First tick captures start time
          false -> state.startTime
        
        -- Time since animation started (in seconds)
        elapsed = (timestamp - actualStartTime) / 1000.0
        
        -- Evaluate spring physics
        newValue = Spring.springValue state.config state.from state.to elapsed
        
        -- Check if spring is at rest
        atRest = Spring.isAtRest state.config state.from state.to elapsed
      in
        state 
          { startTime = actualStartTime
          , currentValue = newValue
          , complete = atRest
          }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // spring // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current value from a spring animation.
springValue :: SpringState -> Number
springValue s = s.currentValue

-- | Check if spring animation is complete.
springComplete :: SpringState -> Boolean
springComplete s = s.complete

-- | Reset a spring to a specific value (stops animation).
resetSpring :: Number -> SpringState -> SpringState
resetSpring v s = s { currentValue = v, from = v, to = v, complete = true }
