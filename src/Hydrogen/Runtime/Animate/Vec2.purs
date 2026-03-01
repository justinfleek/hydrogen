-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // runtime // animate // vec2
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vec2 Animation
-- |
-- | Two-dimensional vector animations for position, size, and other 2D values.
-- | Animates both components together with synchronized timing and easing.
-- |
-- | Uses "pending start" pattern where startTime of -1.0 means "capture
-- | timestamp on first tick" - this allows animations to be created
-- | without knowing the current time.
module Hydrogen.Runtime.Animate.Vec2
  ( -- * Vec2 Type
    Vec2
  
  -- * Vec2 State
  , Vec2State
  , vec2State
  , vec2To
  , tickVec2
  
  -- * Value Access
  , vec2Value
  , vec2Complete
  ) where

import Prelude
  ( negate
  , ($)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  )

import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vec2 // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D vector type for position, size, etc.
type Vec2 = { x :: Number, y :: Number }

-- | Vec2 tween animation state.
-- |
-- | Animates two values together with the same timing.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type Vec2State =
  { easing :: Easing
  , from :: Vec2
  , to :: Vec2
  , duration :: Number
  , startTime :: Number  -- -1.0 means "pending start"
  , currentValue :: Vec2
  , complete :: Boolean
  }

-- | Create initial Vec2 state.
vec2State :: Vec2 -> Vec2State
vec2State initial =
  { easing: Easing.linear
  , from: initial
  , to: initial
  , duration: 0.0
  , startTime: 0.0
  , currentValue: initial
  , complete: true
  }

-- | Start Vec2 animation toward a target.
-- | Uses -1.0 as sentinel to indicate "capture timestamp on first tick".
vec2To :: Vec2State -> Vec2 -> Number -> Easing -> Vec2State
vec2To state target duration easing =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance Vec2 animation to a new timestamp.
-- | If startTime is -1.0, this tick captures the start time.
tickVec2 :: Number -> Vec2State -> Vec2State
tickVec2 timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        -- Handle pending start
        actualStartTime = case state.startTime < 0.0 of
          true -> timestamp
          false -> state.startTime
        
        elapsed = timestamp - actualStartTime
        progress = elapsed / state.duration
      in
        case progress >= 1.0 of
          true -> state
            { startTime = actualStartTime
            , currentValue = state.to
            , complete = true
            }
          false ->
            let
              t = Easing.evaluate state.easing progress
              newX = state.from.x + (state.to.x - state.from.x) * t
              newY = state.from.y + (state.to.y - state.from.y) * t
            in
              state 
                { startTime = actualStartTime
                , currentValue = { x: newX, y: newY } 
                }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // vec2 // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current Vec2 value.
vec2Value :: Vec2State -> Vec2
vec2Value s = s.currentValue

-- | Check if Vec2 animation is complete.
vec2Complete :: Vec2State -> Boolean
vec2Complete s = s.complete
