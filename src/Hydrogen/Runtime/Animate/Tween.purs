-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // runtime // animate // tween
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tween Animation
-- |
-- | Duration-based animations with easing functions. Tweens interpolate
-- | between values over a fixed time period using configurable easing.
-- |
-- | Uses "pending start" pattern where startTime of -1.0 means "capture
-- | timestamp on first tick" - this allows tween animations to be created
-- | without knowing the current time.
module Hydrogen.Runtime.Animate.Tween
  ( -- * Tween State
    TweenState
  , tweenState
  , tweenTo
  , tickTween
  
  -- * Value Access
  , tweenValue
  , tweenComplete
  , resetTween
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
--                                                         // tween // animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tween (duration-based) animation state.
-- | Uses "pending start" pattern - startTime of -1.0 means "start on first tick".
type TweenState =
  { easing :: Easing
  , from :: Number
  , to :: Number
  , duration :: Number     -- milliseconds
  , startTime :: Number    -- -1.0 means "pending start"
  , currentValue :: Number
  , complete :: Boolean
  }

-- | Create initial tween state.
tweenState :: Number -> TweenState
tweenState initialValue =
  { easing: Easing.linear
  , from: initialValue
  , to: initialValue
  , duration: 0.0
  , startTime: 0.0
  , currentValue: initialValue
  , complete: true
  }

-- | Start tween animation toward a target value.
-- | Uses -1.0 as sentinel to indicate "capture timestamp on first tick".
tweenTo :: TweenState -> Number -> Number -> Easing -> TweenState
tweenTo state target duration easing =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: -1.0  -- Sentinel: start on first tick
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance tween animation to a new timestamp.
-- | If startTime is -1.0, this tick captures the start time.
tickTween :: Number -> TweenState -> TweenState
tickTween timestamp state =
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
              easedProgress = Easing.evaluate state.easing progress
              newValue = state.from + (state.to - state.from) * easedProgress
            in
              state 
                { startTime = actualStartTime
                , currentValue = newValue 
                }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // tween // value // access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current value from a tween animation.
tweenValue :: TweenState -> Number
tweenValue s = s.currentValue

-- | Check if tween animation is complete.
tweenComplete :: TweenState -> Boolean
tweenComplete s = s.complete

-- | Reset a tween to a specific value (stops animation).
resetTween :: Number -> TweenState -> TweenState
resetTween v s = s { currentValue = v, from = v, to = v, complete = true }
