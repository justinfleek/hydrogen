-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // runtime // animate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation State Helpers
-- |
-- | Ergonomic utilities for managing animated values in Hydrogen apps.
-- | Works with the Cmd-based tick pattern where animation state lives
-- | in app state and ticks are scheduled via `animationFrame`.
-- |
-- | ## Spring Animation Pattern
-- |
-- | ```purescript
-- | import Hydrogen.Runtime.Animate as Animate
-- | import Hydrogen.Runtime.Cmd (animationFrame, noCmd, transition)
-- |
-- | type State = { position :: Animate.SpringState }
-- |
-- | init = { position: Animate.springState springDefault 0.0 }
-- |
-- | update = case _ of
-- |   MoveTo target -> 
-- |     transition state 
-- |       { position = Animate.springTo state.position target }
-- |       (animationFrame Tick)
-- |   
-- |   Tick timestamp ->
-- |     let pos = Animate.tickSpring timestamp state.position
-- |     in case Animate.isComplete pos of
-- |       true -> noCmd state { position = pos }
-- |       false -> transition state { position = pos } (animationFrame Tick)
-- |
-- | view state =
-- |   E.div_ 
-- |     [ E.style "transform" (translateX (Animate.value state.position)) ]
-- |     []
-- | ```
-- |
-- | ## Tween Animation Pattern
-- |
-- | ```purescript
-- | type State = { opacity :: Animate.TweenState }
-- |
-- | update = case _ of
-- |   FadeIn -> 
-- |     transition state
-- |       { opacity = Animate.tweenTo state.opacity 1.0 300.0 easeOutCubic }
-- |       (animationFrame Tick)
-- | ```
module Hydrogen.Runtime.Animate
  ( -- * Spring Animation
    SpringState
  , springState
  , springTo
  , tickSpring
  
  -- * Tween Animation
  , TweenState
  , tweenState
  , tweenTo
  , tickTween
  
  -- * Spring Value Access
  , springValue
  , springComplete
  , resetSpring
  
  -- * Tween Value Access
  , tweenValue
  , tweenComplete
  , resetTween
  
  -- * Style Helpers
  , translateX
  , translateY
  , translate
  , scale
  , rotate
  , opacity
  ) where

import Prelude
  ( show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  )

import Hydrogen.Motion.Spring (SpringConfig)
import Hydrogen.Motion.Spring as Spring
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // spring // animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spring animation state.
-- |
-- | Contains everything needed to evaluate a spring at any timestamp.
type SpringState =
  { config :: SpringConfig
  , from :: Number
  , to :: Number
  , startTime :: Number
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
-- | start from its current position.
springTo :: SpringState -> Number -> Number -> SpringState
springTo state target timestamp =
  { config: state.config
  , from: state.currentValue
  , to: target
  , startTime: timestamp
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance spring animation to a new timestamp.
-- |
-- | Call this on each animation frame to update the current value.
tickSpring :: Number -> SpringState -> SpringState
tickSpring timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        -- Time since animation started (convert to 0-1 range)
        -- Springs typically settle in ~1 second, so we scale appropriately
        elapsed = (timestamp - state.startTime) / 1000.0
        
        -- Evaluate spring physics
        newValue = Spring.springValue state.config state.from state.to elapsed
        
        -- Check if spring is at rest
        atRest = Spring.isAtRest state.config state.from state.to elapsed
      in
        state 
          { currentValue = newValue
          , complete = atRest
          }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // tween // animation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tween (duration-based) animation state.
type TweenState =
  { easing :: Easing
  , from :: Number
  , to :: Number
  , duration :: Number     -- milliseconds
  , startTime :: Number
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
tweenTo :: TweenState -> Number -> Number -> Easing -> Number -> TweenState
tweenTo state target duration easing timestamp =
  { easing
  , from: state.currentValue
  , to: target
  , duration
  , startTime: timestamp
  , currentValue: state.currentValue
  , complete: false
  }

-- | Advance tween animation to a new timestamp.
tickTween :: Number -> TweenState -> TweenState
tickTween timestamp state =
  case state.complete of
    true -> state
    false ->
      let
        elapsed = timestamp - state.startTime
        progress = elapsed / state.duration
      in
        case progress >= 1.0 of
          true -> state
            { currentValue = state.to
            , complete = true
            }
          false ->
            let
              easedProgress = Easing.evaluate state.easing progress
              newValue = state.from + (state.to - state.from) * easedProgress
            in
              state { currentValue = newValue }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // spring // value // access
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the current value from a spring animation.
springValue :: SpringState -> Number
springValue s = s.currentValue

-- | Check if spring animation is complete.
springComplete :: SpringState -> Boolean
springComplete s = s.complete

-- | Reset a spring to a specific value (stops animation).
resetSpring :: Number -> SpringState -> SpringState
resetSpring v s = s { currentValue = v, from = v, to = v, complete = true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // tween // value // access
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the current value from a tween animation.
tweenValue :: TweenState -> Number
tweenValue s = s.currentValue

-- | Check if tween animation is complete.
tweenComplete :: TweenState -> Boolean
tweenComplete s = s.complete

-- | Reset a tween to a specific value (stops animation).
resetTween :: Number -> TweenState -> TweenState
resetTween v s = s { currentValue = v, from = v, to = v, complete = true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // style // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate translateX transform style value.
translateX :: Number -> String
translateX x = "translateX(" <> show x <> "px)"

-- | Generate translateY transform style value.
translateY :: Number -> String
translateY y = "translateY(" <> show y <> "px)"

-- | Generate translate transform style value.
translate :: Number -> Number -> String
translate x y = "translate(" <> show x <> "px, " <> show y <> "px)"

-- | Generate scale transform style value.
scale :: Number -> String
scale s = "scale(" <> show s <> ")"

-- | Generate rotate transform style value (degrees).
rotate :: Number -> String
rotate deg = "rotate(" <> show deg <> "deg)"

-- | Generate opacity style value.
opacity :: Number -> String
opacity o = show o
