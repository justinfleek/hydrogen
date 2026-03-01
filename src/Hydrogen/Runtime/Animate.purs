-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // runtime // animate
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
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `Hydrogen.Runtime.Animate.Spring` - Physics-based spring animations
-- | - `Hydrogen.Runtime.Animate.Tween` - Duration-based tween animations
-- | - `Hydrogen.Runtime.Animate.Style` - CSS transform/style helpers
-- | - `Hydrogen.Runtime.Animate.Vec2` - 2D vector animations
-- | - `Hydrogen.Runtime.Animate.Color` - RGB color animations
-- | - `Hydrogen.Runtime.Animate.Animator` - Multi-property animation manager
-- | - `Hydrogen.Runtime.Animate.Sequence` - Animation sequencing
module Hydrogen.Runtime.Animate
  ( -- * Spring Animation
    module Hydrogen.Runtime.Animate.Spring
  
  -- * Tween Animation
  , module Hydrogen.Runtime.Animate.Tween
  
  -- * Style Helpers
  , module Hydrogen.Runtime.Animate.Style
  
  -- * Vec2 Animation
  , module Hydrogen.Runtime.Animate.Vec2
  
  -- * Color Animation
  , module Hydrogen.Runtime.Animate.Color
  
  -- * Multi-Property Animation
  , module Hydrogen.Runtime.Animate.Animator
  
  -- * Sequencing
  , module Hydrogen.Runtime.Animate.Sequence
  ) where

import Hydrogen.Runtime.Animate.Spring
  ( SpringState
  , springState
  , springTo
  , tickSpring
  , springValue
  , springComplete
  , resetSpring
  )

import Hydrogen.Runtime.Animate.Tween
  ( TweenState
  , tweenState
  , tweenTo
  , tickTween
  , tweenValue
  , tweenComplete
  , resetTween
  )

import Hydrogen.Runtime.Animate.Style
  ( translateX
  , translateY
  , translate
  , scale
  , rotate
  , opacity
  )

import Hydrogen.Runtime.Animate.Vec2
  ( Vec2
  , Vec2State
  , vec2State
  , vec2To
  , tickVec2
  , vec2Value
  , vec2Complete
  )

import Hydrogen.Runtime.Animate.Color
  ( RGB
  , ColorState
  , colorState
  , colorTo
  , tickColor
  , colorValue
  , colorComplete
  , rgbToLegacyCss
  )

import Hydrogen.Runtime.Animate.Animator
  ( AnimatorState
  , animator
  , withSpring
  , withTween
  , withVec2
  , withColor
  , startAnimator
  , tickAnimator
  , animatorComplete
  , getSpring
  , getTween
  , getVec2
  , getColor
  )

import Hydrogen.Runtime.Animate.Sequence
  ( SequenceStep
  , Sequence
  , sequence
  , andThen
  , withDelay
  , tickSequence
  , sequenceComplete
  , sequenceValue
  )
