-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // tour // animation // reducedmotion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reduced Motion Support
-- |
-- | This module provides support for the "prefers-reduced-motion" media query.
-- | Users who experience motion sickness or have vestibular disorders can
-- | enable this preference in their OS settings.
-- |
-- | ## Strategies
-- |
-- | - InstantTransition: No animation at all
-- | - FadeOnly: Allow fades, remove motion
-- | - SlowerAnimation: Keep animation but slower
-- | - PreserveAnimation: Ignore preference (not recommended)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Animation.ReducedMotion (applyReducedMotion)
-- |
-- | -- In runtime, detect preference and apply
-- | finalAnim = applyReducedMotion FadeOnly tooltipAnimation
-- | ```

module Hydrogen.Tour.Animation.ReducedMotion
  ( -- * Application
    applyReducedMotion
    -- * Re-exports
  , module Types
  ) where

import Prelude
  ( map
  , (<)
  , (*)
  , ($)
  )

import Data.Int (floor, toNumber)
import Data.Number (floor) as Number
import Hydrogen.Tour.Animation.Types
  ( EasingCurve(Preset)
  , EasingPreset(EaseLinear, EaseOut)
  , ReducedMotionStrategy(InstantTransition, FadeOnly, SlowerAnimation, PreserveAnimation)
  , SpringConfig
  , TourAnimation(AnimFade, AnimSlide, AnimScale, AnimSpring, AnimComposite)
  ) as Types
import Hydrogen.Tour.Types (Milliseconds(Milliseconds))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply reduced motion strategy to an animation
-- |
-- | Transforms an animation according to the specified strategy.
-- | This should be called at runtime when the user preference is known.
applyReducedMotion :: Types.ReducedMotionStrategy -> Types.TourAnimation -> Types.TourAnimation
applyReducedMotion strategy anim = case strategy of
  Types.InstantTransition -> makeInstant anim
  Types.FadeOnly -> stripMotion anim
  Types.SlowerAnimation -> makeSlower anim
  Types.PreserveAnimation -> anim
  where
  makeInstant :: Types.TourAnimation -> Types.TourAnimation
  makeInstant = case _ of
    Types.AnimFade cfg -> Types.AnimFade cfg { duration = Milliseconds 0 }
    Types.AnimSlide cfg -> Types.AnimSlide cfg { duration = Milliseconds 0 }
    Types.AnimScale cfg -> Types.AnimScale cfg { duration = Milliseconds 0 }
    Types.AnimSpring cfg -> Types.AnimFade
      { opacity: { from: if cfg.from < cfg.to then 0.0 else 1.0
                 , to: if cfg.from < cfg.to then 1.0 else 0.0 }
      , duration: Milliseconds 0
      , easing: Types.Preset Types.EaseLinear
      }
    Types.AnimComposite cfg -> Types.AnimComposite cfg { animations = map makeInstant cfg.animations }
  
  stripMotion :: Types.TourAnimation -> Types.TourAnimation
  stripMotion = case _ of
    Types.AnimFade cfg -> Types.AnimFade cfg  -- Keep fades
    Types.AnimSlide cfg -> Types.AnimFade  -- Convert slides to fades
      { opacity: { from: 0.0, to: 1.0 }
      , duration: cfg.duration
      , easing: cfg.easing
      }
    Types.AnimScale cfg -> Types.AnimFade  -- Convert scales to fades
      { opacity: { from: 0.0, to: 1.0 }
      , duration: cfg.duration
      , easing: cfg.easing
      }
    Types.AnimSpring _ -> Types.AnimFade
      { opacity: { from: 0.0, to: 1.0 }
      , duration: Milliseconds 200
      , easing: Types.Preset Types.EaseOut
      }
    Types.AnimComposite cfg -> Types.AnimComposite cfg { animations = map stripMotion cfg.animations }
  
  makeSlower :: Types.TourAnimation -> Types.TourAnimation
  makeSlower = case _ of
    Types.AnimFade cfg -> Types.AnimFade cfg { duration = multiplyDuration 2.0 cfg.duration }
    Types.AnimSlide cfg -> Types.AnimSlide cfg { duration = multiplyDuration 2.0 cfg.duration }
    Types.AnimScale cfg -> Types.AnimScale cfg { duration = multiplyDuration 2.0 cfg.duration }
    Types.AnimSpring cfg -> Types.AnimSpring cfg { spring = makeSpringSlower cfg.spring }
    Types.AnimComposite cfg -> Types.AnimComposite cfg { animations = map makeSlower cfg.animations }
  
  multiplyDuration :: Number -> Milliseconds -> Milliseconds
  multiplyDuration factor (Milliseconds ms) = Milliseconds $ floor $ Number.floor (toNumber ms * factor)
  
  makeSpringSlower :: Types.SpringConfig -> Types.SpringConfig
  makeSpringSlower cfg = cfg 
    { stiffness = cfg.stiffness * 0.5
    , damping = cfg.damping * 1.5
    }
