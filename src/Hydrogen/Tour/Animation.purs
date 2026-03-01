-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // tour // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation System for Product Tours
-- |
-- | This module provides the motion vocabulary for tour transitions:
-- | - Easing curves (bounded, named presets + custom cubic-bezier)
-- | - Spring physics configuration
-- | - Morph transitions (spotlight shape morphing)
-- | - Animation composition
-- |
-- | ## Design Philosophy
-- |
-- | All animations are described as pure data. The runtime interprets these
-- | descriptions to produce actual motion. This enables:
-- | - Deterministic animations (same config = same motion)
-- | - Composable animation primitives
-- | - Spring physics for natural feel
-- | - Respect for reduced motion preferences
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Animation as Anim
-- |
-- | -- Use presets
-- | tooltipAnim = Anim.fadeSlideIn Anim.Bottom Anim.springSnappy
-- |
-- | -- Custom easing
-- | customEase = Anim.cubicBezier 0.34 1.56 0.64 1.0
-- |
-- | -- Compose animations
-- | combined = Anim.sequence [fadeIn, slideIn, scaleUp]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Types: Core type definitions
-- | - Easing: Easing curve functions
-- | - Spring: Spring physics configuration
-- | - Morph: Morph transition configuration
-- | - Builders: Animation builder functions
-- | - Composition: Animation composition
-- | - ReducedMotion: Accessibility support
-- | - Css: CSS generation

module Hydrogen.Tour.Animation
  ( module Types
  , module Easing
  , module Spring
  , module Morph
  , module Builders
  , module Composition
  , module ReducedMotion
  , module Css
  ) where

import Hydrogen.Tour.Animation.Types
  ( EasingCurve(Preset, CubicBezier)
  , EasingPreset
    ( EaseLinear
    , EaseIn
    , EaseOut
    , EaseInOut
    , EaseInQuad
    , EaseOutQuad
    , EaseInOutQuad
    , EaseInCubic
    , EaseOutCubic
    , EaseInOutCubic
    , EaseInQuart
    , EaseOutQuart
    , EaseInOutQuart
    , EaseInExpo
    , EaseOutExpo
    , EaseInOutExpo
    , EaseInBack
    , EaseOutBack
    , EaseInOutBack
    )
  , SpringConfig
  , SpringPreset(SpringDefault, SpringSnappy, SpringGentle, SpringBouncy, SpringStiff)
  , MorphConfig
  , MorphTarget(MorphToRect, MorphToCircle, MorphToViewport, MorphHidden)
  , TourAnimation(AnimFade, AnimSlide, AnimScale, AnimSpring, AnimComposite)
  , AnimationDirection(Normal, Reverse, Alternate, AlternateReverse)
  , AnimationFill(FillNone, FillForwards, FillBackwards, FillBoth)
  , AnimationPlayState(Playing, Paused)
  , AnimationComposition(Sequence, Parallel, Stagger)
  , ReducedMotionStrategy(InstantTransition, FadeOnly, SlowerAnimation, PreserveAnimation)
  ) as Types

import Hydrogen.Tour.Animation.Easing
  ( cubicBezier
  , easingPreset
  , easingToCss
  ) as Easing

import Hydrogen.Tour.Animation.Spring
  ( springConfig
  , springPreset
  , springDefault
  , springSnappy
  , springGentle
  , springBouncy
  , springStiff
  ) as Spring

import Hydrogen.Tour.Animation.Morph
  ( defaultMorphConfig
  , morphWithSpring
  , morphWithDuration
  ) as Morph

import Hydrogen.Tour.Animation.Builders
  ( fadeIn
  , fadeOut
  , slideIn
  , slideOut
  , scaleIn
  , scaleOut
  , fadeSlideIn
  , fadeSlideOut
  ) as Builders

import Hydrogen.Tour.Animation.Composition
  ( sequence
  , parallel
  , stagger
  , withDelay
  , withDuration
  ) as Composition

import Hydrogen.Tour.Animation.ReducedMotion
  ( applyReducedMotion
  ) as ReducedMotion

import Hydrogen.Tour.Animation.Css
  ( animationToCss
  , keyframesToCss
  ) as Css
