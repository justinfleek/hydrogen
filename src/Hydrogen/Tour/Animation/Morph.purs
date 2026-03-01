-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // tour // animation // morph
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Morph Configuration for Spotlight Transitions
-- |
-- | This module provides configuration for spotlight morph transitions.
-- | Morphing allows the spotlight shape to smoothly animate between
-- | different target elements during a product tour.
-- |
-- | ## Morph Targets
-- |
-- | - Rectangle: Standard element highlight
-- | - Circle: Circular focus area
-- | - Viewport: Full screen (no spotlight)
-- | - Hidden: Invisible state

module Hydrogen.Tour.Animation.Morph
  ( -- * Configuration
    defaultMorphConfig
  , morphWithSpring
  , morphWithDuration
    -- * Re-exports
  , module Types
  ) where

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Tour.Animation.Types
  ( EasingCurve(Preset)
  , EasingPreset(EaseOutCubic)
  , MorphConfig
  , MorphTarget(MorphToRect, MorphToCircle, MorphToViewport, MorphHidden)
  , SpringConfig
  ) as Types
import Hydrogen.Tour.Animation.Spring (springDefault)
import Hydrogen.Tour.Types (Milliseconds(Milliseconds))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default morph configuration
-- |
-- | Uses spring physics for natural-feeling transitions.
defaultMorphConfig :: Types.MorphConfig
defaultMorphConfig =
  { duration: Milliseconds 300
  , spring: Just springDefault
  , easing: Types.Preset Types.EaseOutCubic
  , morphPath: true
  }

-- | Morph with spring physics
-- |
-- | Creates a morph configuration using the provided spring settings.
-- | Spring physics provide more natural motion than CSS easing.
morphWithSpring :: Types.SpringConfig -> Types.MorphConfig
morphWithSpring spring = defaultMorphConfig { spring = Just spring }

-- | Morph with duration (no spring)
-- |
-- | Creates a morph configuration using CSS transitions instead of spring.
-- | Useful when precise timing is required.
morphWithDuration :: Milliseconds -> Types.EasingCurve -> Types.MorphConfig
morphWithDuration duration easing = 
  defaultMorphConfig { spring = Nothing, duration = duration, easing = easing }
