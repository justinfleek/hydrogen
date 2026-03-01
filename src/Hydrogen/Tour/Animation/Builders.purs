-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // tour // animation // builders
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Builder Functions
-- |
-- | This module provides convenient builder functions for creating common
-- | animation patterns. These builders compose into more complex animations.
-- |
-- | ## Common Patterns
-- |
-- | - Fade: Opacity transitions
-- | - Slide: Position translations
-- | - Scale: Size transformations
-- | - Combined: Fade + Slide for tooltips

module Hydrogen.Tour.Animation.Builders
  ( -- * Fade Animations
    fadeIn
  , fadeOut
    -- * Slide Animations
  , slideIn
  , slideOut
    -- * Scale Animations
  , scaleIn
  , scaleOut
    -- * Combined Animations
  , fadeSlideIn
  , fadeSlideOut
  ) where

import Prelude
  ( negate
  )

import Hydrogen.Tour.Animation.Types
  ( AnimationComposition(Parallel)
  , EasingCurve
  , EasingPreset(EaseOut)
  , EasingCurve(Preset)
  , SpringConfig
  , TourAnimation(AnimFade, AnimSlide, AnimScale, AnimSpring, AnimComposite)
  )
import Hydrogen.Tour.Types
  ( Milliseconds(Milliseconds)
  , Pixel(Pixel)
  , Side(Top, Bottom, Left, Right)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // fade animations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fade in animation
-- |
-- | Animates opacity from 0 to 1 over the specified duration.
fadeIn :: Milliseconds -> EasingCurve -> TourAnimation
fadeIn duration easing = AnimFade
  { opacity: { from: 0.0, to: 1.0 }
  , duration
  , easing
  }

-- | Fade out animation
-- |
-- | Animates opacity from 1 to 0 over the specified duration.
fadeOut :: Milliseconds -> EasingCurve -> TourAnimation
fadeOut duration easing = AnimFade
  { opacity: { from: 1.0, to: 0.0 }
  , duration
  , easing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slide animations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slide in from a direction
-- |
-- | Animates from outside the specified side to the final position.
slideIn :: Side -> Pixel -> Milliseconds -> EasingCurve -> TourAnimation
slideIn side (Pixel distance) duration easing = AnimSlide
  { translate: case side of
      Top -> { fromX: Pixel 0, fromY: Pixel (negate distance), toX: Pixel 0, toY: Pixel 0 }
      Bottom -> { fromX: Pixel 0, fromY: Pixel distance, toX: Pixel 0, toY: Pixel 0 }
      Left -> { fromX: Pixel (negate distance), fromY: Pixel 0, toX: Pixel 0, toY: Pixel 0 }
      Right -> { fromX: Pixel distance, fromY: Pixel 0, toX: Pixel 0, toY: Pixel 0 }
  , duration
  , easing
  }

-- | Slide out to a direction
-- |
-- | Animates from the current position to outside the specified side.
slideOut :: Side -> Pixel -> Milliseconds -> EasingCurve -> TourAnimation
slideOut side (Pixel distance) duration easing = AnimSlide
  { translate: case side of
      Top -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel 0, toY: Pixel (negate distance) }
      Bottom -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel 0, toY: Pixel distance }
      Left -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel (negate distance), toY: Pixel 0 }
      Right -> { fromX: Pixel 0, fromY: Pixel 0, toX: Pixel distance, toY: Pixel 0 }
  , duration
  , easing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // scale animations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale in animation
-- |
-- | Animates scale from the specified value to 1.0.
scaleIn :: Number -> Milliseconds -> EasingCurve -> TourAnimation
scaleIn fromScale duration easing = AnimScale
  { scale: { from: fromScale, to: 1.0 }
  , transformOrigin: "center"
  , duration
  , easing
  }

-- | Scale out animation
-- |
-- | Animates scale from 1.0 to the specified value.
scaleOut :: Number -> Milliseconds -> EasingCurve -> TourAnimation
scaleOut toScale duration easing = AnimScale
  { scale: { from: 1.0, to: toScale }
  , transformOrigin: "center"
  , duration
  , easing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // combined animations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined fade + slide in (common tooltip entrance)
-- |
-- | Uses spring physics for the slide, CSS easing for the fade.
-- | This is the recommended animation for tooltip entrances.
fadeSlideIn :: Side -> SpringConfig -> TourAnimation
fadeSlideIn side spring = AnimComposite
  { animations:
      [ AnimFade { opacity: { from: 0.0, to: 1.0 }, duration: Milliseconds 200, easing: Preset EaseOut }
      , AnimSpring { property: "translateY", from: slideOffset side, to: 0.0, spring }
      ]
  , composition: Parallel
  }
  where
  slideOffset :: Side -> Number
  slideOffset = case _ of
    Top -> -8.0
    Bottom -> 8.0
    Left -> 0.0
    Right -> 0.0

-- | Combined fade + slide out
-- |
-- | Uses CSS easing for both fade and slide.
fadeSlideOut :: Side -> Milliseconds -> EasingCurve -> TourAnimation
fadeSlideOut side duration easing = AnimComposite
  { animations:
      [ fadeOut duration easing
      , slideOut side (Pixel 8) duration easing
      ]
  , composition: Parallel
  }
