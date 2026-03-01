-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // tour // animation // composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Animation Composition
-- |
-- | This module provides functions for composing multiple animations together.
-- | Animations can be combined sequentially, in parallel, or with staggered timing.
-- |
-- | ## Composition Modes
-- |
-- | - Sequence: Play one after another
-- | - Parallel: Play simultaneously
-- | - Stagger: Parallel with delay between each
-- |
-- | ## Modifiers
-- |
-- | - withDelay: Add delay before animation starts
-- | - withDuration: Override animation duration

module Hydrogen.Tour.Animation.Composition
  ( -- * Composition Functions
    sequence
  , parallel
  , stagger
    -- * Modifiers
  , withDelay
  , withDuration
  ) where

import Prelude
  ( (+)
  )

import Hydrogen.Tour.Animation.Types
  ( AnimationComposition(Sequence, Parallel, Stagger)
  , TourAnimation(AnimFade, AnimSlide, AnimScale, AnimSpring, AnimComposite)
  )
import Hydrogen.Tour.Types (Milliseconds(Milliseconds))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // composition functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sequence animations (play one after another)
-- |
-- | Each animation starts after the previous one completes.
sequence :: Array TourAnimation -> TourAnimation
sequence animations = AnimComposite { animations, composition: Sequence }

-- | Parallel animations (play simultaneously)
-- |
-- | All animations start at the same time.
parallel :: Array TourAnimation -> TourAnimation
parallel animations = AnimComposite { animations, composition: Parallel }

-- | Stagger animations (parallel with delay between each)
-- |
-- | Each animation starts after a specified delay from the previous.
-- | Useful for animating lists or grids.
stagger :: Milliseconds -> Array TourAnimation -> TourAnimation
stagger delayMs animations = AnimComposite { animations, composition: Stagger delayMs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add delay to an animation
-- |
-- | Note: For springs, delay is not directly supported. Consider using
-- | a composition with a preceding delay animation.
withDelay :: Milliseconds -> TourAnimation -> TourAnimation
withDelay (Milliseconds delayMs) anim = case anim of
  AnimFade cfg -> AnimFade cfg { duration = addDelay cfg.duration }
  AnimSlide cfg -> AnimSlide cfg { duration = addDelay cfg.duration }
  AnimScale cfg -> AnimScale cfg { duration = addDelay cfg.duration }
  AnimSpring cfg -> AnimSpring cfg  -- Springs don't have delay built-in
  AnimComposite cfg -> AnimComposite cfg
  where
  addDelay :: Milliseconds -> Milliseconds
  addDelay (Milliseconds d) = Milliseconds (d + delayMs)

-- | Override animation duration
-- |
-- | Note: For springs, duration is determined by physics parameters.
-- | Use spring config to control timing instead.
withDuration :: Milliseconds -> TourAnimation -> TourAnimation
withDuration duration anim = case anim of
  AnimFade cfg -> AnimFade cfg { duration = duration }
  AnimSlide cfg -> AnimSlide cfg { duration = duration }
  AnimScale cfg -> AnimScale cfg { duration = duration }
  AnimSpring _ -> anim  -- Springs don't use duration
  AnimComposite cfg -> AnimComposite cfg
