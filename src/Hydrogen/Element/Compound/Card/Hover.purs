-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // compound // card // hover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover — Interactive hover effects for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Hover effects make cards feel alive and responsive. This module
-- | coordinates multiple effect types that can trigger on hover:
-- | - Visual transforms (scale, lift, rotate)
-- | - Audio feedback (dog bark, click sound)
-- | - Animation playback (Lottie starts playing)
-- | - Particle effects (sparkles, confetti)
-- |
-- | ## Use Cases
-- |
-- | - Product cards that enlarge on hover
-- | - Dog cards that bark when hovered
-- | - Profile cards with animated avatars
-- | - Easter egg interactions
-- |
-- | ## State Machine
-- |
-- | ```
-- | idle → entering → active → leaving → idle
-- |        (200ms)    (hold)   (200ms)
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - Types: Core types (CardHoverConfig, HoverEasing)
-- | - Visual: Transform and style effects
-- | - Audio: Sound feedback effects
-- | - Animation: Lottie animation triggers
-- | - Presets: Combined effect configurations
-- |
-- | ## Dependencies
-- |
-- | - Schema.Reactive.HoverEffect (hover primitives)
-- | - Schema.Audio.Trigger (audio triggers)
-- | - Schema.Motion.Lottie (animation triggers)

module Hydrogen.Element.Compound.Card.Hover
  ( module Types
  , module Visual
  , module Audio
  , module Animation
  , module Presets
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // submodule imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Card.Hover.Types
  ( CardHoverConfig(..)
  , HoverEasing(..)
  , cardHoverConfig
  , defaultCardHover
  , noHover
  ) as Types

import Hydrogen.Element.Compound.Card.Hover.Visual
  ( glowOnHover
  , glowOnHoverWith
  , liftOnHover
  , liftOnHoverWith
  , scaleOnHover
  , scaleOnHoverWith
  , tiltOnHover
  ) as Visual

import Hydrogen.Element.Compound.Card.Hover.Audio
  ( soundOnClick
  , soundOnHover
  , soundOnHoverWith
  ) as Audio

import Hydrogen.Element.Compound.Card.Hover.Animation
  ( pauseLottieOnLeave
  , playLottieOnHover
  , playLottieOnHoverWith
  ) as Animation

import Hydrogen.Element.Compound.Card.Hover.Presets
  ( dramaticHover
  , interactiveHover
  , interactiveHoverWith
  , subtleHover
  ) as Presets
