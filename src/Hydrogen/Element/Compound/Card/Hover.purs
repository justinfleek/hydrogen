-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // card // hover
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
-- | ## Dependencies
-- |
-- | - Schema.Reactive.HoverEffect (hover primitives)
-- | - Schema.Audio.Trigger (audio triggers)
-- | - Schema.Motion.Lottie (animation triggers)

module Hydrogen.Element.Compound.Card.Hover
  ( -- * Card Hover Config
    CardHoverConfig
  , cardHoverConfig
  , defaultCardHover
  , noHover
  
  -- * Visual Effects
  , liftOnHover
  , scaleOnHover
  , glowOnHover
  , tiltOnHover
  
  -- * Audio Effects
  , soundOnHover
  , soundOnClick
  
  -- * Animation Effects
  , playLottieOnHover
  , pauseLottieOnLeave
  
  -- * Combined Presets
  , subtleHover
  , dramaticHover
  , interactiveHover
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // card hover config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete hover effect configuration for a card
data CardHoverConfig = CardHoverConfigPlaceholder

derive instance eqCardHoverConfig :: Eq CardHoverConfig

instance showCardHoverConfig :: Show CardHoverConfig where
  show _ = "CardHoverConfig"

-- | Create card hover config (placeholder)
cardHoverConfig :: CardHoverConfig
cardHoverConfig = CardHoverConfigPlaceholder

-- | Default hover effect (subtle lift + shadow)
defaultCardHover :: CardHoverConfig
defaultCardHover = CardHoverConfigPlaceholder

-- | No hover effects
noHover :: CardHoverConfig
noHover = CardHoverConfigPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // visual effects
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Lift card on hover (translateY)
liftOnHover :: CardHoverConfig
liftOnHover = CardHoverConfigPlaceholder

-- | Scale card on hover
scaleOnHover :: CardHoverConfig
scaleOnHover = CardHoverConfigPlaceholder

-- | Add glow on hover
glowOnHover :: CardHoverConfig
glowOnHover = CardHoverConfigPlaceholder

-- | Tilt toward mouse position on hover
tiltOnHover :: CardHoverConfig
tiltOnHover = CardHoverConfigPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // audio effects
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Play sound when hover starts
soundOnHover :: CardHoverConfig
soundOnHover = CardHoverConfigPlaceholder

-- | Play sound when clicked
soundOnClick :: CardHoverConfig
soundOnClick = CardHoverConfigPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // animation effects
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Start Lottie animation when hover starts
playLottieOnHover :: CardHoverConfig
playLottieOnHover = CardHoverConfigPlaceholder

-- | Pause Lottie animation when hover ends
pauseLottieOnLeave :: CardHoverConfig
pauseLottieOnLeave = CardHoverConfigPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // combined presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Subtle hover (small lift + shadow increase)
subtleHover :: CardHoverConfig
subtleHover = CardHoverConfigPlaceholder

-- | Dramatic hover (large scale + glow)
dramaticHover :: CardHoverConfig
dramaticHover = CardHoverConfigPlaceholder

-- | Interactive hover (sound + animation)
interactiveHover :: CardHoverConfig
interactiveHover = CardHoverConfigPlaceholder
