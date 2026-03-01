-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // element // compound // card // hover // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover Presets — Combined hover effect configurations.
-- |
-- | ## Overview
-- |
-- | Presets combine multiple hover effects into cohesive configurations:
-- | - Subtle: Small lift with shadow increase
-- | - Dramatic: Large scale with glow
-- | - Interactive: Sound + animation + visual effects
-- |
-- | ## Use Cases
-- |
-- | - Product cards (subtle)
-- | - Feature highlights (dramatic)
-- | - Game-like interfaces (interactive)
-- |
-- | ## Dependencies
-- |
-- | - Types (CardHoverConfig, HoverEasing)
-- | - Data.Maybe (optional values)

module Hydrogen.Element.Compound.Card.Hover.Presets
  ( -- * Combined Presets
    subtleHover
  , dramaticHover
  , interactiveHover
  , interactiveHoverWith
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Card.Hover.Types
  ( CardHoverConfig(CardHoverConfig)
  , HoverEasing(EaseOut, EaseSpring)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // combined presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subtle hover (small lift + shadow increase)
subtleHover :: CardHoverConfig
subtleHover = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.02
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 150.0
  , easing: EaseOut
  }

-- | Dramatic hover (large scale + glow)
dramaticHover :: CardHoverConfig
dramaticHover = CardHoverConfig
  { liftPixels: 8.0
  , scaleFactor: 1.05
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.1
  , shadowIncrease: 16.0
  , glowColor: Just "#3B82F6"
  , glowRadius: 30.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 300.0
  , easing: EaseSpring
  }

-- | Interactive hover (sound + animation)
interactiveHover :: CardHoverConfig
interactiveHover = CardHoverConfig
  { liftPixels: 4.0
  , scaleFactor: 1.02
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 8.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just "/sounds/hover.mp3"
  , leaveSound: Nothing
  , clickSound: Just "/sounds/click.mp3"
  , audioVolume: 0.5
  , lottieUrl: Just "/animations/sparkle.json"
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Interactive hover with custom sounds and animation
interactiveHoverWith :: String -> String -> String -> CardHoverConfig
interactiveHoverWith hoverSoundUrl clickSoundUrl lottieUrl = CardHoverConfig
  { liftPixels: 4.0
  , scaleFactor: 1.02
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 8.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just hoverSoundUrl
  , leaveSound: Nothing
  , clickSound: Just clickSoundUrl
  , audioVolume: 0.5
  , lottieUrl: Just lottieUrl
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }
