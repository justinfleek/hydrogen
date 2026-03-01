-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // card // hover // animation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover Animation Effects — Lottie animation triggers for hover.
-- |
-- | ## Overview
-- |
-- | Animation effects control Lottie playback on hover:
-- | - Play animation when hover starts
-- | - Pause animation when hover ends
-- | - Reverse animation on leave
-- |
-- | ## Use Cases
-- |
-- | - Profile cards with animated avatars
-- | - Product cards with sparkle effects
-- | - Interactive illustrations
-- |
-- | ## Dependencies
-- |
-- | - Types (CardHoverConfig, HoverEasing)
-- | - Data.Maybe (optional values)

module Hydrogen.Element.Compound.Card.Hover.Animation
  ( -- * Lottie Effects
    playLottieOnHover
  , playLottieOnHoverWith
  , pauseLottieOnLeave
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Card.Hover.Types
  ( CardHoverConfig(CardHoverConfig)
  , HoverEasing(EaseLinear)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lottie effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Start Lottie animation when hover starts
playLottieOnHover :: CardHoverConfig
playLottieOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Just "/animations/default.json"
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- | Lottie animation with custom URL
playLottieOnHoverWith :: String -> CardHoverConfig
playLottieOnHoverWith url = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Just url
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }

-- | Pause Lottie animation when hover ends (with reverse)
pauseLottieOnLeave :: CardHoverConfig
pauseLottieOnLeave = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 0.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Just "/animations/default.json"
  , lottiePlayOnHover: true
  , lottiePauseOnLeave: true
  , lottieReverse: true
  , transitionDuration: 0.0
  , easing: EaseLinear
  }
