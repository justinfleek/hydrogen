-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // card // hover // audio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover Audio Effects — Sound feedback for hover interactions.
-- |
-- | ## Overview
-- |
-- | Audio effects provide sonic feedback for card interactions:
-- | - Hover enter sounds
-- | - Hover leave sounds
-- | - Click sounds
-- |
-- | ## Use Cases
-- |
-- | - Dog cards that bark when hovered
-- | - UI feedback sounds
-- | - Easter egg interactions
-- |
-- | ## Dependencies
-- |
-- | - Types (CardHoverConfig, HoverEasing)
-- | - Data.Maybe (optional values)

module Hydrogen.Element.Compound.Card.Hover.Audio
  ( -- * Sound Effects
    soundOnHover
  , soundOnHoverWith
  , soundOnClick
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Card.Hover.Types
  ( CardHoverConfig(CardHoverConfig)
  , HoverEasing(EaseOut, EaseLinear)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // sound effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Play sound when hover starts
soundOnHover :: CardHoverConfig
soundOnHover = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just "/sounds/hover.mp3"
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.5
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Sound on hover with custom URL and volume
soundOnHoverWith :: String -> Number -> CardHoverConfig
soundOnHoverWith url volume = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Just url
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: volume
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Play sound when clicked
soundOnClick :: CardHoverConfig
soundOnClick = CardHoverConfig
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
  , clickSound: Just "/sounds/click.mp3"
  , audioVolume: 0.5
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }
