-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // compound // card // hover // visual
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover Visual Effects — Transform and style effects for hover.
-- |
-- | ## Overview
-- |
-- | Visual effects modify the card's appearance on hover:
-- | - Lift (translateY)
-- | - Scale (transform scale)
-- | - Glow (box-shadow with color)
-- | - Tilt (3D perspective transform)
-- |
-- | ## Dependencies
-- |
-- | - Types (CardHoverConfig, HoverEasing)
-- | - Data.Maybe (optional values)

module Hydrogen.Element.Compound.Card.Hover.Visual
  ( -- * Lift Effects
    liftOnHover
  , liftOnHoverWith
  
  -- * Scale Effects
  , scaleOnHover
  , scaleOnHoverWith
  
  -- * Glow Effects
  , glowOnHover
  , glowOnHoverWith
  
  -- * Tilt Effects
  , tiltOnHover
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (*)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Card.Hover.Types
  ( CardHoverConfig(CardHoverConfig)
  , HoverEasing(EaseOut, EaseInOut)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // lift effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lift card on hover (translateY)
liftOnHover :: CardHoverConfig
liftOnHover = CardHoverConfig
  { liftPixels: 4.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: 8.0
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
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Lift with custom pixels
liftOnHoverWith :: Number -> CardHoverConfig
liftOnHoverWith pixels = CardHoverConfig
  { liftPixels: pixels
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
  , shadowIncrease: pixels * 2.0
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
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scale effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale card on hover
scaleOnHover :: CardHoverConfig
scaleOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.03
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
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
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | Scale with custom factor
scaleOnHoverWith :: Number -> CardHoverConfig
scaleOnHoverWith factor = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: factor
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.0
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
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glow effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add glow on hover
glowOnHover :: CardHoverConfig
glowOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 0.0
  , glowColor: Just "#3B82F6"
  , glowRadius: 20.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 250.0
  , easing: EaseInOut
  }

-- | Glow with custom color
glowOnHoverWith :: String -> Number -> CardHoverConfig
glowOnHoverWith color radius = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 0.0
  , brightness: 1.05
  , shadowIncrease: 0.0
  , glowColor: Just color
  , glowRadius: radius
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.0
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 250.0
  , easing: EaseInOut
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tilt effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tilt toward mouse position on hover
tiltOnHover :: CardHoverConfig
tiltOnHover = CardHoverConfig
  { liftPixels: 0.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: true
  , tiltMaxAngle: 10.0
  , brightness: 1.0
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
  , transitionDuration: 100.0
  , easing: EaseOut
  }
