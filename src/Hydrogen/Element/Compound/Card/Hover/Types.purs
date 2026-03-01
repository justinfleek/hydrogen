-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // card // hover // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Hover Types — Core types for hover effect configuration.
-- |
-- | ## Overview
-- |
-- | This module contains the foundational types for card hover effects:
-- | - `CardHoverConfig`: Complete hover effect configuration
-- | - `HoverEasing`: Easing function for transitions
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show, comparison operators)
-- | - Data.Maybe (optional values)

module Hydrogen.Element.Compound.Card.Hover.Types
  ( -- * Card Hover Config
    CardHoverConfig(..)
  , cardHoverConfig
  , defaultCardHover
  , noHover
  
  -- * Easing
  , HoverEasing
      ( EaseLinear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseSpring
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover easing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Easing function for hover transitions
data HoverEasing
  = EaseLinear
  | EaseIn
  | EaseOut
  | EaseInOut
  | EaseSpring

derive instance eqHoverEasing :: Eq HoverEasing

instance showHoverEasing :: Show HoverEasing where
  show EaseLinear = "linear"
  show EaseIn = "ease-in"
  show EaseOut = "ease-out"
  show EaseInOut = "ease-in-out"
  show EaseSpring = "spring"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // card hover config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete hover effect configuration for a card.
-- |
-- | Composes all possible hover behaviors into a single configuration:
-- | - Transform effects (scale, lift, rotate, tilt)
-- | - Style effects (brightness, shadow, glow)
-- | - Audio triggers (hover enter, leave, click sounds)
-- | - Animation triggers (Lottie playback)
-- | - Timing (transition duration, easing)
-- |
-- | ## Transform Configuration
-- |
-- | - `liftPixels`: Vertical lift (negative Y translation)
-- | - `scaleFactor`: Scale multiplier (1.0 = no change)
-- | - `rotateDegrees`: Rotation angle
-- | - `tiltEnabled`: 3D tilt toward mouse position
-- | - `tiltMaxAngle`: Maximum tilt angle in degrees
-- |
-- | ## Style Configuration
-- |
-- | - `brightness`: Brightness multiplier (1.0 = no change)
-- | - `shadowIncrease`: Additional shadow spread on hover
-- | - `glowColor`: Optional glow color (hex)
-- | - `glowRadius`: Glow blur radius
-- |
-- | ## Audio Configuration
-- |
-- | - `hoverSound`: Sound URL for hover enter
-- | - `leaveSound`: Sound URL for hover leave
-- | - `clickSound`: Sound URL for click
-- | - `audioVolume`: Volume (0.0 to 1.0)
-- |
-- | ## Animation Configuration
-- |
-- | - `lottieUrl`: Lottie animation URL
-- | - `lottiePlayOnHover`: Play when hover starts
-- | - `lottiePauseOnLeave`: Pause when hover ends
-- | - `lottieReverse`: Reverse on leave
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Product card with subtle lift
-- | productHover = subtleHover
-- |
-- | -- Dog card that barks
-- | dogHover = soundOnHoverWith "/sounds/bark.mp3" 0.5
-- |
-- | -- Interactive card with animation
-- | fancyHover = cardHoverConfig
-- |   { liftPixels: 4.0
-- |   , scaleFactor: 1.02
-- |   , lottieUrl: Just "/animations/sparkle.json"
-- |   , lottiePlayOnHover: true
-- |   }
-- | ```
newtype CardHoverConfig = CardHoverConfig
  { -- Transform
    liftPixels :: Number               -- ^ Vertical lift in pixels
  , scaleFactor :: Number              -- ^ Scale multiplier
  , rotateDegrees :: Number            -- ^ Rotation angle
  , tiltEnabled :: Boolean             -- ^ Enable 3D tilt effect
  , tiltMaxAngle :: Number             -- ^ Maximum tilt angle (degrees)
  
  -- Style
  , brightness :: Number               -- ^ Brightness multiplier
  , shadowIncrease :: Number           -- ^ Additional shadow on hover
  , glowColor :: Maybe String          -- ^ Glow color (hex)
  , glowRadius :: Number               -- ^ Glow blur radius
  
  -- Audio
  , hoverSound :: Maybe String         -- ^ Sound URL for hover enter
  , leaveSound :: Maybe String         -- ^ Sound URL for hover leave
  , clickSound :: Maybe String         -- ^ Sound URL for click
  , audioVolume :: Number              -- ^ Audio volume (0.0 to 1.0)
  
  -- Animation
  , lottieUrl :: Maybe String          -- ^ Lottie animation URL
  , lottiePlayOnHover :: Boolean       -- ^ Play Lottie on hover
  , lottiePauseOnLeave :: Boolean      -- ^ Pause Lottie on leave
  , lottieReverse :: Boolean           -- ^ Reverse Lottie on leave
  
  -- Timing
  , transitionDuration :: Number       -- ^ Transition duration (ms)
  , easing :: HoverEasing              -- ^ Easing function
  }

derive instance eqCardHoverConfig :: Eq CardHoverConfig

instance showCardHoverConfig :: Show CardHoverConfig where
  show (CardHoverConfig c) = 
    "CardHoverConfig(lift:" <> show c.liftPixels <> 
    ", scale:" <> show c.scaleFactor <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // config constructor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create card hover config with full options
cardHoverConfig
  :: { liftPixels :: Number
     , scaleFactor :: Number
     , rotateDegrees :: Number
     , tiltEnabled :: Boolean
     , tiltMaxAngle :: Number
     , brightness :: Number
     , shadowIncrease :: Number
     , glowColor :: Maybe String
     , glowRadius :: Number
     , hoverSound :: Maybe String
     , leaveSound :: Maybe String
     , clickSound :: Maybe String
     , audioVolume :: Number
     , lottieUrl :: Maybe String
     , lottiePlayOnHover :: Boolean
     , lottiePauseOnLeave :: Boolean
     , lottieReverse :: Boolean
     , transitionDuration :: Number
     , easing :: HoverEasing
     }
  -> CardHoverConfig
cardHoverConfig cfg = CardHoverConfig
  { liftPixels: cfg.liftPixels
  , scaleFactor: clampScale cfg.scaleFactor
  , rotateDegrees: cfg.rotateDegrees
  , tiltEnabled: cfg.tiltEnabled
  , tiltMaxAngle: clampAngle cfg.tiltMaxAngle
  , brightness: clampBrightness cfg.brightness
  , shadowIncrease: clampShadow cfg.shadowIncrease
  , glowColor: cfg.glowColor
  , glowRadius: clampRadius cfg.glowRadius
  , hoverSound: cfg.hoverSound
  , leaveSound: cfg.leaveSound
  , clickSound: cfg.clickSound
  , audioVolume: clampVolume cfg.audioVolume
  , lottieUrl: cfg.lottieUrl
  , lottiePlayOnHover: cfg.lottiePlayOnHover
  , lottiePauseOnLeave: cfg.lottiePauseOnLeave
  , lottieReverse: cfg.lottieReverse
  , transitionDuration: clampDuration cfg.transitionDuration
  , easing: cfg.easing
  }
  where
    clampScale s
      | s < 0.5 = 0.5
      | s > 2.0 = 2.0
      | otherwise = s
    clampAngle a
      | a < 0.0 = 0.0
      | a > 45.0 = 45.0
      | otherwise = a
    clampBrightness b
      | b < 0.5 = 0.5
      | b > 2.0 = 2.0
      | otherwise = b
    clampShadow s
      | s < 0.0 = 0.0
      | s > 50.0 = 50.0
      | otherwise = s
    clampRadius r
      | r < 0.0 = 0.0
      | r > 100.0 = 100.0
      | otherwise = r
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampDuration d
      | d < 0.0 = 0.0
      | d > 2000.0 = 2000.0
      | otherwise = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // default values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default hover effect (subtle lift + shadow)
defaultCardHover :: CardHoverConfig
defaultCardHover = CardHoverConfig
  { liftPixels: 2.0
  , scaleFactor: 1.0
  , rotateDegrees: 0.0
  , tiltEnabled: false
  , tiltMaxAngle: 10.0
  , brightness: 1.0
  , shadowIncrease: 4.0
  , glowColor: Nothing
  , glowRadius: 0.0
  , hoverSound: Nothing
  , leaveSound: Nothing
  , clickSound: Nothing
  , audioVolume: 0.7
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 200.0
  , easing: EaseOut
  }

-- | No hover effects
noHover :: CardHoverConfig
noHover = CardHoverConfig
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
  , lottieUrl: Nothing
  , lottiePlayOnHover: false
  , lottiePauseOnLeave: false
  , lottieReverse: false
  , transitionDuration: 0.0
  , easing: EaseLinear
  }
