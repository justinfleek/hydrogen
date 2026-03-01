-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // carousel // item hover
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Item Hover — Interactive hover effects for carousel items.
-- |
-- | ## Design Philosophy
-- |
-- | Hover effects define interactive behaviors:
-- | - Audio playback (enter/leave/loop sounds)
-- | - Lottie animation triggers
-- | - Transform effects (scale, lift)
-- | - Combined effects
-- |
-- | ## Dependencies
-- |
-- | - Data.Maybe for optional audio/lottie URLs

module Hydrogen.Element.Compound.Carousel.Item.Hover
  ( ItemHover
      ( HoverNone
      , HoverAudio
      , HoverAudioEnterLeave
      , HoverLottie
      , HoverLottieReverse
      , HoverScale
      , HoverLift
      , HoverCombined
      )
  , ItemHoverConfig
  , itemHover
  , noItemHover
  , audioOnHover
  , audioOnHoverWith
  , audioOnHoverEnterLeave
  , lottieOnHover
  , lottieOnHoverReverse
  , scaleOnHover
  , liftOnHover
  , combinedHover
  , combinedHoverWith
  , defaultHoverConfig
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

import Data.Maybe (Maybe(Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hover effect configuration for an item.
-- |
-- | Defines interactive behaviors when hovering over carousel items:
-- | - Audio playback (enter/leave/loop sounds)
-- | - Lottie animation triggers
-- | - Transform effects (scale, lift)
-- | - Combined effects
-- |
-- | ## Audio Hover
-- |
-- | Play sounds when mouse enters/leaves the item.
-- | Volume is normalized 0.0 to 1.0.
-- |
-- | ## Lottie Hover
-- |
-- | Start a Lottie animation on hover. Can play forward on enter
-- | and reverse on leave for smooth transitions.
-- |
-- | ## Transform Hover
-- |
-- | Scale, translate, or rotate the item on hover.
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Play bark sound at 50% volume
-- | dogCard = audioOnHover "/sounds/bark.mp3" 0.5
-- |
-- | -- Animate dog wagging tail
-- | animatedDog = lottieOnHover "/animations/dog-wag.json"
-- |
-- | -- Scale up with sound
-- | combined = combinedHoverWith 
-- |   (Just "/sounds/hover.mp3") 
-- |   (Just "/animations/pulse.json")
-- |   1.05
-- | ```
data ItemHover
  = HoverNone                                     -- ^ No hover effects
  | HoverAudio String Number                      -- ^ audioUrl, volume
  | HoverAudioEnterLeave String String Number     -- ^ enterUrl, leaveUrl, volume
  | HoverLottie String                            -- ^ lottieUrl
  | HoverLottieReverse String                     -- ^ lottieUrl (reverse on leave)
  | HoverScale Number Number                      -- ^ scale factor, duration ms
  | HoverLift Number Number                       -- ^ lift pixels, duration ms
  | HoverCombined ItemHoverConfig                 -- ^ Full configuration

-- | Full hover configuration for combined effects
type ItemHoverConfig =
  { audioUrl :: Maybe String           -- ^ Sound to play on enter
  , audioVolume :: Number              -- ^ Audio volume (0.0 to 1.0)
  , lottieUrl :: Maybe String          -- ^ Lottie animation URL
  , lottieReverse :: Boolean           -- ^ Reverse animation on leave
  , scaleFactor :: Number              -- ^ Scale multiplier (1.0 = no change)
  , liftPixels :: Number               -- ^ Vertical lift in pixels
  , durationMs :: Number               -- ^ Transition duration
  }

derive instance eqItemHover :: Eq ItemHover

instance showItemHover :: Show ItemHover where
  show HoverNone = "none"
  show (HoverAudio _ v) = "audio:" <> show v
  show (HoverAudioEnterLeave _ _ v) = "audio-enter-leave:" <> show v
  show (HoverLottie _) = "lottie"
  show (HoverLottieReverse _) = "lottie-reverse"
  show (HoverScale s _) = "scale:" <> show s
  show (HoverLift l _) = "lift:" <> show l <> "px"
  show (HoverCombined _) = "combined"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create hover with scale effect
itemHover :: Number -> Number -> ItemHover
itemHover scale duration = HoverScale (clampScale scale) (clampDuration duration)
  where
    clampScale s
      | s < 0.5 = 0.5
      | s > 2.0 = 2.0
      | otherwise = s
    clampDuration d
      | d < 0.0 = 0.0
      | d > 2000.0 = 2000.0
      | otherwise = d

-- | No hover effects
noItemHover :: ItemHover
noItemHover = HoverNone

-- | Play audio on hover enter
-- |
-- | - url: Audio file URL
-- | - volume: Playback volume (0.0 to 1.0)
audioOnHover :: String -> ItemHover
audioOnHover url = HoverAudio url 0.7

-- | Play audio with custom volume
audioOnHoverWith :: String -> Number -> ItemHover
audioOnHoverWith url volume = HoverAudio url (clampVolume volume)
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Play different sounds on enter and leave
audioOnHoverEnterLeave :: String -> String -> Number -> ItemHover
audioOnHoverEnterLeave enterUrl leaveUrl volume = 
  HoverAudioEnterLeave enterUrl leaveUrl (clampVolume volume)
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Start Lottie animation on hover
lottieOnHover :: String -> ItemHover
lottieOnHover = HoverLottie

-- | Lottie with reverse playback on leave
lottieOnHoverReverse :: String -> ItemHover
lottieOnHoverReverse = HoverLottieReverse

-- | Scale effect on hover
scaleOnHover :: Number -> ItemHover
scaleOnHover factor = HoverScale factor 200.0

-- | Lift effect on hover (vertical translate)
liftOnHover :: Number -> ItemHover
liftOnHover pixels = HoverLift pixels 200.0

-- | Combined hover effects
combinedHover :: ItemHover
combinedHover = HoverCombined defaultHoverConfig

-- | Combined hover with custom configuration
combinedHoverWith 
  :: Maybe String    -- ^ Audio URL
  -> Maybe String    -- ^ Lottie URL
  -> Number          -- ^ Scale factor
  -> ItemHover
combinedHoverWith audio lottie scale = HoverCombined
  { audioUrl: audio
  , audioVolume: 0.7
  , lottieUrl: lottie
  , lottieReverse: true
  , scaleFactor: scale
  , liftPixels: 0.0
  , durationMs: 200.0
  }

-- | Default hover configuration
defaultHoverConfig :: ItemHoverConfig
defaultHoverConfig =
  { audioUrl: Nothing
  , audioVolume: 0.7
  , lottieUrl: Nothing
  , lottieReverse: true
  , scaleFactor: 1.0
  , liftPixels: 0.0
  , durationMs: 200.0
  }
