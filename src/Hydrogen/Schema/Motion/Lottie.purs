-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // motion // lottie
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lottie — Animation data and playback configuration.
-- |
-- | ## Design Philosophy
-- |
-- | Lottie animations are JSON-based vector animations exported from
-- | After Effects via Bodymovin. This module provides:
-- | - Source management (URL or inline JSON)
-- | - Playback control (autoplay, loop, direction, speed)
-- | - Event-triggered playback
-- | - Segment playback (specific frame ranges)
-- |
-- | ## Use Cases
-- |
-- | - Loading spinners
-- | - Hover animations (dog starts playing when hovered)
-- | - Success/error feedback animations
-- | - Decorative illustrations
-- | - Icon animations
-- |
-- | ## Runtime Interpretation
-- |
-- | The runtime uses lottie-web or similar library to render.
-- | This module is pure data describing WHAT to animate.

module Hydrogen.Schema.Motion.Lottie
  ( -- * Lottie Source
    LottieSource
      ( LottieUrl
      , LottieInline
      )
  , lottieUrl
  , lottieInline
  
  -- * Playback Direction
  , PlaybackDirection
      ( Forward
      , Reverse
      , Alternate
      )
  
  -- * Playback Config
  , LottiePlayback
  , lottiePlayback
  , defaultPlayback
  , autoplayLoop
  , playOnce
  
  -- * Segment
  , LottieSegment
  , lottieSegment
  , fullAnimation
  
  -- * Trigger Config
  , LottieTrigger
      ( TriggerOnLoad
      , TriggerOnHover
      , TriggerOnClick
      , TriggerOnEnter
      , TriggerManual
      )
  
  -- * Lottie Animation
  , LottieAnimation
  , lottieAnimation
  , defaultLottie
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // lottie source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of Lottie animation data
data LottieSource
  = LottieUrl String      -- ^ URL to .json animation file
  | LottieInline String   -- ^ Inline JSON animation data

derive instance eqLottieSource :: Eq LottieSource
derive instance ordLottieSource :: Ord LottieSource

instance showLottieSource :: Show LottieSource where
  show (LottieUrl _) = "LottieUrl"
  show (LottieInline _) = "LottieInline"

-- | Create URL lottie source
lottieUrl :: String -> LottieSource
lottieUrl = LottieUrl

-- | Create inline lottie source
lottieInline :: String -> LottieSource
lottieInline = LottieInline

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // playback direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation playback direction
data PlaybackDirection
  = Forward     -- ^ Play from start to end
  | Reverse     -- ^ Play from end to start
  | Alternate   -- ^ Alternate between forward and reverse

derive instance eqPlaybackDirection :: Eq PlaybackDirection
derive instance ordPlaybackDirection :: Ord PlaybackDirection

instance showPlaybackDirection :: Show PlaybackDirection where
  show Forward = "forward"
  show Reverse = "reverse"
  show Alternate = "alternate"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // playback config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lottie playback configuration
data LottiePlayback = LottiePlaybackPlaceholder

derive instance eqLottiePlayback :: Eq LottiePlayback

instance showLottiePlayback :: Show LottiePlayback where
  show _ = "LottiePlayback"

-- | Create playback config (placeholder)
lottiePlayback :: LottiePlayback
lottiePlayback = LottiePlaybackPlaceholder

-- | Default playback (autoplay, loop, 1x speed)
defaultPlayback :: LottiePlayback
defaultPlayback = LottiePlaybackPlaceholder

-- | Autoplay with loop
autoplayLoop :: LottiePlayback
autoplayLoop = LottiePlaybackPlaceholder

-- | Play once and stop
playOnce :: LottiePlayback
playOnce = LottiePlaybackPlaceholder

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // segment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Segment of animation (frame range)
data LottieSegment = LottieSegmentPlaceholder

derive instance eqLottieSegment :: Eq LottieSegment

instance showLottieSegment :: Show LottieSegment where
  show _ = "LottieSegment"

-- | Create segment (placeholder)
lottieSegment :: LottieSegment
lottieSegment = LottieSegmentPlaceholder

-- | Full animation (all frames)
fullAnimation :: LottieSegment
fullAnimation = LottieSegmentPlaceholder

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lottie trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | When to start playing the animation
data LottieTrigger
  = TriggerOnLoad     -- ^ Play when element loads
  | TriggerOnHover    -- ^ Play when hovered
  | TriggerOnClick    -- ^ Play when clicked
  | TriggerOnEnter    -- ^ Play when element enters viewport
  | TriggerManual     -- ^ Don't auto-play, control programmatically

derive instance eqLottieTrigger :: Eq LottieTrigger
derive instance ordLottieTrigger :: Ord LottieTrigger

instance showLottieTrigger :: Show LottieTrigger where
  show TriggerOnLoad = "on-load"
  show TriggerOnHover = "on-hover"
  show TriggerOnClick = "on-click"
  show TriggerOnEnter = "on-enter"
  show TriggerManual = "manual"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // lottie animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Lottie animation configuration
data LottieAnimation = LottieAnimationPlaceholder

derive instance eqLottieAnimation :: Eq LottieAnimation

instance showLottieAnimation :: Show LottieAnimation where
  show _ = "LottieAnimation"

-- | Create lottie animation (placeholder)
lottieAnimation :: LottieAnimation
lottieAnimation = LottieAnimationPlaceholder

-- | Default lottie animation
defaultLottie :: LottieAnimation
defaultLottie = LottieAnimationPlaceholder
