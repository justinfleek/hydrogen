-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // reactive // hover-effect/audio
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HoverAudio — Audio triggered on hover.
-- |
-- | ## Design Philosophy
-- |
-- | Describes sounds to play when hovering over an element:
-- | - Enter sound (mouse enters)
-- | - Leave sound (mouse exits)
-- | - Loop while hovering
-- |
-- | ## Audio Sources
-- |
-- | Audio can come from URL or inline base64 data.
-- | Volume is normalized 0.0 to 1.0.
-- |
-- | ## Fade Behavior
-- |
-- | Fades smooth out abrupt audio starts/stops:
-- | - fadeInMs: gradual volume increase on enter
-- | - fadeOutMs: gradual volume decrease on leave
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Dog card plays bark on hover
-- | dogBark = hoverAudioEnter (HoverAudioUrl "/sounds/bark.mp3") 0.5
-- |
-- | -- Ambient loop while hovering
-- | ambientHover = hoverAudioLoop (HoverAudioUrl "/sounds/ambient.ogg") 0.3
-- | ```

module Hydrogen.Schema.Reactive.HoverEffect.Audio
  ( HoverAudio(..)
  , HoverAudioSource(..)
  , hoverAudio
  , noHoverAudio
  , hoverAudioEnter
  , hoverAudioEnterLeave
  , hoverAudioLoop
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // audio source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio source for hover sounds
data HoverAudioSource
  = HoverAudioNone                    -- ^ No audio
  | HoverAudioUrl String              -- ^ URL to audio file
  | HoverAudioInline String           -- ^ Base64-encoded audio data

derive instance eqHoverAudioSource :: Eq HoverAudioSource

instance showHoverAudioSource :: Show HoverAudioSource where
  show HoverAudioNone = "none"
  show (HoverAudioUrl _) = "url"
  show (HoverAudioInline _) = "inline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hover audio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Audio triggered on hover
newtype HoverAudio = HoverAudio
  { enterSound :: HoverAudioSource     -- ^ Sound on mouse enter
  , leaveSound :: HoverAudioSource     -- ^ Sound on mouse leave  
  , loopSound :: HoverAudioSource      -- ^ Sound looped while hovering
  , volume :: Number                   -- ^ Master volume (0.0 to 1.0)
  , fadeInMs :: Number                 -- ^ Fade in duration (milliseconds)
  , fadeOutMs :: Number                -- ^ Fade out duration (milliseconds)
  }

derive instance eqHoverAudio :: Eq HoverAudio

instance showHoverAudio :: Show HoverAudio where
  show (HoverAudio a) = 
    "HoverAudio(vol:" <> show a.volume <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create hover audio with full configuration
hoverAudio 
  :: { enterSound :: HoverAudioSource
     , leaveSound :: HoverAudioSource
     , loopSound :: HoverAudioSource
     , volume :: Number
     , fadeInMs :: Number
     , fadeOutMs :: Number
     }
  -> HoverAudio
hoverAudio cfg = HoverAudio
  { enterSound: cfg.enterSound
  , leaveSound: cfg.leaveSound
  , loopSound: cfg.loopSound
  , volume: clampVolume cfg.volume
  , fadeInMs: clampMs cfg.fadeInMs
  , fadeOutMs: clampMs cfg.fadeOutMs
  }
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v
    clampMs ms
      | ms < 0.0 = 0.0
      | otherwise = ms

-- | No hover audio
noHoverAudio :: HoverAudio
noHoverAudio = HoverAudio
  { enterSound: HoverAudioNone
  , leaveSound: HoverAudioNone
  , loopSound: HoverAudioNone
  , volume: 0.0
  , fadeInMs: 0.0
  , fadeOutMs: 0.0
  }

-- | Play sound on hover enter only
hoverAudioEnter :: HoverAudioSource -> Number -> HoverAudio
hoverAudioEnter src vol = HoverAudio
  { enterSound: src
  , leaveSound: HoverAudioNone
  , loopSound: HoverAudioNone
  , volume: vol
  , fadeInMs: 50.0
  , fadeOutMs: 0.0
  }

-- | Play sound on both enter and leave
hoverAudioEnterLeave :: HoverAudioSource -> HoverAudioSource -> Number -> HoverAudio
hoverAudioEnterLeave enter leave vol = HoverAudio
  { enterSound: enter
  , leaveSound: leave
  , loopSound: HoverAudioNone
  , volume: vol
  , fadeInMs: 50.0
  , fadeOutMs: 50.0
  }

-- | Loop sound while hovering
hoverAudioLoop :: HoverAudioSource -> Number -> HoverAudio
hoverAudioLoop src vol = HoverAudio
  { enterSound: HoverAudioNone
  , leaveSound: HoverAudioNone
  , loopSound: src
  , volume: vol
  , fadeInMs: 100.0
  , fadeOutMs: 100.0
  }
