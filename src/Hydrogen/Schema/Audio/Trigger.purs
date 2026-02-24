-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // audio // trigger
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Audio Trigger — Event-based audio playback for UI feedback.
-- |
-- | ## Design Philosophy
-- |
-- | Audio triggers are declarative descriptions of when and how to play
-- | sounds in response to UI events. The runtime handles actual playback.
-- |
-- | ## Use Cases
-- |
-- | - Hover sounds (dog bark on hover over dog card)
-- | - Click feedback (button press sounds)
-- | - Enter/exit sounds (slide transitions)
-- | - Achievement sounds (gamification)
-- | - Error/success feedback
-- |
-- | ## Audio Behavior
-- |
-- | - Play once vs loop
-- | - Fade in/out
-- | - Volume control
-- | - Delay before playing
-- |
-- | ## Dependencies
-- |
-- | - Schema.Audio.Level (volume)
-- | - Schema.Dimension.Temporal (delay, fade duration)

module Hydrogen.Schema.Audio.Trigger
  ( -- * Audio Source
    AudioSource
      ( AudioUrl
      , AudioInline
      )
  , audioUrl
  , audioInline
  
  -- * Trigger Events
  , TriggerEvent
      ( OnHoverEnter
      , OnHoverLeave
      , OnClick
      , OnFocus
      , OnBlur
      , OnEnter
      , OnExit
      , OnLoad
      )
  
  -- * Audio Behavior
  , AudioBehavior
      ( PlayOnce
      , Loop
      , FadeIn
      , FadeOut
      , FadeInOut
      )
  
  -- * Audio Trigger
  , AudioTrigger
  , audioTrigger
  , audioTriggerSimple
  
  -- * Presets
  , hoverSound
  , clickSound
  , transitionSound
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // audio source
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Source of audio content
data AudioSource
  = AudioUrl String       -- ^ URL to audio file
  | AudioInline String    -- ^ Base64-encoded audio data

derive instance eqAudioSource :: Eq AudioSource
derive instance ordAudioSource :: Ord AudioSource

instance showAudioSource :: Show AudioSource where
  show (AudioUrl _) = "AudioUrl"
  show (AudioInline _) = "AudioInline"

-- | Create URL audio source
audioUrl :: String -> AudioSource
audioUrl = AudioUrl

-- | Create inline audio source
audioInline :: String -> AudioSource
audioInline = AudioInline

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // trigger events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Events that can trigger audio playback
data TriggerEvent
  = OnHoverEnter    -- ^ Mouse enters element
  | OnHoverLeave    -- ^ Mouse leaves element
  | OnClick         -- ^ Element clicked
  | OnFocus         -- ^ Element receives focus
  | OnBlur          -- ^ Element loses focus
  | OnEnter         -- ^ Element enters viewport / becomes active
  | OnExit          -- ^ Element exits viewport / becomes inactive
  | OnLoad          -- ^ Element finished loading

derive instance eqTriggerEvent :: Eq TriggerEvent
derive instance ordTriggerEvent :: Ord TriggerEvent

instance showTriggerEvent :: Show TriggerEvent where
  show OnHoverEnter = "hover-enter"
  show OnHoverLeave = "hover-leave"
  show OnClick = "click"
  show OnFocus = "focus"
  show OnBlur = "blur"
  show OnEnter = "enter"
  show OnExit = "exit"
  show OnLoad = "load"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // audio behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | How audio should be played
data AudioBehavior
  = PlayOnce      -- ^ Play once and stop
  | Loop          -- ^ Loop continuously
  | FadeIn        -- ^ Fade in from silence
  | FadeOut       -- ^ Fade out to silence
  | FadeInOut     -- ^ Fade in at start, fade out at end

derive instance eqAudioBehavior :: Eq AudioBehavior
derive instance ordAudioBehavior :: Ord AudioBehavior

instance showAudioBehavior :: Show AudioBehavior where
  show PlayOnce = "play-once"
  show Loop = "loop"
  show FadeIn = "fade-in"
  show FadeOut = "fade-out"
  show FadeInOut = "fade-in-out"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // audio trigger
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete audio trigger configuration
data AudioTrigger = AudioTriggerPlaceholder

derive instance eqAudioTrigger :: Eq AudioTrigger

instance showAudioTrigger :: Show AudioTrigger where
  show _ = "AudioTrigger"

-- | Create audio trigger (placeholder)
audioTrigger :: AudioTrigger
audioTrigger = AudioTriggerPlaceholder

-- | Simple audio trigger (placeholder)
audioTriggerSimple :: AudioTrigger
audioTriggerSimple = AudioTriggerPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hover sound preset (placeholder)
hoverSound :: AudioTrigger
hoverSound = AudioTriggerPlaceholder

-- | Click sound preset (placeholder)
clickSound :: AudioTrigger
clickSound = AudioTriggerPlaceholder

-- | Transition sound preset (placeholder)
transitionSound :: AudioTrigger
transitionSound = AudioTriggerPlaceholder
