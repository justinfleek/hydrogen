-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // playhead // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PlayheadBehavior — Interaction atoms for playhead response.
-- |
-- | ## Atoms Included
-- |
-- | - Haptic feedback (vibration on play/pause, scrub)
-- | - Audio cues (click sounds)
-- | - Timing (long press, debounce)
-- | - Scrub behavior (continuous feedback during drag)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Haptic.Feedback (ImpactFeedback, SelectionFeedback)
-- | - Hydrogen.Schema.Haptic.Event (AudioCue)
-- |
-- | ## Design Philosophy
-- |
-- | Behavior describes HOW the playhead responds, not what it shows.
-- | All timing uses bounded types — no unbounded Numbers.

module Hydrogen.Schema.Element.Playhead.Behavior
  ( -- * Playhead Behavior Record
    PlayheadBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  
  -- * Behavior Accessors
  , getHapticOnPlay
  , getHapticOnPause
  , getHapticOnScrub
  , getAudioOnClick
  , getLongPressMs
  , getDebounceMs
  
  -- * Behavior Modifiers
  , setHapticOnPlay
  , setHapticOnPause
  , setHapticOnScrub
  , setAudioOnClick
  , setLongPressMs
  , setDebounceMs
  , enableScrubHaptics
  , disableAllHaptics
  
  -- * Re-exports from Haptic
  , module Hydrogen.Schema.Haptic.Feedback
  , module Hydrogen.Schema.Haptic.Event
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded as Bounded

import Hydrogen.Schema.Haptic.Feedback
  ( ImpactFeedback(ImpactLight, ImpactMedium, ImpactHeavy)
  , SelectionFeedback(SelectionTick)
  , ContinuousFeedback
  , sliderFeedback
  )

import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  , audioCue
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // playhead behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete playhead behavior — all interaction properties.
-- |
-- | ## Bounded Values
-- |
-- | - longPressThresholdMs: 100-2000ms
-- | - debounceMs: 0-500ms
-- | - scrubFeedbackHz: 10-120Hz (via ContinuousFeedback)
-- |
-- | No unbounded timing. No negative durations.
type PlayheadBehavior =
  { -- Haptic on state changes
    hapticOnPlay :: Maybe ImpactFeedback      -- ^ Vibration when play pressed
  , hapticOnPause :: Maybe ImpactFeedback     -- ^ Vibration when pause pressed
  , hapticOnStop :: Maybe ImpactFeedback      -- ^ Vibration when stop pressed
  , hapticOnSeek :: Maybe ImpactFeedback      -- ^ Vibration when seeking completes
    -- Haptic during scrubbing
  , hapticOnScrub :: Maybe ContinuousFeedback -- ^ Continuous feedback during drag
  , hapticOnScrubTick :: Maybe SelectionFeedback -- ^ Tick at time markers
    -- Audio feedback
  , audioOnClick :: Maybe AudioCue            -- ^ Sound on button click
  , audioOnScrubStart :: Maybe AudioCue       -- ^ Sound when scrub starts
  , audioOnScrubEnd :: Maybe AudioCue         -- ^ Sound when scrub ends
    -- Timing
  , longPressThresholdMs :: Number            -- ^ Long press threshold (bounded 100-2000)
  , debounceMs :: Number                      -- ^ Click debounce (bounded 0-500)
    -- Keyboard
  , keyboardSeekSeconds :: Number             -- ^ Arrow key seek amount (bounded 1-60)
  , keyboardVolumeStep :: Number              -- ^ Arrow key volume step (bounded 0.01-0.25)
  }

-- | Default playhead behavior.
-- |
-- | Light haptic on play/pause, no scrub haptics, 500ms long press.
defaultBehavior :: PlayheadBehavior
defaultBehavior =
  { hapticOnPlay: Just ImpactLight
  , hapticOnPause: Just ImpactLight
  , hapticOnStop: Nothing
  , hapticOnSeek: Nothing
  , hapticOnScrub: Nothing
  , hapticOnScrubTick: Nothing
  , audioOnClick: Nothing
  , audioOnScrubStart: Nothing
  , audioOnScrubEnd: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  , keyboardSeekSeconds: 5.0
  , keyboardVolumeStep: 0.1
  }

-- | Silent behavior — no haptics, no audio.
-- |
-- | For accessibility or quiet contexts.
silentBehavior :: PlayheadBehavior
silentBehavior =
  { hapticOnPlay: Nothing
  , hapticOnPause: Nothing
  , hapticOnStop: Nothing
  , hapticOnSeek: Nothing
  , hapticOnScrub: Nothing
  , hapticOnScrubTick: Nothing
  , audioOnClick: Nothing
  , audioOnScrubStart: Nothing
  , audioOnScrubEnd: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  , keyboardSeekSeconds: 5.0
  , keyboardVolumeStep: 0.1
  }

-- | Rich behavior — full haptics and audio.
-- |
-- | For immersive media experiences.
richBehavior :: PlayheadBehavior
richBehavior =
  { hapticOnPlay: Just ImpactMedium
  , hapticOnPause: Just ImpactMedium
  , hapticOnStop: Just ImpactHeavy
  , hapticOnSeek: Just ImpactLight
  , hapticOnScrub: Just (sliderFeedback 0.3)
  , hapticOnScrubTick: Just SelectionTick
  , audioOnClick: Just (audioCue "ui_click" 0.3 1.0 0.0)
  , audioOnScrubStart: Just (audioCue "scrub_start" 0.2 1.0 0.0)
  , audioOnScrubEnd: Just (audioCue "scrub_end" 0.2 1.0 0.0)
  , longPressThresholdMs: 500.0
  , debounceMs: 50.0
  , keyboardSeekSeconds: 10.0
  , keyboardVolumeStep: 0.05
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for play.
getHapticOnPlay :: PlayheadBehavior -> Maybe ImpactFeedback
getHapticOnPlay b = b.hapticOnPlay

-- | Get haptic feedback for pause.
getHapticOnPause :: PlayheadBehavior -> Maybe ImpactFeedback
getHapticOnPause b = b.hapticOnPause

-- | Get continuous haptic feedback for scrubbing.
getHapticOnScrub :: PlayheadBehavior -> Maybe ContinuousFeedback
getHapticOnScrub b = b.hapticOnScrub

-- | Get audio cue for click.
getAudioOnClick :: PlayheadBehavior -> Maybe AudioCue
getAudioOnClick b = b.audioOnClick

-- | Get long press threshold in milliseconds (bounded 100-2000).
getLongPressMs :: PlayheadBehavior -> Number
getLongPressMs b = Bounded.clampNumber 100.0 2000.0 b.longPressThresholdMs

-- | Get debounce time in milliseconds (bounded 0-500).
getDebounceMs :: PlayheadBehavior -> Number
getDebounceMs b = Bounded.clampNumber 0.0 500.0 b.debounceMs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set haptic feedback for play.
setHapticOnPlay :: ImpactFeedback -> PlayheadBehavior -> PlayheadBehavior
setHapticOnPlay h b = b { hapticOnPlay = Just h }

-- | Set haptic feedback for pause.
setHapticOnPause :: ImpactFeedback -> PlayheadBehavior -> PlayheadBehavior
setHapticOnPause h b = b { hapticOnPause = Just h }

-- | Set continuous haptic feedback for scrubbing.
setHapticOnScrub :: ContinuousFeedback -> PlayheadBehavior -> PlayheadBehavior
setHapticOnScrub h b = b { hapticOnScrub = Just h }

-- | Set audio cue for click.
setAudioOnClick :: AudioCue -> PlayheadBehavior -> PlayheadBehavior
setAudioOnClick a b = b { audioOnClick = Just a }

-- | Set long press threshold (bounded 100-2000ms).
setLongPressMs :: Number -> PlayheadBehavior -> PlayheadBehavior
setLongPressMs ms b = b { longPressThresholdMs = Bounded.clampNumber 100.0 2000.0 ms }

-- | Set debounce time (bounded 0-500ms).
setDebounceMs :: Number -> PlayheadBehavior -> PlayheadBehavior
setDebounceMs ms b = b { debounceMs = Bounded.clampNumber 0.0 500.0 ms }

-- | Enable scrub haptics with default slider feedback.
enableScrubHaptics :: PlayheadBehavior -> PlayheadBehavior
enableScrubHaptics b = b
  { hapticOnScrub = Just (sliderFeedback 0.3)
  , hapticOnScrubTick = Just SelectionTick
  }

-- | Disable all haptic feedback.
disableAllHaptics :: PlayheadBehavior -> PlayheadBehavior
disableAllHaptics b = b
  { hapticOnPlay = Nothing
  , hapticOnPause = Nothing
  , hapticOnStop = Nothing
  , hapticOnSeek = Nothing
  , hapticOnScrub = Nothing
  , hapticOnScrubTick = Nothing
  }
