-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // element // button // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonBehavior — interaction atoms for button response.
-- |
-- | ## Atoms Included
-- |
-- | - Haptic feedback (vibration on press/release)
-- | - Audio cues (click sounds)
-- | - Keyboard shortcuts
-- | - Long press threshold

module Hydrogen.Schema.Element.Button.Behavior
  ( -- * Button Behavior Record
    ButtonBehavior
  , defaultBehavior
    -- * Behavior Variants
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  , dangerBehavior
  , mediaBehavior
  , toggleBehavior
    -- * Accessors
  , behHapticPress
  , behHapticRelease
  , behAudioClick
  , behLongPressMs
  , behDebounceMs
    -- * Modifiers
  , setHapticPress
  , setHapticRelease
  , setAudioClick
  , setLongPressMs
  , setDebounceMs
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Haptic.Feedback
  ( ImpactFeedback(ImpactLight, ImpactMedium, ImpactHeavy)
  ) as Haptic

import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  , clickCue
  , confirmCue
  , warnCue
  ) as Haptic

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // button behavior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Behavior atoms for button interaction.
-- |
-- | Haptic, audio, and timing properties.
type ButtonBehavior =
  { -- Haptic
    hapticOnPress :: Maybe Haptic.ImpactFeedback    -- ^ Vibration on press
  , hapticOnRelease :: Maybe Haptic.ImpactFeedback  -- ^ Vibration on release
    -- Audio
  , audioOnClick :: Maybe Haptic.AudioCue           -- ^ Sound on click
    -- Timing
  , longPressThresholdMs :: Number                  -- ^ Long press threshold (ms)
  , debounceMs :: Number                            -- ^ Click debounce (ms)
  }

-- | Default button behavior.
-- |
-- | Light haptic on press, no audio, 500ms long press threshold.
defaultBehavior :: ButtonBehavior
defaultBehavior =
  { hapticOnPress: Just Haptic.ImpactLight
  , hapticOnRelease: Nothing
  , audioOnClick: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for press.
behHapticPress :: ButtonBehavior -> Maybe Haptic.ImpactFeedback
behHapticPress b = b.hapticOnPress

-- | Get haptic feedback for release.
behHapticRelease :: ButtonBehavior -> Maybe Haptic.ImpactFeedback
behHapticRelease b = b.hapticOnRelease

-- | Get audio cue for click.
behAudioClick :: ButtonBehavior -> Maybe Haptic.AudioCue
behAudioClick b = b.audioOnClick

-- | Get long press threshold in milliseconds.
behLongPressMs :: ButtonBehavior -> Number
behLongPressMs b = b.longPressThresholdMs

-- | Get debounce in milliseconds.
behDebounceMs :: ButtonBehavior -> Number
behDebounceMs b = b.debounceMs

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // behavior variants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Silent behavior (no haptics, no audio).
-- |
-- | For accessibility settings or quiet contexts.
silentBehavior :: ButtonBehavior
silentBehavior =
  { hapticOnPress: Nothing
  , hapticOnRelease: Nothing
  , audioOnClick: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  }

-- | Rich behavior (full haptic and audio feedback).
-- |
-- | Maximum sensory feedback for game/entertainment contexts.
richBehavior :: ButtonBehavior
richBehavior =
  { hapticOnPress: Just Haptic.ImpactMedium
  , hapticOnRelease: Just Haptic.ImpactLight
  , audioOnClick: Just Haptic.clickCue
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  }

-- | Reduced motion behavior.
-- |
-- | Respects prefers-reduced-motion, minimal haptics only.
reducedMotionBehavior :: ButtonBehavior
reducedMotionBehavior =
  { hapticOnPress: Just Haptic.ImpactLight
  , hapticOnRelease: Nothing
  , audioOnClick: Nothing
  , longPressThresholdMs: 500.0
  , debounceMs: 0.0
  }

-- | Danger action behavior.
-- |
-- | Heavy haptic warning, longer press threshold for confirmation.
dangerBehavior :: ButtonBehavior
dangerBehavior =
  { hapticOnPress: Just Haptic.ImpactHeavy
  , hapticOnRelease: Just Haptic.ImpactMedium
  , audioOnClick: Just Haptic.warnCue
  , longPressThresholdMs: 1000.0  -- Longer hold to confirm destructive action
  , debounceMs: 200.0  -- Prevent accidental double-click
  }

-- | Media control behavior.
-- |
-- | Quick response, subtle feedback, no debounce (rapid tapping allowed).
mediaBehavior :: ButtonBehavior
mediaBehavior =
  { hapticOnPress: Just Haptic.ImpactLight
  , hapticOnRelease: Nothing
  , audioOnClick: Nothing  -- Media controls shouldn't make extra sounds
  , longPressThresholdMs: 300.0  -- Faster long-press for seek/scrub
  , debounceMs: 0.0
  }

-- | Toggle button behavior.
-- |
-- | Distinct feedback on press to confirm state change.
toggleBehavior :: ButtonBehavior
toggleBehavior =
  { hapticOnPress: Just Haptic.ImpactMedium
  , hapticOnRelease: Nothing
  , audioOnClick: Just Haptic.confirmCue
  , longPressThresholdMs: 500.0
  , debounceMs: 100.0  -- Small debounce to prevent toggle flicker
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // modifiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set haptic press feedback.
setHapticPress :: Haptic.ImpactFeedback -> ButtonBehavior -> ButtonBehavior
setHapticPress h b = b { hapticOnPress = Just h }

-- | Set haptic release feedback.
setHapticRelease :: Haptic.ImpactFeedback -> ButtonBehavior -> ButtonBehavior
setHapticRelease h b = b { hapticOnRelease = Just h }

-- | Set audio click cue.
setAudioClick :: Haptic.AudioCue -> ButtonBehavior -> ButtonBehavior
setAudioClick a b = b { audioOnClick = Just a }

-- | Set long press threshold (bounded 100-3000ms).
setLongPressMs :: Number -> ButtonBehavior -> ButtonBehavior
setLongPressMs ms b = b { longPressThresholdMs = Bounded.clampNumber 100.0 3000.0 ms }

-- | Set debounce (bounded 0-500ms).
setDebounceMs :: Number -> ButtonBehavior -> ButtonBehavior
setDebounceMs ms b = b { debounceMs = Bounded.clampNumber 0.0 500.0 ms }
