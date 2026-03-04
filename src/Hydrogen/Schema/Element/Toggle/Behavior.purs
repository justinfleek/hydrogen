-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // toggle // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ToggleBehavior — Interaction atoms for toggle/switch response.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - ImpactFeedback (Haptic.Feedback) — Tap feedback types
-- | - AudioCue (Haptic.Event) — Audio feedback
-- | - Milliseconds (Dimension.Temporal) — Verified timing
-- |
-- | ## Toggle Behavior Model
-- |
-- | A toggle responds to:
-- | - Click/tap: Toggle state
-- | - Keyboard (Space/Enter): Toggle state
-- | - Keyboard (ArrowLeft/ArrowRight): Set off/on directly
-- | - Long press: Optional (e.g., show tooltip)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Haptic.Feedback (ImpactFeedback)
-- | - Hydrogen.Schema.Haptic.Event (AudioCue)
-- | - Hydrogen.Schema.Dimension.Temporal (Milliseconds)

module Hydrogen.Schema.Element.Toggle.Behavior
  ( -- * Toggle Behavior Record
    ToggleBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  
  -- * Behavior Accessors
  , getHapticOnToggle
  , getAudioOnToggle
  , getTransitionDuration
  , getDebounceMs
  , isReducedMotion
  
  -- * Behavior Modifiers
  , setHapticOnToggle
  , setAudioOnToggle
  , setTransitionDuration
  , setDebounceMs
  , setReducedMotion
  , enableHaptics
  , disableHaptics
  , enableAudio
  , disableAudio
  
  -- * Re-exports
  , module Hydrogen.Schema.Haptic.Feedback
  , module Hydrogen.Schema.Haptic.Event
  , module Hydrogen.Schema.Dimension.Temporal
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
  )

import Hydrogen.Schema.Haptic.Event
  ( AudioCue
  , audioCue
  )

import Hydrogen.Schema.Dimension.Temporal
  ( Milliseconds(Milliseconds)
  , milliseconds
  , unwrapMilliseconds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // toggle behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete toggle behavior — all interaction properties.
-- |
-- | ## Verified Bounds
-- |
-- | - transitionDurationMs: bounded [0-2000] ms
-- | - debounceMs: bounded [0-500] ms
-- | - haptic feedback: via ImpactFeedback enum
-- | - audio cue: via AudioCue type
-- |
-- | ## Timing
-- |
-- | - transitionDuration: How long the thumb takes to slide
-- | - debounce: Minimum time between toggle actions (prevents double-tap)
-- |
-- | ## Accessibility
-- |
-- | - reducedMotion: When true, transition duration should be 0
-- | - Keyboard support is always enabled (Space, Enter, Arrow keys)
type ToggleBehavior =
  { -- Haptic feedback
    hapticOnToggle :: Maybe ImpactFeedback   -- ^ Vibration when toggled
  , hapticOnHover :: Maybe SelectionFeedback -- ^ Subtle tick on hover
    -- Audio feedback
  , audioOnToggle :: Maybe AudioCue          -- ^ Sound when toggled
    -- Timing
  , transitionDurationMs :: Milliseconds     -- ^ Thumb slide duration
  , debounceMs :: Milliseconds               -- ^ Minimum time between toggles
    -- Accessibility
  , reducedMotion :: Boolean                 -- ^ Respect prefers-reduced-motion
    -- Keyboard
  , keyboardArrows :: Boolean                -- ^ Arrow keys set on/off directly
  , keyboardSpaceToggle :: Boolean           -- ^ Space key toggles
  , keyboardEnterToggle :: Boolean           -- ^ Enter key toggles
  }

-- | Default toggle behavior.
-- |
-- | Light haptic, 200ms transition, no debounce, keyboard enabled.
defaultBehavior :: ToggleBehavior
defaultBehavior =
  { hapticOnToggle: Just ImpactLight
  , hapticOnHover: Nothing
  , audioOnToggle: Nothing
  , transitionDurationMs: milliseconds 200.0
  , debounceMs: milliseconds 0.0
  , reducedMotion: false
  , keyboardArrows: true
  , keyboardSpaceToggle: true
  , keyboardEnterToggle: true
  }

-- | Silent toggle behavior — no haptics, no audio.
-- |
-- | For quiet environments or accessibility preferences.
silentBehavior :: ToggleBehavior
silentBehavior = defaultBehavior
  { hapticOnToggle = Nothing
  , hapticOnHover = Nothing
  , audioOnToggle = Nothing
  }

-- | Rich toggle behavior — full haptics and audio.
-- |
-- | Medium haptic, click sound, hover tick.
richBehavior :: ToggleBehavior
richBehavior = defaultBehavior
  { hapticOnToggle = Just ImpactMedium
  , hapticOnHover = Just SelectionTick
  , audioOnToggle = Just (audioCue "toggle_click" 0.3 1.0 0.0)
  }

-- | Reduced motion behavior.
-- |
-- | Zero transition duration, respects prefers-reduced-motion.
reducedMotionBehavior :: ToggleBehavior
reducedMotionBehavior = defaultBehavior
  { transitionDurationMs = milliseconds 0.0
  , reducedMotion = true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for toggle action.
getHapticOnToggle :: ToggleBehavior -> Maybe ImpactFeedback
getHapticOnToggle b = b.hapticOnToggle

-- | Get audio cue for toggle action.
getAudioOnToggle :: ToggleBehavior -> Maybe AudioCue
getAudioOnToggle b = b.audioOnToggle

-- | Get transition duration in milliseconds (bounded 0-2000).
getTransitionDuration :: ToggleBehavior -> Milliseconds
getTransitionDuration b = 
  let (Milliseconds ms) = b.transitionDurationMs
  in milliseconds (Bounded.clampNumber 0.0 2000.0 ms)

-- | Get debounce time in milliseconds (bounded 0-500).
getDebounceMs :: ToggleBehavior -> Milliseconds
getDebounceMs b = 
  let (Milliseconds ms) = b.debounceMs
  in milliseconds (Bounded.clampNumber 0.0 500.0 ms)

-- | Is reduced motion enabled?
isReducedMotion :: ToggleBehavior -> Boolean
isReducedMotion b = b.reducedMotion

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set haptic feedback for toggle.
setHapticOnToggle :: ImpactFeedback -> ToggleBehavior -> ToggleBehavior
setHapticOnToggle h b = b { hapticOnToggle = Just h }

-- | Set audio cue for toggle.
setAudioOnToggle :: AudioCue -> ToggleBehavior -> ToggleBehavior
setAudioOnToggle a b = b { audioOnToggle = Just a }

-- | Set transition duration (bounded 0-2000ms).
setTransitionDuration :: Number -> ToggleBehavior -> ToggleBehavior
setTransitionDuration ms b = 
  b { transitionDurationMs = milliseconds (Bounded.clampNumber 0.0 2000.0 ms) }

-- | Set debounce time (bounded 0-500ms).
setDebounceMs :: Number -> ToggleBehavior -> ToggleBehavior
setDebounceMs ms b = 
  b { debounceMs = milliseconds (Bounded.clampNumber 0.0 500.0 ms) }

-- | Set reduced motion preference.
setReducedMotion :: Boolean -> ToggleBehavior -> ToggleBehavior
setReducedMotion r b = b { reducedMotion = r }

-- | Enable haptic feedback with default light impact.
enableHaptics :: ToggleBehavior -> ToggleBehavior
enableHaptics b = b { hapticOnToggle = Just ImpactLight }

-- | Disable all haptic feedback.
disableHaptics :: ToggleBehavior -> ToggleBehavior
disableHaptics b = b { hapticOnToggle = Nothing, hapticOnHover = Nothing }

-- | Enable audio feedback with default click sound.
enableAudio :: ToggleBehavior -> ToggleBehavior
enableAudio b = b { audioOnToggle = Just (audioCue "toggle_click" 0.3 1.0 0.0) }

-- | Disable all audio feedback.
disableAudio :: ToggleBehavior -> ToggleBehavior
disableAudio b = b { audioOnToggle = Nothing }
