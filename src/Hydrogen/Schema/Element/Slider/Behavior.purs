-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // slider // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SliderBehavior — Interaction atoms for slider response.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - ImpactFeedback (Haptic.Feedback) — Tap/drag feedback types
-- | - AudioCue (Haptic.Event) — Audio feedback
-- | - Milliseconds (Dimension.Temporal) — Verified timing
-- |
-- | ## Slider Behavior Model
-- |
-- | A slider responds to:
-- | - Drag: Primary interaction, thumb follows pointer
-- | - Click track: Jump to clicked position
-- | - Keyboard: Arrow keys for step increments
-- | - Scroll: Optional mouse wheel support
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Haptic.Feedback (ImpactFeedback)
-- | - Hydrogen.Schema.Haptic.Event (AudioCue)
-- | - Hydrogen.Schema.Dimension.Temporal (Milliseconds)

module Hydrogen.Schema.Element.Slider.Behavior
  ( -- * Slider Behavior Record
    SliderBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  , precisionBehavior
  
  -- * Behavior Accessors
  , getHapticOnDrag
  , getHapticOnStep
  , getAudioOnChange
  , getTransitionDuration
  , getDebounceMs
  , getStepSize
  , isReducedMotion
  , isClickTrackEnabled
  , isScrollEnabled
  
  -- * Behavior Modifiers
  , setHapticOnDrag
  , setHapticOnStep
  , setAudioOnChange
  , setTransitionDuration
  , setDebounceMs
  , setStepSize
  , setReducedMotion
  , enableClickTrack
  , disableClickTrack
  , enableScroll
  , disableScroll
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

import Prim (Boolean, Number)

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
--                                                           // slider behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete slider behavior — all interaction properties.
-- |
-- | ## Verified Bounds
-- |
-- | - transitionDurationMs: bounded [0-500] ms (for thumb animation)
-- | - debounceMs: bounded [0-100] ms (for value change events)
-- | - stepSize: bounded [0-1] (0 = continuous, >0 = discrete steps)
-- | - haptic feedback: via ImpactFeedback enum
-- | - audio cue: via AudioCue type
-- |
-- | ## Interaction Modes
-- |
-- | - Drag: Thumb follows pointer with optional haptic ticks
-- | - Click track: Jump to clicked position (can be disabled)
-- | - Keyboard: Arrow keys increment/decrement by stepSize
-- | - Scroll: Mouse wheel changes value (optional)
-- |
-- | ## Accessibility
-- |
-- | - reducedMotion: When true, transition duration should be 0
-- | - Keyboard support is always enabled (Arrow keys)
type SliderBehavior =
  { -- Haptic feedback
    hapticOnDrag :: Maybe SelectionFeedback   -- ^ Tick while dragging
  , hapticOnStep :: Maybe ImpactFeedback      -- ^ Impact at discrete steps
  , hapticOnBoundary :: Maybe ImpactFeedback  -- ^ Impact when hitting min/max
    -- Audio feedback
  , audioOnChange :: Maybe AudioCue           -- ^ Sound on value change
  , audioOnBoundary :: Maybe AudioCue         -- ^ Sound when hitting min/max
    -- Timing
  , transitionDurationMs :: Milliseconds      -- ^ Thumb animation duration
  , debounceMs :: Milliseconds                -- ^ Value change event debounce
    -- Stepping
  , stepSize :: Number                        -- ^ Step increment (0 = continuous)
  , snapToStep :: Boolean                     -- ^ Snap to nearest step while dragging
    -- Interaction modes
  , clickTrackEnabled :: Boolean              -- ^ Allow clicking track to jump
  , scrollEnabled :: Boolean                  -- ^ Allow mouse wheel to change value
  , keyboardArrows :: Boolean                 -- ^ Arrow keys increment/decrement
    -- Accessibility
  , reducedMotion :: Boolean                  -- ^ Respect prefers-reduced-motion
  }

-- | Default slider behavior.
-- |
-- | Light haptic on drag, 100ms transition, continuous values.
defaultBehavior :: SliderBehavior
defaultBehavior =
  { hapticOnDrag: Just SelectionTick
  , hapticOnStep: Nothing
  , hapticOnBoundary: Just ImpactMedium
  , audioOnChange: Nothing
  , audioOnBoundary: Nothing
  , transitionDurationMs: milliseconds 100.0
  , debounceMs: milliseconds 16.0           -- ~60fps
  , stepSize: 0.0                           -- Continuous
  , snapToStep: false
  , clickTrackEnabled: true
  , scrollEnabled: false
  , keyboardArrows: true
  , reducedMotion: false
  }

-- | Silent slider behavior — no haptics, no audio.
-- |
-- | For quiet environments or accessibility preferences.
silentBehavior :: SliderBehavior
silentBehavior = defaultBehavior
  { hapticOnDrag = Nothing
  , hapticOnStep = Nothing
  , hapticOnBoundary = Nothing
  , audioOnChange = Nothing
  , audioOnBoundary = Nothing
  }

-- | Rich slider behavior — full haptics and audio.
-- |
-- | Tick while dragging, impact at boundaries, subtle change sound.
richBehavior :: SliderBehavior
richBehavior = defaultBehavior
  { hapticOnDrag = Just SelectionTick
  , hapticOnStep = Just ImpactLight
  , hapticOnBoundary = Just ImpactHeavy
  , audioOnChange = Just (audioCue "slider_tick" 0.1 1.0 0.0)
  , audioOnBoundary = Just (audioCue "slider_boundary" 0.3 1.0 0.0)
  }

-- | Reduced motion behavior.
-- |
-- | Zero transition duration, respects prefers-reduced-motion.
reducedMotionBehavior :: SliderBehavior
reducedMotionBehavior = defaultBehavior
  { transitionDurationMs = milliseconds 0.0
  , reducedMotion = true
  }

-- | Precision slider behavior — for fine-grained control.
-- |
-- | Slower response, higher debounce, scroll enabled.
precisionBehavior :: SliderBehavior
precisionBehavior = defaultBehavior
  { transitionDurationMs = milliseconds 50.0
  , debounceMs = milliseconds 50.0
  , scrollEnabled = true
  , stepSize = 0.01                          -- 1% steps
  , snapToStep = true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get haptic feedback for drag action.
getHapticOnDrag :: SliderBehavior -> Maybe SelectionFeedback
getHapticOnDrag b = b.hapticOnDrag

-- | Get haptic feedback for step transitions.
getHapticOnStep :: SliderBehavior -> Maybe ImpactFeedback
getHapticOnStep b = b.hapticOnStep

-- | Get audio cue for value change.
getAudioOnChange :: SliderBehavior -> Maybe AudioCue
getAudioOnChange b = b.audioOnChange

-- | Get transition duration in milliseconds (bounded 0-500).
getTransitionDuration :: SliderBehavior -> Milliseconds
getTransitionDuration b = 
  let (Milliseconds ms) = b.transitionDurationMs
  in milliseconds (Bounded.clampNumber 0.0 500.0 ms)

-- | Get debounce time in milliseconds (bounded 0-100).
getDebounceMs :: SliderBehavior -> Milliseconds
getDebounceMs b = 
  let (Milliseconds ms) = b.debounceMs
  in milliseconds (Bounded.clampNumber 0.0 100.0 ms)

-- | Get step size (bounded 0-1).
getStepSize :: SliderBehavior -> Number
getStepSize b = Bounded.clampNumber 0.0 1.0 b.stepSize

-- | Is reduced motion enabled?
isReducedMotion :: SliderBehavior -> Boolean
isReducedMotion b = b.reducedMotion

-- | Is click-to-jump on track enabled?
isClickTrackEnabled :: SliderBehavior -> Boolean
isClickTrackEnabled b = b.clickTrackEnabled

-- | Is mouse wheel scrolling enabled?
isScrollEnabled :: SliderBehavior -> Boolean
isScrollEnabled b = b.scrollEnabled

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set haptic feedback for drag.
setHapticOnDrag :: SelectionFeedback -> SliderBehavior -> SliderBehavior
setHapticOnDrag h b = b { hapticOnDrag = Just h }

-- | Set haptic feedback for step transitions.
setHapticOnStep :: ImpactFeedback -> SliderBehavior -> SliderBehavior
setHapticOnStep h b = b { hapticOnStep = Just h }

-- | Set audio cue for value change.
setAudioOnChange :: AudioCue -> SliderBehavior -> SliderBehavior
setAudioOnChange a b = b { audioOnChange = Just a }

-- | Set transition duration (bounded 0-500ms).
setTransitionDuration :: Number -> SliderBehavior -> SliderBehavior
setTransitionDuration ms b = 
  b { transitionDurationMs = milliseconds (Bounded.clampNumber 0.0 500.0 ms) }

-- | Set debounce time (bounded 0-100ms).
setDebounceMs :: Number -> SliderBehavior -> SliderBehavior
setDebounceMs ms b = 
  b { debounceMs = milliseconds (Bounded.clampNumber 0.0 100.0 ms) }

-- | Set step size (bounded 0-1).
setStepSize :: Number -> SliderBehavior -> SliderBehavior
setStepSize s b = b { stepSize = Bounded.clampNumber 0.0 1.0 s }

-- | Set reduced motion preference.
setReducedMotion :: Boolean -> SliderBehavior -> SliderBehavior
setReducedMotion r b = b { reducedMotion = r }

-- | Enable click-to-jump on track.
enableClickTrack :: SliderBehavior -> SliderBehavior
enableClickTrack b = b { clickTrackEnabled = true }

-- | Disable click-to-jump on track.
disableClickTrack :: SliderBehavior -> SliderBehavior
disableClickTrack b = b { clickTrackEnabled = false }

-- | Enable mouse wheel scrolling.
enableScroll :: SliderBehavior -> SliderBehavior
enableScroll b = b { scrollEnabled = true }

-- | Disable mouse wheel scrolling.
disableScroll :: SliderBehavior -> SliderBehavior
disableScroll b = b { scrollEnabled = false }

-- | Enable haptic feedback with default settings.
enableHaptics :: SliderBehavior -> SliderBehavior
enableHaptics b = b 
  { hapticOnDrag = Just SelectionTick
  , hapticOnBoundary = Just ImpactMedium
  }

-- | Disable all haptic feedback.
disableHaptics :: SliderBehavior -> SliderBehavior
disableHaptics b = b 
  { hapticOnDrag = Nothing
  , hapticOnStep = Nothing
  , hapticOnBoundary = Nothing
  }

-- | Enable audio feedback with default click sound.
enableAudio :: SliderBehavior -> SliderBehavior
enableAudio b = b { audioOnChange = Just (audioCue "slider_tick" 0.1 1.0 0.0) }

-- | Disable all audio feedback.
disableAudio :: SliderBehavior -> SliderBehavior
disableAudio b = b { audioOnChange = Nothing, audioOnBoundary = Nothing }
