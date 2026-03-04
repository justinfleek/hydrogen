-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // element // knob // behavior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KnobBehavior — Interaction atoms for rotational knob controls.
-- |
-- | ## Design Philosophy
-- |
-- | Knob behavior is more complex than slider behavior:
-- | - Multiple drag modes (circular vs linear)
-- | - Fine control modifiers (Shift for precision)
-- | - Bipolar center detent (snap to center for pan knobs)
-- | - MIDI CC mapping (DAW integration)
-- | - Safety confirmation (medical domain)
-- |
-- | ## Drag Modes
-- |
-- | - **Circular**: Rotate around knob center (classic physical knob)
-- | - **LinearVertical**: Vertical mouse movement changes value (Ableton style)
-- | - **LinearHorizontal**: Horizontal mouse movement changes value
-- | - **Angular**: Track angle from center (most precise)
-- |
-- | ## Graded Monad Integration
-- |
-- | Behavior atoms track co-effects:
-- | - MIDI mapping requires hardware access (CoEffectMIDI)
-- | - Audio cues require audio context (CoEffectAudio)
-- | - Haptic feedback requires device capability (CoEffectHaptic)
-- |
-- | ## Verified Atoms
-- |
-- | - ImpactFeedback, SelectionFeedback (Haptic.Feedback)
-- | - AudioCue (Haptic.Event)
-- | - Milliseconds (Dimension.Temporal)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Haptic.Feedback (haptic types)
-- | - Hydrogen.Schema.Haptic.Event (audio cues)
-- | - Hydrogen.Schema.Dimension.Temporal (timing)
-- | - Hydrogen.Schema.Bounded (value clamping)

module Hydrogen.Schema.Element.Knob.Behavior
  ( -- * Drag Mode
    DragMode
      ( DragCircular
      , DragLinearVertical
      , DragLinearHorizontal
      , DragAngular
      )
  , isDragLinear
  
  -- * Snap Behavior
  , SnapBehavior
      ( SnapNone
      , SnapToDefault
      , SnapToCenter
      , SnapToSteps
      , SnapToDetent
      )
  
  -- * MIDI Configuration
  , MIDIConfig
  , midiDisabled
  , midiCC
  , midiNRPN
  
  -- * Knob Behavior Record
  , KnobBehavior
  , defaultBehavior
  , silentBehavior
  , richBehavior
  , reducedMotionBehavior
  , dawBehavior
  , medicalBehavior
  , gameBehavior
  
  -- * Behavior Accessors
  , getDragMode
  , getSensitivity
  , getFineSensitivity
  , getSnapBehavior
  , getDiscreteSteps
  , wrapAround
  , hasHaptics
  , hasAudio
  , getMIDIConfig
  
  -- * Behavior Modifiers
  , setDragMode
  , setSensitivity
  , setFineSensitivity
  , setSnapBehavior
  , setDiscreteSteps
  , setWrapAround
  , setHapticOnDrag
  , setHapticOnStep
  , setHapticOnDetent
  , setHapticOnBoundary
  , setAudioOnChange
  , setAudioOnDetent
  , setMIDIConfig
  , enableHaptics
  , disableHaptics
  , enableAudio
  , disableAudio
  , enableReducedMotion
  
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
  , class Ord
  , class Show
  , show
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  , (==)
  , (&&)
  , (||)
  , (>)
  , (<)
  , (>=)
  , (<=)
  , not
  )

import Prim (Boolean, Int, Number)

import Data.Maybe (Maybe(Just, Nothing))
import Data.Maybe (isJust) as Maybe

import Hydrogen.Schema.Haptic.Feedback
  ( ImpactFeedback
      ( ImpactLight
      , ImpactMedium
      , ImpactHeavy
      , ImpactSoft
      , ImpactRigid
      )
  , SelectionFeedback
      ( SelectionTick
      , SelectionStart
      , SelectionEnd
      )
  , NotificationFeedback
      ( NotifySuccess
      , NotifyWarning
      , NotifyError
      )
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

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // drag mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag interaction mode.
-- |
-- | Different modes suit different workflows:
-- | - Circular: Most intuitive for physical knob metaphor
-- | - LinearVertical: Preferred in DAWs (Ableton, Logic)
-- | - LinearHorizontal: Good for horizontal layouts
-- | - Angular: Most precise for fine adjustment
data DragMode
  = DragCircular         -- ^ Rotate around knob center
  | DragLinearVertical   -- ^ Vertical movement = value change
  | DragLinearHorizontal -- ^ Horizontal movement = value change
  | DragAngular          -- ^ Track angle from center

derive instance eqDragMode :: Eq DragMode
derive instance ordDragMode :: Ord DragMode

instance showDragMode :: Show DragMode where
  show DragCircular = "circular"
  show DragLinearVertical = "linear-vertical"
  show DragLinearHorizontal = "linear-horizontal"
  show DragAngular = "angular"

-- | Is this a linear (non-circular) drag mode?
isDragLinear :: DragMode -> Boolean
isDragLinear DragLinearVertical = true
isDragLinear DragLinearHorizontal = true
isDragLinear _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // snap behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snap behavior for knob values.
-- |
-- | - None: Continuous, no snapping
-- | - ToDefault: Double-click resets to default value
-- | - ToCenter: Magnetic snap to center (for bipolar knobs like pan)
-- | - ToSteps: Snap to discrete step values
-- | - ToDetent: Snap to predefined detent positions
data SnapBehavior
  = SnapNone           -- ^ No snapping (continuous)
  | SnapToDefault      -- ^ Double-click resets
  | SnapToCenter       -- ^ Magnetic center (pan knobs)
  | SnapToSteps        -- ^ Discrete steps only
  | SnapToDetent       -- ^ Predefined detent positions

derive instance eqSnapBehavior :: Eq SnapBehavior
derive instance ordSnapBehavior :: Ord SnapBehavior

instance showSnapBehavior :: Show SnapBehavior where
  show SnapNone = "none"
  show SnapToDefault = "default"
  show SnapToCenter = "center"
  show SnapToSteps = "steps"
  show SnapToDetent = "detent"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // midi configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | MIDI configuration for DAW integration.
-- |
-- | - channel: MIDI channel (1-16)
-- | - ccNumber: Control Change number (0-127)
-- | - nrpnNumber: NRPN number for high-resolution control (optional)
-- | - learn: Whether MIDI learn is active
type MIDIConfig =
  { enabled :: Boolean       -- ^ Is MIDI mapping active?
  , channel :: Int           -- ^ MIDI channel (1-16)
  , ccNumber :: Maybe Int    -- ^ CC number (0-127)
  , nrpnNumber :: Maybe Int  -- ^ NRPN for 14-bit precision
  , learn :: Boolean         -- ^ MIDI learn mode active
  }

-- | MIDI disabled (no mapping).
midiDisabled :: MIDIConfig
midiDisabled =
  { enabled: false
  , channel: 1
  , ccNumber: Nothing
  , nrpnNumber: Nothing
  , learn: false
  }

-- | MIDI CC mapping.
midiCC :: Int -> Int -> MIDIConfig
midiCC channel cc =
  { enabled: true
  , channel: Bounded.clampInt 1 16 channel
  , ccNumber: Just (Bounded.clampInt 0 127 cc)
  , nrpnNumber: Nothing
  , learn: false
  }

-- | MIDI NRPN mapping (14-bit precision).
midiNRPN :: Int -> Int -> MIDIConfig
midiNRPN channel nrpn =
  { enabled: true
  , channel: Bounded.clampInt 1 16 channel
  , ccNumber: Nothing
  , nrpnNumber: Just (Bounded.clampInt 0 16383 nrpn)
  , learn: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // knob behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete knob behavior configuration.
-- |
-- | All timing values use Milliseconds.
-- | All sensitivities are degrees per pixel (or per unit drag).
type KnobBehavior =
  { -- Drag interaction
    dragMode :: DragMode                -- ^ How dragging changes value
  , sensitivity :: Number               -- ^ Degrees per pixel (normal)
  , fineSensitivity :: Number           -- ^ Degrees per pixel (with Shift)
  , fineModifier :: Boolean             -- ^ Is fine control available?
    -- Snapping
  , snap :: SnapBehavior                -- ^ Snap behavior
  , discreteSteps :: Maybe Int          -- ^ Number of discrete steps (Nothing = continuous)
  , centerDetentRange :: Number         -- ^ Range around center for magnetic snap (degrees)
    -- Wrapping
  , wrapAround :: Boolean               -- ^ Can value wrap past boundaries?
    -- Haptic feedback
  , hapticOnDrag :: Maybe ImpactFeedback      -- ^ Feedback while dragging
  , hapticOnStep :: Maybe ImpactFeedback      -- ^ Feedback at step boundaries
  , hapticOnDetent :: Maybe ImpactFeedback    -- ^ Feedback at detent points
  , hapticOnBoundary :: Maybe ImpactFeedback  -- ^ Feedback at min/max
    -- Audio feedback
  , audioOnChange :: Maybe AudioCue     -- ^ Sound on value change
  , audioOnDetent :: Maybe AudioCue     -- ^ Sound at detent points
    -- Timing
  , transitionDuration :: Milliseconds  -- ^ Animation duration
  , debounceDelay :: Milliseconds       -- ^ Value change debounce
    -- Accessibility
  , reducedMotion :: Boolean            -- ^ Respect prefers-reduced-motion
    -- Keyboard
  , keyboardStep :: Number              -- ^ Step per arrow key press
  , keyboardPageStep :: Number          -- ^ Step per Page Up/Down
    -- MIDI
  , midi :: MIDIConfig                  -- ^ MIDI CC/NRPN mapping
    -- Safety (medical)
  , confirmDangerous :: Boolean         -- ^ Require confirmation for dangerous values
  }

-- | Default knob behavior.
defaultBehavior :: KnobBehavior
defaultBehavior =
  { dragMode: DragLinearVertical        -- DAW-style vertical drag
  , sensitivity: 1.0                    -- 1 degree per pixel
  , fineSensitivity: 0.1                -- 0.1 degree per pixel with Shift
  , fineModifier: true
  , snap: SnapToDefault
  , discreteSteps: Nothing
  , centerDetentRange: 5.0              -- 5 degrees magnetic zone
  , wrapAround: false
  , hapticOnDrag: Just ImpactLight
  , hapticOnStep: Nothing
  , hapticOnDetent: Just ImpactMedium
  , hapticOnBoundary: Just ImpactHeavy
  , audioOnChange: Nothing
  , audioOnDetent: Nothing
  , transitionDuration: Milliseconds 100.0
  , debounceDelay: Milliseconds 16.0    -- ~60fps
  , reducedMotion: false
  , keyboardStep: 1.0
  , keyboardPageStep: 10.0
  , midi: midiDisabled
  , confirmDangerous: false
  }

-- | Silent behavior (no haptics, no audio).
silentBehavior :: KnobBehavior
silentBehavior = defaultBehavior
  { hapticOnDrag = Nothing
  , hapticOnStep = Nothing
  , hapticOnDetent = Nothing
  , hapticOnBoundary = Nothing
  , audioOnChange = Nothing
  , audioOnDetent = Nothing
  }

-- | Rich behavior (full haptics and audio).
richBehavior :: KnobBehavior
richBehavior = defaultBehavior
  { hapticOnDrag = Just ImpactLight
  , hapticOnStep = Just ImpactSoft
  , hapticOnDetent = Just ImpactMedium
  , hapticOnBoundary = Just ImpactHeavy
  , audioOnChange = Just (audioCue "tick" 0.3 1.0 0.0)
  , audioOnDetent = Just (audioCue "detent" 0.5 1.0 0.0)
  }

-- | Reduced motion behavior (accessibility).
reducedMotionBehavior :: KnobBehavior
reducedMotionBehavior = defaultBehavior
  { transitionDuration = Milliseconds 0.0
  , reducedMotion = true
  }

-- | DAW-optimized behavior.
-- |
-- | - Linear vertical drag (Ableton style)
-- | - Fine control with Shift
-- | - Double-click to reset
-- | - MIDI learn ready
dawBehavior :: KnobBehavior
dawBehavior = defaultBehavior
  { dragMode = DragLinearVertical
  , sensitivity = 0.5                   -- Slower, more precise
  , fineSensitivity = 0.05              -- Very fine with Shift
  , fineModifier = true
  , snap = SnapToDefault
  , discreteSteps = Nothing
  , hapticOnDrag = Nothing              -- DAWs usually don't have haptics
  , hapticOnStep = Nothing
  , hapticOnDetent = Nothing
  , hapticOnBoundary = Nothing
  , midi = midiDisabled                 -- Ready for MIDI learn
  }

-- | Medical-grade behavior.
-- |
-- | - Discrete steps only
-- | - Confirmation for dangerous values
-- | - Strong haptic feedback
-- | - No wrap-around
medicalBehavior :: KnobBehavior
medicalBehavior = defaultBehavior
  { dragMode = DragCircular             -- Physical knob feel
  , sensitivity = 2.0                   -- Faster response
  , fineSensitivity = 0.5
  , fineModifier = false                -- No fine control needed
  , snap = SnapToSteps
  , discreteSteps = Just 100            -- 100 discrete positions
  , wrapAround = false                  -- NEVER wrap (safety)
  , hapticOnStep = Just ImpactMedium    -- Click at every step
  , hapticOnDetent = Just ImpactHeavy   -- Strong at zone boundaries
  , hapticOnBoundary = Just ImpactRigid -- Maximum at limits
  , audioOnChange = Just (audioCue "step" 0.4 1.0 0.0)
  , confirmDangerous = true             -- Require confirmation in danger zone
  }

-- | Game UI behavior.
-- |
-- | - Circular drag (intuitive)
-- | - Full feedback
-- | - Fast response
-- | - Optional wrap-around
gameBehavior :: KnobBehavior
gameBehavior = richBehavior
  { dragMode = DragCircular
  , sensitivity = 1.5
  , fineSensitivity = 0.3
  , snap = SnapNone
  , wrapAround = true                   -- Can wrap for hue/rotation
  , transitionDuration = Milliseconds 50.0  -- Snappy
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get drag mode.
getDragMode :: KnobBehavior -> DragMode
getDragMode b = b.dragMode

-- | Get normal sensitivity (degrees per pixel).
getSensitivity :: KnobBehavior -> Number
getSensitivity b = b.sensitivity

-- | Get fine sensitivity (with Shift).
getFineSensitivity :: KnobBehavior -> Number
getFineSensitivity b = b.fineSensitivity

-- | Get snap behavior.
getSnapBehavior :: KnobBehavior -> SnapBehavior
getSnapBehavior b = b.snap

-- | Get discrete steps (if any).
getDiscreteSteps :: KnobBehavior -> Maybe Int
getDiscreteSteps b = b.discreteSteps

-- | Does this knob wrap around at boundaries?
wrapAround :: KnobBehavior -> Boolean
wrapAround b = b.wrapAround

-- | Are haptics enabled?
hasHaptics :: KnobBehavior -> Boolean
hasHaptics b = Maybe.isJust b.hapticOnDrag 
            || Maybe.isJust b.hapticOnStep
            || Maybe.isJust b.hapticOnDetent
            || Maybe.isJust b.hapticOnBoundary

-- | Is audio feedback enabled?
hasAudio :: KnobBehavior -> Boolean
hasAudio b = Maybe.isJust b.audioOnChange || Maybe.isJust b.audioOnDetent

-- | Get MIDI configuration.
getMIDIConfig :: KnobBehavior -> MIDIConfig
getMIDIConfig b = b.midi

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set drag mode.
setDragMode :: DragMode -> KnobBehavior -> KnobBehavior
setDragMode m b = b { dragMode = m }

-- | Set normal sensitivity (bounded 0.01-10.0).
setSensitivity :: Number -> KnobBehavior -> KnobBehavior
setSensitivity s b = b { sensitivity = Bounded.clampNumber 0.01 10.0 s }

-- | Set fine sensitivity (bounded 0.001-1.0).
setFineSensitivity :: Number -> KnobBehavior -> KnobBehavior
setFineSensitivity s b = b { fineSensitivity = Bounded.clampNumber 0.001 1.0 s }

-- | Set snap behavior.
setSnapBehavior :: SnapBehavior -> KnobBehavior -> KnobBehavior
setSnapBehavior s b = b { snap = s }

-- | Set discrete steps (bounded 2-1000).
setDiscreteSteps :: Maybe Int -> KnobBehavior -> KnobBehavior
setDiscreteSteps steps b = case steps of
  Nothing -> b { discreteSteps = Nothing }
  Just n -> b { discreteSteps = Just (Bounded.clampInt 2 1000 n) }

-- | Set wrap-around behavior.
setWrapAround :: Boolean -> KnobBehavior -> KnobBehavior
setWrapAround w b = b { wrapAround = w }

-- | Set haptic feedback while dragging.
setHapticOnDrag :: Maybe ImpactFeedback -> KnobBehavior -> KnobBehavior
setHapticOnDrag h b = b { hapticOnDrag = h }

-- | Set haptic feedback at step boundaries.
setHapticOnStep :: Maybe ImpactFeedback -> KnobBehavior -> KnobBehavior
setHapticOnStep h b = b { hapticOnStep = h }

-- | Set haptic feedback at detent points.
setHapticOnDetent :: Maybe ImpactFeedback -> KnobBehavior -> KnobBehavior
setHapticOnDetent h b = b { hapticOnDetent = h }

-- | Set haptic feedback at min/max boundaries.
setHapticOnBoundary :: Maybe ImpactFeedback -> KnobBehavior -> KnobBehavior
setHapticOnBoundary h b = b { hapticOnBoundary = h }

-- | Set audio cue on value change.
setAudioOnChange :: Maybe AudioCue -> KnobBehavior -> KnobBehavior
setAudioOnChange a b = b { audioOnChange = a }

-- | Set audio cue at detent points.
setAudioOnDetent :: Maybe AudioCue -> KnobBehavior -> KnobBehavior
setAudioOnDetent a b = b { audioOnDetent = a }

-- | Set MIDI configuration.
setMIDIConfig :: MIDIConfig -> KnobBehavior -> KnobBehavior
setMIDIConfig m b = b { midi = m }

-- | Enable all haptics with default feedback.
enableHaptics :: KnobBehavior -> KnobBehavior
enableHaptics b = b
  { hapticOnDrag = Just ImpactLight
  , hapticOnStep = Just ImpactSoft
  , hapticOnDetent = Just ImpactMedium
  , hapticOnBoundary = Just ImpactHeavy
  }

-- | Disable all haptics.
disableHaptics :: KnobBehavior -> KnobBehavior
disableHaptics b = b
  { hapticOnDrag = Nothing
  , hapticOnStep = Nothing
  , hapticOnDetent = Nothing
  , hapticOnBoundary = Nothing
  }

-- | Enable audio feedback with default cues.
enableAudio :: KnobBehavior -> KnobBehavior
enableAudio b = b
  { audioOnChange = Just (audioCue "tick" 0.3 1.0 0.0)
  , audioOnDetent = Just (audioCue "detent" 0.5 1.0 0.0)
  }

-- | Disable audio feedback.
disableAudio :: KnobBehavior -> KnobBehavior
disableAudio b = b
  { audioOnChange = Nothing
  , audioOnDetent = Nothing
  }

-- | Enable reduced motion mode.
enableReducedMotion :: KnobBehavior -> KnobBehavior
enableReducedMotion b = b
  { transitionDuration = Milliseconds 0.0
  , reducedMotion = true
  }
