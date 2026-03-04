-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // element // knob // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | KnobState — State atoms for rotational knob controls.
-- |
-- | ## Design Philosophy
-- |
-- | Knobs are rotational continuous controls — the circular cousin of sliders.
-- | Unlike sliders (linear left-to-right), knobs map VALUE to ANGLE.
-- |
-- | ## Graded Monad Integration
-- |
-- | Knob state participates in the Orchard co-effect algebra:
-- | - Pure knobs require nothing (CoEffectNone)
-- | - MIDI-mapped knobs require HW access (CoEffectMIDI)
-- | - Automated knobs require timeline context (CoEffectTimeline)
-- |
-- | ## Domain-Specific State Machines
-- |
-- | Each domain has fundamentally different state requirements:
-- | - **Hospital**: Safety confirmation state, warning zone active
-- | - **Game**: Animation state, particle emission triggers
-- | - **DAW**: Automation mode (manual/read/write/touch/latch)
-- | - **Mograph**: Keyframe presence, expression binding
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Degrees (Geometry.Angle) — Angular position [0, 360)
-- | - Progress (Temporal.Progress) — Normalized value [0, 1]
-- | - Range (Dimension.Range) — Value bounds with invariant min <= max
-- | - Flags (Reactive.Flags) — Interaction state
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Angle (Degrees, angular math)
-- | - Hydrogen.Schema.Temporal.Progress (normalized progress)
-- | - Hydrogen.Schema.Dimension.Range (value bounds)
-- | - Hydrogen.Schema.Reactive.Flags (UI state flags)
-- | - Hydrogen.Schema.Motion.Keyframe (keyframe state for mograph)

module Hydrogen.Schema.Element.Knob.State
  ( -- * Automation State (DAW domain)
    AutomationMode
      ( AutoManual
      , AutoRead
      , AutoWrite
      , AutoTouch
      , AutoLatch
      )
  , isAutomationActive
  
  -- * Keyframe State (Mograph domain)
  , KeyframePresence
      ( KeyframeNone
      , KeyframePresent
      , KeyframePending
      )
  , hasKeyframe
  
  -- * Safety State (Medical domain)
  , SafetyZone
      ( ZoneSafe
      , ZoneCaution
      , ZoneDanger
      )
  , isSafeValue
  , requiresConfirmation
  
  -- * Knob Value Sum Type
  , KnobValue
      ( ValueAngle
      , ValueVolume
      , ValuePan
      , ValueFrequency
      , ValueRate
      , ValuePercent
      , ValueBipolar
      , ValueMedical
      )
  , toProgress
  , fromProgress
  , isBipolar
  
  -- * Knob Element State Record
  , KnobElementState
  , defaultState
  , volumeState
  , panState
  , frequencyState
  , rateState
  , rotationState
  , medicalState
  
  -- * State Accessors
  , getValue
  , getAngle
  , getProgressNormalized
  , isDisabled
  , isFocused
  , isHovered
  , isPressed
  , isDragging
  , isAnimating
  , getAutomationMode
  , getKeyframePresence
  , getSafetyZone
  , getDefaultValue
  
  -- * State Modifiers
  , setValue
  , setAngle
  , setDisabled
  , setFocused
  , setHovered
  , setPressed
  , setDragging
  , setAnimating
  , setAutomationMode
  , setKeyframePresence
  , setSafetyZone
  , setDefaultValue
  , resetToDefault
  
  -- * Re-exports from Geometry
  , module Hydrogen.Schema.Geometry.Angle
  
  -- * Re-exports from Temporal
  , module Hydrogen.Schema.Temporal.Progress
  
  -- * Re-exports from Dimension
  , module Hydrogen.Schema.Dimension.Range
  
  -- * Re-exports from Reactive
  , module Hydrogen.Schema.Reactive.Flags
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  , (==)
  , (||)
  , (&&)
  , (>)
  , (<)
  , (>=)
  , (<=)
  )

import Prim (Boolean, Number)

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Angle
  ( Degrees
  , degrees
  , unwrapDegrees
  , zero
  , half
  , lerpAngle
  )

import Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , unwrapProgress
  , start
  , end
  )

import Hydrogen.Schema.Dimension.Range
  ( Range
  , range
  , minVal
  , maxVal
  , normalize
  , lerp
  , contains
  , rangeUnit
  , rangePercent
  )

import Hydrogen.Schema.Reactive.Flags
  ( DisabledFlag(DisabledFlag)
  , FocusedFlag(FocusedFlag)
  , HoveredFlag(HoveredFlag)
  , PressedFlag(PressedFlag)
  , DraggingFlag(DraggingFlag)
  , AnimatingFlag(AnimatingFlag)
  )

import Hydrogen.Schema.Bounded as Bounded

import Data.Number (log, pow) as Number

-- Bounded types from Schema pillars for type-safe KnobValue
import Hydrogen.Schema.Audio.Level
  ( LinearGain(LinearGain)
  , linearGain
  , unwrapLinearGain
  )

import Hydrogen.Schema.Audio.Spatial
  ( Pan(Pan)
  , pan
  , unwrapPan
  )

import Hydrogen.Schema.Audio.Synthesis
  ( CutoffFreq(CutoffFreq)
  , cutoffFreq
  , unwrapCutoffFreq
  )

import Hydrogen.Schema.Media.Video
  ( PlaybackRate
  , playbackRate
  , unwrapPlaybackRate
  )

import Hydrogen.Schema.Dimension.Percentage
  ( Percent(Percent)
  , percent
  , unwrapPercent
  , SignedPercent(SignedPercent)
  , signedPercent
  , unwrapSignedPercent
  )

import Hydrogen.Schema.Medical.Infusion
  ( InfusionRate(InfusionRate)
  , infusionRateFromNumber
  , unwrapInfusionRate
  , toNumber
  ) as Medical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // automation mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Automation mode for DAW/audio workstation knobs.
-- |
-- | These modes determine how the knob interacts with automation lanes:
-- | - Manual: No automation, user has full control
-- | - Read: Follows automation, user can override temporarily
-- | - Write: Records all movements to automation lane
-- | - Touch: Records while touched, returns to automation when released
-- | - Latch: Like Touch, but holds last value when released
data AutomationMode
  = AutoManual     -- ^ No automation
  | AutoRead       -- ^ Playback automation
  | AutoWrite      -- ^ Record all movements
  | AutoTouch      -- ^ Record while touched
  | AutoLatch      -- ^ Record, hold on release

derive instance eqAutomationMode :: Eq AutomationMode
derive instance ordAutomationMode :: Ord AutomationMode

instance showAutomationMode :: Show AutomationMode where
  show AutoManual = "manual"
  show AutoRead = "read"
  show AutoWrite = "write"
  show AutoTouch = "touch"
  show AutoLatch = "latch"

-- | Is automation actively controlling or recording the knob?
isAutomationActive :: AutomationMode -> Boolean
isAutomationActive AutoManual = false
isAutomationActive _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // keyframe presence
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyframe presence for motion graphics knobs.
-- |
-- | Indicates whether this parameter has keyframes at the current time:
-- | - None: No keyframes on this parameter
-- | - Present: Keyframe exists at current time (stopwatch filled)
-- | - Pending: Keyframes exist but not at current time (stopwatch empty)
data KeyframePresence
  = KeyframeNone      -- ^ No keyframes on parameter
  | KeyframePresent   -- ^ Keyframe at current time
  | KeyframePending   -- ^ Keyframes exist, not at current time

derive instance eqKeyframePresence :: Eq KeyframePresence
derive instance ordKeyframePresence :: Ord KeyframePresence

instance showKeyframePresence :: Show KeyframePresence where
  show KeyframeNone = "none"
  show KeyframePresent = "present"
  show KeyframePending = "pending"

-- | Does this parameter have a keyframe at current time?
hasKeyframe :: KeyframePresence -> Boolean
hasKeyframe KeyframePresent = true
hasKeyframe _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // safety zone
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safety zone for medical/hospital knobs.
-- |
-- | Medical knobs have clearly defined safety zones:
-- | - Safe: Value is within normal operating range (green)
-- | - Caution: Value is elevated, monitor closely (yellow)
-- | - Danger: Value requires confirmation, potentially harmful (red)
data SafetyZone
  = ZoneSafe      -- ^ Normal operating range
  | ZoneCaution   -- ^ Elevated, monitor closely
  | ZoneDanger    -- ^ Requires confirmation

derive instance eqSafetyZone :: Eq SafetyZone
derive instance ordSafetyZone :: Ord SafetyZone

instance showSafetyZone :: Show SafetyZone where
  show ZoneSafe = "safe"
  show ZoneCaution = "caution"
  show ZoneDanger = "danger"

-- | Is the current value in a safe zone?
isSafeValue :: SafetyZone -> Boolean
isSafeValue ZoneSafe = true
isSafeValue _ = false

-- | Does the current value require user confirmation?
requiresConfirmation :: SafetyZone -> Boolean
requiresConfirmation ZoneDanger = true
requiresConfirmation _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // knob value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum type for all knob value domains.
-- |
-- | Each variant uses its native bounded type from Schema pillars.
-- | Invalid values (NaN, Infinity, out-of-bounds) are rejected at construction.
-- |
-- | ## Bounded Type Mappings
-- |
-- | - Angle: Degrees from Geometry.Angle (0-360, wraps)
-- | - Volume: LinearGain from Audio.Level (0-1, clamps)
-- | - Pan: Pan from Audio.Spatial (-1 to +1, clamps)
-- | - Frequency: CutoffFreq from Audio.Synthesis (20-20000 Hz)
-- | - Rate: PlaybackRate from Media.Video (0.25-4.0x)
-- | - Percent: Percent from Dimension.Percentage (0-100)
-- | - Bipolar: SignedPercent from Dimension.Percentage (-100 to +100)
-- | - Medical: InfusionRate from Medical.Infusion (0-999 Int)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Using bounded types instead of raw Number guarantees:
-- | - No NaN or Infinity can propagate through knob values
-- | - All values are within valid domain bounds
-- | - Type system prevents mixing incompatible value types
data KnobValue
  = ValueAngle Degrees              -- ^ Raw rotation (hue, etc.) [0, 360)
  | ValueVolume LinearGain          -- ^ Audio level [0, 1] clamped
  | ValuePan Pan                    -- ^ Stereo position [-1, +1] clamped
  | ValueFrequency CutoffFreq       -- ^ Hz [20, 20000] clamped
  | ValueRate PlaybackRate          -- ^ Playback speed [0.25, 4.0] clamped
  | ValuePercent Percent            -- ^ Generic percentage [0, 100] clamped
  | ValueBipolar SignedPercent      -- ^ Center-zero [-100, +100] clamped
  | ValueMedical Medical.InfusionRate  -- ^ IV rate [0, 999] Int clamped

derive instance eqKnobValue :: Eq KnobValue
derive instance ordKnobValue :: Ord KnobValue

instance showKnobValue :: Show KnobValue where
  show (ValueAngle d) = "angle:" <> show d
  show (ValueVolume v) = "volume:" <> show (unwrapLinearGain v * 100.0) <> "%"
  show (ValuePan p) = "pan:" <> show (unwrapPan p * 100.0)
  show (ValueFrequency f) = "freq:" <> show (unwrapCutoffFreq f) <> "Hz"
  show (ValueRate r) = "rate:" <> show (unwrapPlaybackRate r) <> "x"
  show (ValuePercent p) = "percent:" <> show (unwrapPercent p) <> "%"
  show (ValueBipolar b) = "bipolar:" <> show (unwrapSignedPercent b)
  show (ValueMedical m) = "medical:" <> show (Medical.unwrapInfusionRate m)

-- | Is this a bipolar value (center = 0)?
isBipolar :: KnobValue -> Boolean
isBipolar (ValuePan _) = true
isBipolar (ValueBipolar _) = true
isBipolar _ = false

-- | Convert any knob value to normalized progress [0, 1].
-- |
-- | Since all KnobValue variants now use bounded types, the values are
-- | GUARANTEED to be within valid ranges. No runtime clamping needed.
-- |
-- | ## Mappings
-- |
-- | - Angle: [0, 360) -> [0, 1]
-- | - Volume: LinearGain [0, 1] -> [0, 1] (direct)
-- | - Pan: [-1, +1] -> [0, 1] (0.5 = center)
-- | - Frequency: [20, 20000] Hz -> [0, 1] (logarithmic)
-- | - Rate: [0.25, 4.0]x -> [0, 1] (logarithmic)
-- | - Percent: [0, 100] -> [0, 1]
-- | - Bipolar: [-100, +100] -> [0, 1] (0.5 = center)
-- | - Medical: [0, 999] -> [0, 1]
toProgress :: KnobValue -> Progress
toProgress val = case val of
  ValueAngle d -> progress (unwrapDegrees d / 360.0)
  ValueVolume v -> progress (unwrapLinearGain v)  -- Already [0, 1]
  ValuePan p -> progress ((unwrapPan p + 1.0) / 2.0)  -- [-1, 1] -> [0, 1]
  ValueFrequency f -> 
    let logMin = logBase 10.0 20.0
        logMax = logBase 10.0 20000.0
        logF = logBase 10.0 (unwrapCutoffFreq f)
    in progress ((logF - logMin) / (logMax - logMin))
  ValueRate r ->
    let logMin = logBase 10.0 0.25
        logMax = logBase 10.0 4.0
        logR = logBase 10.0 (unwrapPlaybackRate r)
    in progress ((logR - logMin) / (logMax - logMin))
  ValuePercent p -> progress (unwrapPercent p / 100.0)
  ValueBipolar b -> progress ((unwrapSignedPercent b + 100.0) / 200.0)
  ValueMedical m -> progress (Medical.toNumber m / 999.0)

-- | Create a knob value from normalized progress, given a template value.
-- |
-- | The template determines what type of value to create. Smart constructors
-- | are used to guarantee the resulting value is within valid bounds.
-- |
-- | ## Safety
-- |
-- | Since Progress is bounded to [0, 1] and we use smart constructors,
-- | the output is GUARANTEED to be valid. No runtime errors possible.
fromProgress :: Progress -> KnobValue -> KnobValue
fromProgress p template = 
  let t = unwrapProgress p
  in case template of
    ValueAngle _ -> ValueAngle (degrees (t * 360.0))
    ValueVolume _ -> ValueVolume (linearGain t)  -- [0, 1] -> LinearGain
    ValuePan _ -> ValuePan (pan (t * 2.0 - 1.0))  -- [0, 1] -> [-1, 1]
    ValueFrequency _ -> 
      let logMin = logBase 10.0 20.0
          logMax = logBase 10.0 20000.0
          logF = logMin + t * (logMax - logMin)
      in ValueFrequency (cutoffFreq (pow 10.0 logF))
    ValueRate _ ->
      let logMin = logBase 10.0 0.25
          logMax = logBase 10.0 4.0
          logR = logMin + t * (logMax - logMin)
      in ValueRate (playbackRate (pow 10.0 logR))
    ValuePercent _ -> ValuePercent (percent (t * 100.0))
    ValueBipolar _ -> ValueBipolar (signedPercent (t * 200.0 - 100.0))
    ValueMedical _ -> ValueMedical (Medical.infusionRateFromNumber (t * 999.0))

-- | Logarithm base b (using natural log from Data.Number)
logBase :: Number -> Number -> Number
logBase b x = Number.log x / Number.log b

-- | Power function (re-export from Data.Number)
pow :: Number -> Number -> Number
pow = Number.pow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete knob element state.
-- |
-- | Combines:
-- | - Core value (what the knob represents)
-- | - Interaction flags (user input state)
-- | - Domain-specific state (automation, keyframes, safety)
-- | - Default value (for reset-to-default feature)
type KnobElementState =
  { -- Core value
    value :: KnobValue              -- ^ Current value
  , defaultValue :: KnobValue       -- ^ Value to reset to (Cmd+click)
    -- Interaction flags
  , disabled :: DisabledFlag
  , focused :: FocusedFlag
  , hovered :: HoveredFlag
  , pressed :: PressedFlag
  , dragging :: DraggingFlag
  , animating :: AnimatingFlag
    -- Domain-specific state
  , automationMode :: AutomationMode        -- ^ DAW automation
  , keyframePresence :: KeyframePresence    -- ^ Mograph keyframes
  , safetyZone :: SafetyZone                -- ^ Medical safety
  }

-- | Default knob state (percent knob, 50%).
defaultState :: KnobElementState
defaultState =
  { value: ValuePercent (percent 50.0)
  , defaultValue: ValuePercent (percent 50.0)
  , disabled: DisabledFlag false      -- enabled
  , focused: FocusedFlag false        -- unfocused
  , hovered: HoveredFlag false        -- unhovered
  , pressed: PressedFlag false        -- released
  , dragging: DraggingFlag false      -- not dragging
  , animating: AnimatingFlag false    -- not animating
  , automationMode: AutoManual
  , keyframePresence: KeyframeNone
  , safetyZone: ZoneSafe
  }

-- | Volume knob state (0-1 linear gain, default 0.8).
-- |
-- | Input is linear gain [0, 1]. Smart constructor clamps out-of-bounds values.
volumeState :: Number -> KnobElementState
volumeState vol = defaultState
  { value = ValueVolume (linearGain vol)
  , defaultValue = ValueVolume (linearGain 0.8)
  }

-- | Pan knob state (-1 to +1, default center).
-- |
-- | Input is pan position [-1, +1]. Smart constructor clamps out-of-bounds values.
panState :: Number -> KnobElementState
panState p = defaultState
  { value = ValuePan (pan p)
  , defaultValue = ValuePan (pan 0.0)
  }

-- | Frequency knob state (20-20000 Hz, default 1000 Hz).
-- |
-- | Input is frequency in Hz. Smart constructor clamps to [20, 20000].
frequencyState :: Number -> KnobElementState
frequencyState freq = defaultState
  { value = ValueFrequency (cutoffFreq freq)
  , defaultValue = ValueFrequency (cutoffFreq 1000.0)
  }

-- | Playback rate knob state (0.25-4.0x, default 1.0x).
-- |
-- | Input is rate multiplier. Smart constructor clamps to [0.25, 4.0].
rateState :: Number -> KnobElementState
rateState r = defaultState
  { value = ValueRate (playbackRate r)
  , defaultValue = ValueRate (playbackRate 1.0)
  }

-- | Rotation knob state (0-360 degrees).
rotationState :: Number -> KnobElementState
rotationState deg = defaultState
  { value = ValueAngle (degrees deg)
  , defaultValue = ValueAngle zero
  }

-- | Medical knob state (0-999, discrete).
-- |
-- | Medical knobs have safety zones based on value:
-- | - 0-300: Safe (green)
-- | - 301-600: Caution (yellow)
-- | - 601-999: Danger (red)
-- |
-- | Input is rate in mL/hr. Smart constructor clamps and handles NaN/Infinity.
medicalState :: Number -> KnobElementState
medicalState val = 
  let rate = Medical.infusionRateFromNumber val
      rateNum = Medical.toNumber rate
      zone = if rateNum <= 300.0 then ZoneSafe
             else if rateNum <= 600.0 then ZoneCaution
             else ZoneDanger
  in defaultState
    { value = ValueMedical rate
    , defaultValue = ValueMedical (Medical.infusionRateFromNumber 0.0)
    , safetyZone = zone
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current value.
getValue :: KnobElementState -> KnobValue
getValue s = s.value

-- | Get the current angle (converts any value to degrees).
getAngle :: KnobElementState -> Degrees
getAngle s = 
  let p = toProgress s.value
  in degrees (unwrapProgress p * 360.0)

-- | Get value as normalized progress [0, 1].
getProgressNormalized :: KnobElementState -> Progress
getProgressNormalized s = toProgress s.value

-- | Is knob disabled?
isDisabled :: KnobElementState -> Boolean
isDisabled s = case s.disabled of
  DisabledFlag b -> b

-- | Is knob focused?
isFocused :: KnobElementState -> Boolean
isFocused s = case s.focused of
  FocusedFlag b -> b

-- | Is knob hovered?
isHovered :: KnobElementState -> Boolean
isHovered s = case s.hovered of
  HoveredFlag b -> b

-- | Is knob pressed?
isPressed :: KnobElementState -> Boolean
isPressed s = case s.pressed of
  PressedFlag b -> b

-- | Is knob being dragged?
isDragging :: KnobElementState -> Boolean
isDragging s = case s.dragging of
  DraggingFlag b -> b

-- | Is knob animating?
isAnimating :: KnobElementState -> Boolean
isAnimating s = case s.animating of
  AnimatingFlag b -> b

-- | Get automation mode.
getAutomationMode :: KnobElementState -> AutomationMode
getAutomationMode s = s.automationMode

-- | Get keyframe presence.
getKeyframePresence :: KnobElementState -> KeyframePresence
getKeyframePresence s = s.keyframePresence

-- | Get safety zone.
getSafetyZone :: KnobElementState -> SafetyZone
getSafetyZone s = s.safetyZone

-- | Get default value (for reset).
getDefaultValue :: KnobElementState -> KnobValue
getDefaultValue s = s.defaultValue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the current value.
setValue :: KnobValue -> KnobElementState -> KnobElementState
setValue v s = s { value = v }

-- | Set value from angle (preserves value type).
setAngle :: Degrees -> KnobElementState -> KnobElementState
setAngle d s = 
  let p = progress (unwrapDegrees d / 360.0)
  in s { value = fromProgress p s.value }

-- | Set disabled state.
setDisabled :: Boolean -> KnobElementState -> KnobElementState
setDisabled b s = s { disabled = DisabledFlag b }

-- | Set focused state.
setFocused :: Boolean -> KnobElementState -> KnobElementState
setFocused b s = s { focused = FocusedFlag b }

-- | Set hovered state.
setHovered :: Boolean -> KnobElementState -> KnobElementState
setHovered b s = s { hovered = HoveredFlag b }

-- | Set pressed state.
setPressed :: Boolean -> KnobElementState -> KnobElementState
setPressed b s = s { pressed = PressedFlag b }

-- | Set dragging state.
setDragging :: Boolean -> KnobElementState -> KnobElementState
setDragging b s = s { dragging = DraggingFlag b }

-- | Set animating state.
setAnimating :: Boolean -> KnobElementState -> KnobElementState
setAnimating b s = s { animating = AnimatingFlag b }

-- | Set automation mode.
setAutomationMode :: AutomationMode -> KnobElementState -> KnobElementState
setAutomationMode m s = s { automationMode = m }

-- | Set keyframe presence.
setKeyframePresence :: KeyframePresence -> KnobElementState -> KnobElementState
setKeyframePresence k s = s { keyframePresence = k }

-- | Set safety zone.
setSafetyZone :: SafetyZone -> KnobElementState -> KnobElementState
setSafetyZone z s = s { safetyZone = z }

-- | Set default value.
setDefaultValue :: KnobValue -> KnobElementState -> KnobElementState
setDefaultValue v s = s { defaultValue = v }

-- | Reset to default value.
resetToDefault :: KnobElementState -> KnobElementState
resetToDefault s = s { value = s.defaultValue }
