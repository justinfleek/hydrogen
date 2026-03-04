-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // element // slider // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SliderState — State atoms for slider/range controls.
-- |
-- | ## Verified Atoms (re-exported from Schema pillars)
-- |
-- | - Hue (Color.Hue) — Hue slider (0-359, wraps)
-- | - Saturation (Color.Saturation) — Saturation slider (0-100)
-- | - Lightness (Color.Lightness) — Lightness slider (0-100)
-- | - Volume (Media.Video) — Audio slider (0.0-1.0)
-- | - Kelvin (Color.Kelvin) — Color temperature (1000-40000)
-- | - Progress (Temporal.Progress) — Generic progress (0.0-1.0)
-- | - Range (Dimension.Range) — Dual-thumb range selection
-- | - DisabledFlag, FocusedFlag (Reactive.Flags) — UI state
-- |
-- | ## Slider Value Model
-- |
-- | SliderValue is a sum type that captures all possible slider value types:
-- | - Each variant uses its native bounded type
-- | - The slider semantics determine which variant is active
-- | - Conversion functions normalize all values to Progress (0.0-1.0)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Color.Hue (hue values)
-- | - Hydrogen.Schema.Color.Saturation (saturation values)
-- | - Hydrogen.Schema.Color.Lightness (lightness values)
-- | - Hydrogen.Schema.Color.Kelvin (temperature values)
-- | - Hydrogen.Schema.Media.Video (volume)
-- | - Hydrogen.Schema.Temporal.Progress (generic progress)
-- | - Hydrogen.Schema.Dimension.Range (dual-thumb)
-- | - Hydrogen.Schema.Reactive.Flags (UI state flags)
-- |
-- | ## Design Philosophy
-- |
-- | State atoms describe WHAT the slider shows, not HOW it looks.
-- | All values use verified bounded types — no raw Numbers.

module Hydrogen.Schema.Element.Slider.State
  ( -- * Slider Value Sum Type
    SliderValue
      ( ValueHue
      , ValueSaturation
      , ValueLightness
      , ValueVolume
      , ValueKelvin
      , ValueProgress
      , ValueRange
      , ValueZoom
      )
  , toProgress
  , fromProgress
  
  -- * Slider Element State Record
  , SliderElementState
  , defaultState
  , hueState
  , saturationState
  , lightnessState
  , volumeState
  , kelvinState
  , progressState
  , rangeState
  , zoomState
  
  -- * State Accessors
  , getValue
  , getProgressNormalized
  , isDisabled
  , isFocused
  , isHovered
  , isPressed
  , isDragging
  , isAnimating
  
  -- * State Modifiers
  , setValue
  , setDisabled
  , setFocused
  , setHovered
  , setPressed
  , setDragging
  , setAnimating
  
  -- * Re-exports from Color
  , module Hydrogen.Schema.Color.Hue
  , module Hydrogen.Schema.Color.Saturation
  , module Hydrogen.Schema.Color.Lightness
  , module Hydrogen.Schema.Color.Kelvin
  
  -- * Re-exports from Media
  , module Hydrogen.Schema.Media.Video
  
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
  , (/)
  , (-)
  , (*)
  , (+)
  , (<>)
  )

import Prim (Boolean, Int, Number)

import Data.Int (toNumber, round) as Int

import Hydrogen.Schema.Color.Hue
  ( Hue
  , hue
  , unwrap
  , red
  ) as Hue

import Hydrogen.Schema.Color.Hue
  ( Hue
  , hue
  , unwrap
  , red
  , orange
  , yellow
  , green
  , cyan
  , blue
  , magenta
  , hueWrap
  , rotate
  , complement
  )

import Hydrogen.Schema.Color.Saturation
  ( Saturation
  , saturation
  , unwrap
  , gray
  , muted
  , medium
  , vivid
  , full
  ) as Saturation

import Hydrogen.Schema.Color.Saturation
  ( Saturation
  , saturation
  , gray
  , muted
  , medium
  , vivid
  , full
  )

import Hydrogen.Schema.Color.Lightness
  ( Lightness
  , lightness
  , unwrap
  ) as Lightness

import Hydrogen.Schema.Color.Lightness
  ( Lightness
  , lightness
  , lighten
  , darken
  )

import Hydrogen.Schema.Color.Kelvin
  ( Kelvin
  , kelvin
  , unwrap
  , kelvinToRgb
  ) as Kelvin

import Hydrogen.Schema.Color.Kelvin
  ( Kelvin
  , kelvin
  , kelvinToRgb
  , isWarm
  , isNeutral
  , isCool
  )

import Hydrogen.Schema.Media.Video
  ( Volume
  , volume
  , unwrapVolume
  , volumeMute
  , volumeHalf
  , volumeFull
  )

import Hydrogen.Schema.Temporal.Progress
  ( Progress
  , progress
  , unwrapProgress
  , start
  , end
  )

import Hydrogen.Schema.Dimension.Range
  ( Range(Range)
  , range
  , rangeUnit
  , rangePercent
  , minVal
  , maxVal
  , span
  , normalize
  , lerp
  )

import Hydrogen.Schema.Dimension.Percentage
  ( Ratio(Ratio)
  , ratio
  , unwrapRatio
  ) as Percentage

-- | Reactive.Flags provides verified boolean atoms for UI state.
-- |
-- | For sliders, we use:
-- | - DisabledFlag: Cannot interact with slider
-- | - FocusedFlag: Has keyboard focus (enables arrow key control)
-- | - HoveredFlag: Pointer is over slider (visual feedback)
-- | - PressedFlag: Thumb is being pressed (mousedown/touchstart)
-- | - DraggingFlag: Thumb is being dragged (value changing)
-- | - AnimatingFlag: Transition animation in progress
import Hydrogen.Schema.Reactive.Flags
  ( DisabledFlag(DisabledFlag)
  , FocusedFlag(FocusedFlag)
  , HoveredFlag(HoveredFlag)
  , PressedFlag(PressedFlag)
  , DraggingFlag(DraggingFlag)
  , AnimatingFlag(AnimatingFlag)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // slider value
-- ═════════════════════════════════════════════════════════════════════════════

-- | SliderValue — Sum type for all slider value domains.
-- |
-- | Each variant uses its native bounded type from Schema pillars:
-- | - ValueHue: Hue (0-359, wraps)
-- | - ValueSaturation: Saturation (0-100, clamps)
-- | - ValueLightness: Lightness (0-100, clamps)
-- | - ValueVolume: Volume (0.0-1.0, clamps)
-- | - ValueKelvin: Kelvin (1000-40000, clamps)
-- | - ValueProgress: Progress (0.0-1.0, clamps)
-- | - ValueRange: Range (min/max pair for dual-thumb)
-- | - ValueZoom: Ratio (0.1-10.0 typical, UI zoom level)
data SliderValue
  = ValueHue Hue
  | ValueSaturation Saturation
  | ValueLightness Lightness
  | ValueVolume Volume
  | ValueKelvin Kelvin
  | ValueProgress Progress
  | ValueRange Range
  | ValueZoom Percentage.Ratio

derive instance eqSliderValue :: Eq SliderValue
derive instance ordSliderValue :: Ord SliderValue

instance showSliderValue :: Show SliderValue where
  show (ValueHue h) = "ValueHue(" <> show h <> ")"
  show (ValueSaturation s) = "ValueSaturation(" <> show s <> ")"
  show (ValueLightness l) = "ValueLightness(" <> show l <> ")"
  show (ValueVolume v) = "ValueVolume(" <> show v <> ")"
  show (ValueKelvin k) = "ValueKelvin(" <> show k <> ")"
  show (ValueProgress p) = "ValueProgress(" <> show p <> ")"
  show (ValueRange r) = "ValueRange(" <> show r <> ")"
  show (ValueZoom z) = "ValueZoom(" <> show z <> ")"

-- | Convert any SliderValue to normalized Progress (0.0-1.0).
-- |
-- | This is essential for rendering — the thumb position is always
-- | determined by Progress regardless of the underlying value type.
-- |
-- | ## Normalization Rules
-- |
-- | - Hue: 0-359 → 0.0-1.0 (linear)
-- | - Saturation/Lightness: 0-100 → 0.0-1.0
-- | - Volume: Already 0.0-1.0
-- | - Kelvin: 1000-40000 → 0.0-1.0 (linear)
-- | - Progress: Already 0.0-1.0
-- | - Range: Returns midpoint as progress
-- | - Zoom: Maps [0.1, 10.0] → 0.0-1.0 (logarithmic scaling)
toProgress :: SliderValue -> Progress
toProgress = case _ of
  ValueHue h -> 
    progress (Int.toNumber (Hue.unwrap h) / 359.0)
  ValueSaturation s -> 
    progress (Int.toNumber (Saturation.unwrap s) / 100.0)
  ValueLightness l -> 
    progress (Int.toNumber (Lightness.unwrap l) / 100.0)
  ValueVolume v -> 
    progress (unwrapVolume v)
  ValueKelvin k -> 
    -- Normalize 1000-40000 to 0.0-1.0
    progress ((Int.toNumber (Kelvin.unwrap k) - 1000.0) / 39000.0)
  ValueProgress p -> p
  ValueRange r ->
    -- For range, return normalized midpoint
    let midPoint = (minVal r + maxVal r) / 2.0
    in progress (normalize midPoint r)
  ValueZoom z ->
    -- Logarithmic: log10(0.1)=-1, log10(10)=1, mapped to 0-1
    -- Simplified linear for now: (z - 0.1) / 9.9
    progress ((Percentage.unwrapRatio z - 0.1) / 9.9)

-- | Convert Progress back to a specific SliderValue type.
-- |
-- | Requires knowing the target type. Use the appropriate variant.
fromProgress :: Progress -> SliderValue -> SliderValue
fromProgress p val = case val of
  ValueHue _ -> 
    ValueHue (hue (roundToInt (unwrapProgress p * 359.0)))
  ValueSaturation _ -> 
    ValueSaturation (saturation (roundToInt (unwrapProgress p * 100.0)))
  ValueLightness _ -> 
    ValueLightness (lightness (roundToInt (unwrapProgress p * 100.0)))
  ValueVolume _ -> 
    ValueVolume (volume (unwrapProgress p))
  ValueKelvin _ -> 
    ValueKelvin (kelvin (roundToInt (unwrapProgress p * 39000.0 + 1000.0)))
  ValueProgress _ -> 
    ValueProgress p
  ValueRange r ->
    -- Scale progress to range, update both min and max
    let v = lerp (unwrapProgress p) r
    in ValueRange (range v v)
  ValueZoom _ ->
    -- Reverse: p * 9.9 + 0.1
    ValueZoom (Percentage.ratio (unwrapProgress p * 9.9 + 0.1))

-- | Helper to round Number to Int.
-- |
-- | Uses Data.Int.round for proper rounding.
roundToInt :: Number -> Int
roundToInt = Int.round

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // slider element state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete slider element state — all values needed to render a slider.
-- |
-- | ## Verified Bounded Types
-- |
-- | Every field uses a verified Schema atom from Reactive.Flags:
-- | - value: SliderValue (sum type of bounded values)
-- | - disabled: DisabledFlag — Cannot interact with slider
-- | - focused: FocusedFlag — Has keyboard focus
-- | - hovered: HoveredFlag — Pointer is over slider
-- | - pressed: PressedFlag — Thumb is being pressed
-- | - dragging: DraggingFlag — Thumb is being dragged
-- | - animating: AnimatingFlag — Transition animation in progress
-- |
-- | ## State Machine
-- |
-- | A slider transitions between interaction states:
-- | - Idle: No interaction (all flags false)
-- | - Hovered: Pointer over track or thumb
-- | - Focused: Has keyboard focus (arrow keys adjust value)
-- | - Pressed: Mousedown/touchstart on thumb
-- | - Dragging: Thumb actively being dragged (value changing)
-- | - Animating: Value transition animation in progress
-- |
-- | Multiple states can be active simultaneously:
-- | - focused AND dragging (keyboard focus while mouse-dragging)
-- | - hovered AND focused (pointer over while keyboard-focused)
-- | - dragging AND animating (smooth value transitions during drag)
type SliderElementState =
  { -- Core value (polymorphic via sum type)
    value :: SliderValue
    -- Interaction state (verified flags from Reactive.Flags)
  , disabled :: DisabledFlag         -- ^ Cannot interact with slider
  , focused :: FocusedFlag           -- ^ Has keyboard focus
  , hovered :: HoveredFlag           -- ^ Pointer is over slider
  , pressed :: PressedFlag           -- ^ Thumb is being pressed
  , dragging :: DraggingFlag         -- ^ Thumb is being dragged
  , animating :: AnimatingFlag       -- ^ Transition animation in progress
  }

-- | Default slider state — progress at 0.5, enabled, not interacting.
defaultState :: SliderElementState
defaultState =
  { value: ValueProgress (progress 0.5)
  , disabled: DisabledFlag false
  , focused: FocusedFlag false
  , hovered: HoveredFlag false
  , pressed: PressedFlag false
  , dragging: DraggingFlag false
  , animating: AnimatingFlag false
  }

-- | Hue slider state — red hue (0°).
hueState :: SliderElementState
hueState = defaultState { value = ValueHue Hue.red }

-- | Saturation slider state — full saturation (100%).
saturationState :: SliderElementState
saturationState = defaultState { value = ValueSaturation Saturation.full }

-- | Lightness slider state — mid lightness (50%).
lightnessState :: SliderElementState
lightnessState = defaultState { value = ValueLightness (lightness 50) }

-- | Volume slider state — half volume (0.5).
volumeState :: SliderElementState
volumeState = defaultState { value = ValueVolume volumeHalf }

-- | Kelvin slider state — daylight (6500K).
kelvinState :: SliderElementState
kelvinState = defaultState { value = ValueKelvin (kelvin 6500) }

-- | Progress slider state — start (0.0).
progressState :: SliderElementState
progressState = defaultState { value = ValueProgress start }

-- | Range slider state — unit range [0, 1].
rangeState :: SliderElementState
rangeState = defaultState { value = ValueRange rangeUnit }

-- | Zoom slider state — 1.0x (100% zoom).
zoomState :: SliderElementState
zoomState = defaultState { value = ValueZoom (Percentage.ratio 1.0) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current value.
getValue :: SliderElementState -> SliderValue
getValue s = s.value

-- | Get value as normalized progress (0.0-1.0).
-- |
-- | Useful for positioning the thumb regardless of value type.
getProgressNormalized :: SliderElementState -> Progress
getProgressNormalized s = toProgress s.value

-- | Is the slider disabled?
isDisabled :: SliderElementState -> Boolean
isDisabled s = case s.disabled of
  DisabledFlag b -> b

-- | Does the slider have keyboard focus?
isFocused :: SliderElementState -> Boolean
isFocused s = case s.focused of
  FocusedFlag b -> b

-- | Is the pointer hovering over the slider?
isHovered :: SliderElementState -> Boolean
isHovered s = case s.hovered of
  HoveredFlag b -> b

-- | Is the thumb being pressed (mousedown/touchstart)?
isPressed :: SliderElementState -> Boolean
isPressed s = case s.pressed of
  PressedFlag b -> b

-- | Is the thumb being dragged?
isDragging :: SliderElementState -> Boolean
isDragging s = case s.dragging of
  DraggingFlag b -> b

-- | Is a transition animation in progress?
isAnimating :: SliderElementState -> Boolean
isAnimating s = case s.animating of
  AnimatingFlag b -> b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set value directly.
setValue :: SliderValue -> SliderElementState -> SliderElementState
setValue v s = s { value = v }

-- | Set disabled state.
setDisabled :: Boolean -> SliderElementState -> SliderElementState
setDisabled b s = s { disabled = DisabledFlag b }

-- | Set focused state.
setFocused :: Boolean -> SliderElementState -> SliderElementState
setFocused b s = s { focused = FocusedFlag b }

-- | Set hovered state.
setHovered :: Boolean -> SliderElementState -> SliderElementState
setHovered b s = s { hovered = HoveredFlag b }

-- | Set pressed state.
setPressed :: Boolean -> SliderElementState -> SliderElementState
setPressed b s = s { pressed = PressedFlag b }

-- | Set dragging state.
setDragging :: Boolean -> SliderElementState -> SliderElementState
setDragging b s = s { dragging = DraggingFlag b }

-- | Set animating state.
setAnimating :: Boolean -> SliderElementState -> SliderElementState
setAnimating b s = s { animating = AnimatingFlag b }
