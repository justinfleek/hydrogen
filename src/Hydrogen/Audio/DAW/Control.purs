-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // audio // daw // control
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DAW Control — Visual Control Primitives for CHAD
-- |
-- | Knobs, sliders, buttons, pads, wheels — all the tactile controls a producer
-- | expects. Every control has UUID5 identity and bounded value ranges.
-- |
-- | ## Control Types
-- |
-- | - Knob: Rotary control (0° to 270° typical)
-- | - Slider: Linear vertical or horizontal
-- | - Button: Momentary or toggle
-- | - Pad: Velocity-sensitive trigger (8x8 grid for Launchpad-style)
-- | - Wheel: Pitch bend / mod wheel
-- | - Switch: Multi-position selector
-- | - XYPad: 2D control surface
-- | - Encoder: Endless rotary with acceleration
-- |
-- | ## TouchDesigner Integration
-- |
-- | All controls emit OSC-compatible messages and can receive external input.
-- | CHAD can both control and be controlled.
-- |
-- | ## Reference
-- | CHAD autonomous DJ system — building the knobs he turns
module Hydrogen.Audio.DAW.Control
  ( -- * Core Control Types
    ControlId
  , mkControlId
  , controlIdValue
    -- * Value Range
  , ControlRange
  , mkControlRange
  , rangeMin
  , rangeMax
  , rangeDefault
  , normalizeToRange
  , rangeToNormalized
    -- * Knob
  , Knob
  , mkKnob
  , KnobStyle
      ( KnobClassic
      , KnobArc
      , KnobDot
      , KnobVintage
      , KnobLED
      , KnobBipolar
      )
  , KnobSize
      ( KnobTiny
      , KnobSmall
      , KnobMedium
      , KnobLarge
      , KnobXLarge
      )
  , KnobConfig
  , defaultKnobConfig
    -- * Slider  
  , Slider
  , mkSlider
  , SliderOrientation
      ( SliderVertical
      , SliderHorizontal
      )
  , SliderStyle
      ( SliderFader
      , SliderBar
      , SliderFill
      , SliderBipolar
      )
  , SliderConfig
  , defaultSliderConfig
    -- * Button
  , Button
  , mkButton
  , ButtonMode
      ( ButtonMomentary
      , ButtonToggle
      , ButtonRadio
      )
  , ButtonStyle
      ( ButtonFlat
      , ButtonRaised
      , ButtonLED
      , ButtonPad
      )
  , ButtonConfig
  , defaultButtonConfig
    -- * Pad
  , Pad
  , mkPad
  , PadConfig
  , defaultPadConfig
    -- * Grid
  , PadGrid
  , mkPadGrid
  , GridSize
  , mkGridSize
  , gridPadAt
    -- * Wheel
  , Wheel
  , mkWheel
  , WheelType
      ( WheelPitchBend
      , WheelMod
      , WheelExpression
      )
  , WheelConfig
    -- * Switch
  , Switch
  , mkSwitch
  , SwitchConfig
  , SwitchStyle
      ( SwitchRotary
      , SwitchSlide
      , SwitchSegment
      )
    -- * XY Pad
  , XYPad
  , mkXYPad
  , XYPadConfig
    -- * Encoder
  , Encoder
  , mkEncoder
  , EncoderConfig
    -- * Control State
  , ControlValue
  , mkControlValue
  , controlNormalized
  , controlScaled
    -- * MIDI Mapping
  , MidiMapping
  , MidiCC
  , mkMidiCC
  , MidiChannel
  , mkMidiChannel
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Int (toNumber, floor)
import Data.Array (index, replicate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // control id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a control (UUID5 compatible)
newtype ControlId = ControlId String

derive instance eqControlId :: Eq ControlId
derive instance ordControlId :: Ord ControlId

instance showControlId :: Show ControlId where
  show (ControlId id) = "(ControlId " <> show id <> ")"

mkControlId :: String -> ControlId
mkControlId = ControlId

controlIdValue :: ControlId -> String
controlIdValue (ControlId id) = id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // control range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range for a control's value with bounds
-- |
-- | All controls operate on normalized 0.0-1.0 internally,
-- | but display and emit values in their configured range.
data ControlRange = ControlRange
  { min :: Number
  , max :: Number
  , default :: Number
  }

derive instance eqControlRange :: Eq ControlRange

instance showControlRange :: Show ControlRange where
  show (ControlRange r) = "(ControlRange " <> show r.min <> "-" <> show r.max <> ")"

mkControlRange :: Number -> Number -> Number -> Maybe ControlRange
mkControlRange min max def
  | min < max && def >= min && def <= max = 
      Just (ControlRange { min, max, default: def })
  | otherwise = Nothing

rangeMin :: ControlRange -> Number
rangeMin (ControlRange r) = r.min

rangeMax :: ControlRange -> Number
rangeMax (ControlRange r) = r.max

rangeDefault :: ControlRange -> Number
rangeDefault (ControlRange r) = r.default

-- | Convert normalized (0-1) to range value
normalizeToRange :: ControlRange -> Number -> Number
normalizeToRange (ControlRange r) normalized =
  r.min + (normalized * (r.max - r.min))

-- | Convert range value to normalized (0-1)
rangeToNormalized :: ControlRange -> Number -> Number
rangeToNormalized (ControlRange r) value =
  (value - r.min) / (r.max - r.min)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // control value
-- ═════════════════════════════════════════════════════════════════════════════

-- | A control's current value (always normalized 0.0-1.0 internally)
newtype ControlValue = ControlValue Number

derive instance eqControlValue :: Eq ControlValue
derive instance ordControlValue :: Ord ControlValue

instance showControlValue :: Show ControlValue where
  show (ControlValue v) = "(ControlValue " <> show v <> ")"

mkControlValue :: Number -> Maybe ControlValue
mkControlValue v
  | v >= 0.0 && v <= 1.0 = Just (ControlValue v)
  | otherwise = Nothing

-- | Get normalized value (0.0-1.0)
controlNormalized :: ControlValue -> Number
controlNormalized (ControlValue v) = v

-- | Get scaled value for a range
controlScaled :: ControlRange -> ControlValue -> Number
controlScaled range (ControlValue v) = normalizeToRange range v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // knob
-- ═════════════════════════════════════════════════════════════════════════════

-- | Knob visual style
data KnobStyle
  = KnobClassic       -- Traditional circular knob with pointer
  | KnobArc           -- Arc indicator around edge
  | KnobDot           -- Minimalist dot indicator
  | KnobVintage       -- Skeuomorphic vintage look
  | KnobLED           -- LED ring around knob
  | KnobBipolar       -- Center-detent with +/- display

derive instance eqKnobStyle :: Eq KnobStyle

instance showKnobStyle :: Show KnobStyle where
  show KnobClassic = "KnobClassic"
  show KnobArc = "KnobArc"
  show KnobDot = "KnobDot"
  show KnobVintage = "KnobVintage"
  show KnobLED = "KnobLED"
  show KnobBipolar = "KnobBipolar"

-- | Knob configuration
type KnobConfig =
  { style :: KnobStyle
  , size :: KnobSize
  , sensitivity :: Number       -- Drag sensitivity multiplier
  , acceleration :: Boolean     -- Enable acceleration on fast drag
  , snapToDefault :: Boolean    -- Double-click returns to default
  , showValue :: Boolean        -- Display numeric value
  , label :: String
  }

-- | Knob sizes
data KnobSize = KnobTiny | KnobSmall | KnobMedium | KnobLarge | KnobXLarge

derive instance eqKnobSize :: Eq KnobSize

defaultKnobConfig :: KnobConfig
defaultKnobConfig =
  { style: KnobClassic
  , size: KnobMedium
  , sensitivity: 1.0
  , acceleration: true
  , snapToDefault: true
  , showValue: true
  , label: ""
  }

-- | A rotary knob control
data Knob = Knob
  { id :: ControlId
  , range :: ControlRange
  , value :: ControlValue
  , config :: KnobConfig
  , midiMapping :: Maybe MidiMapping
  }

derive instance eqKnob :: Eq Knob

mkKnob :: ControlId -> ControlRange -> KnobConfig -> Knob
mkKnob id range config = Knob
  { id
  , range
  , value: ControlValue (rangeToNormalized range (rangeDefault range))
  , config
  , midiMapping: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // slider
-- ═════════════════════════════════════════════════════════════════════════════

data SliderOrientation = SliderVertical | SliderHorizontal

derive instance eqSliderOrientation :: Eq SliderOrientation

data SliderStyle
  = SliderFader        -- Traditional mixer fader
  | SliderBar          -- Simple bar
  | SliderFill         -- Fill from min to current
  | SliderBipolar      -- Fill from center

derive instance eqSliderStyle :: Eq SliderStyle

type SliderConfig =
  { orientation :: SliderOrientation
  , style :: SliderStyle
  , length :: Int               -- Pixels
  , thickness :: Int            -- Pixels
  , showValue :: Boolean
  , showTicks :: Boolean
  , tickCount :: Int
  , label :: String
  }

defaultSliderConfig :: SliderConfig
defaultSliderConfig =
  { orientation: SliderVertical
  , style: SliderFader
  , length: 100
  , thickness: 20
  , showValue: true
  , showTicks: false
  , tickCount: 11
  , label: ""
  }

-- | A linear slider control
data Slider = Slider
  { id :: ControlId
  , range :: ControlRange
  , value :: ControlValue
  , config :: SliderConfig
  , midiMapping :: Maybe MidiMapping
  }

derive instance eqSlider :: Eq Slider

mkSlider :: ControlId -> ControlRange -> SliderConfig -> Slider
mkSlider id range config = Slider
  { id
  , range
  , value: ControlValue (rangeToNormalized range (rangeDefault range))
  , config
  , midiMapping: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // button
-- ═════════════════════════════════════════════════════════════════════════════

data ButtonMode
  = ButtonMomentary    -- Active while pressed
  | ButtonToggle       -- Click to toggle on/off
  | ButtonRadio        -- Part of exclusive group

derive instance eqButtonMode :: Eq ButtonMode

data ButtonStyle
  = ButtonFlat         -- Flat design
  | ButtonRaised       -- 3D raised look
  | ButtonLED          -- LED indicator style
  | ButtonPad          -- Pad-like (for drum triggers)

derive instance eqButtonStyle :: Eq ButtonStyle

type ButtonConfig =
  { mode :: ButtonMode
  , style :: ButtonStyle
  , size :: Int                 -- Pixels (square)
  , colorOff :: String          -- CSS color when off
  , colorOn :: String           -- CSS color when on
  , label :: String
  , radioGroup :: Maybe String  -- For radio button groups
  }

defaultButtonConfig :: ButtonConfig
defaultButtonConfig =
  { mode: ButtonToggle
  , style: ButtonFlat
  , size: 40
  , colorOff: "#333333"
  , colorOn: "#00ff88"
  , label: ""
  , radioGroup: Nothing
  }

-- | A button control
data Button = Button
  { id :: ControlId
  , pressed :: Boolean
  , config :: ButtonConfig
  , midiMapping :: Maybe MidiMapping
  }

derive instance eqButton :: Eq Button

mkButton :: ControlId -> ButtonConfig -> Button
mkButton id config = Button
  { id
  , pressed: false
  , config
  , midiMapping: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                         // pad
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity-sensitive pad (drum pad / Launchpad style)
type PadConfig =
  { size :: Int                 -- Pixels (square)
  , colorOff :: String
  , colorOn :: String
  , colorVelocity :: Boolean    -- Color intensity follows velocity
  , showLabel :: Boolean
  , label :: String
  }

defaultPadConfig :: PadConfig
defaultPadConfig =
  { size: 60
  , colorOff: "#222222"
  , colorOn: "#ff4444"
  , colorVelocity: true
  , showLabel: false
  , label: ""
  }

data Pad = Pad
  { id :: ControlId
  , velocity :: ControlValue    -- 0.0 = off, 1.0 = max velocity
  , config :: PadConfig
  , midiNote :: Maybe Int       -- MIDI note number (0-127)
  }

derive instance eqPad :: Eq Pad

mkPad :: ControlId -> PadConfig -> Pad
mkPad id config = Pad
  { id
  , velocity: ControlValue 0.0
  , config
  , midiNote: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // pad grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid size (e.g., 8x8 for Launchpad, 4x4 for MPC)
data GridSize = GridSize Int Int  -- rows x columns

derive instance eqGridSize :: Eq GridSize

mkGridSize :: Int -> Int -> Maybe GridSize
mkGridSize rows cols
  | rows >= 1 && rows <= 16 && cols >= 1 && cols <= 16 = 
      Just (GridSize rows cols)
  | otherwise = Nothing

-- | A grid of pads
data PadGrid = PadGrid
  { id :: ControlId
  , size :: GridSize
  , pads :: Array Pad
  , spacing :: Int              -- Gap between pads in pixels
  }

derive instance eqPadGrid :: Eq PadGrid

mkPadGrid :: ControlId -> GridSize -> PadConfig -> PadGrid
mkPadGrid id size@(GridSize rows cols) padConfig = PadGrid
  { id
  , size
  , pads: replicate (rows * cols) (mkPad (mkControlId "pad") padConfig)
  , spacing: 4
  }

-- | Get pad at grid position (row, col)
gridPadAt :: PadGrid -> Int -> Int -> Maybe Pad
gridPadAt (PadGrid g) row col = 
  let (GridSize _ cols) = g.size
      idx = row * cols + col
  in index g.pads idx

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // wheel
-- ═════════════════════════════════════════════════════════════════════════════

data WheelType
  = WheelPitchBend     -- Spring-return to center
  | WheelMod          -- Stays where you leave it
  | WheelExpression    -- Foot controller style

derive instance eqWheelType :: Eq WheelType

type WheelConfig =
  { wheelType :: WheelType
  , springReturn :: Boolean     -- Return to center on release
  , height :: Int               -- Pixels
  , label :: String
  }

data Wheel = Wheel
  { id :: ControlId
  , range :: ControlRange
  , value :: ControlValue
  , config :: WheelConfig
  , midiMapping :: Maybe MidiMapping
  }

derive instance eqWheel :: Eq Wheel

mkWheel :: ControlId -> WheelType -> Wheel
mkWheel id wheelType = Wheel
  { id
  , range: ControlRange { min: -1.0, max: 1.0, default: 0.0 }
  , value: ControlValue 0.5  -- Center position in normalized
  , config: 
      { wheelType
      , springReturn: wheelType == WheelPitchBend
      , height: 120
      , label: case wheelType of
          WheelPitchBend -> "Pitch"
          WheelMod -> "Mod"
          WheelExpression -> "Expr"
      }
  , midiMapping: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // switch
-- ═════════════════════════════════════════════════════════════════════════════

type SwitchConfig =
  { positions :: Int            -- Number of positions (2-12)
  , labels :: Array String      -- Label per position
  , style :: SwitchStyle
  }

data SwitchStyle
  = SwitchRotary       -- Rotary selector
  | SwitchSlide        -- Slide switch
  | SwitchSegment      -- Segmented button row

derive instance eqSwitchStyle :: Eq SwitchStyle

data Switch = Switch
  { id :: ControlId
  , position :: Int             -- Current position (0-indexed)
  , config :: SwitchConfig
  , midiMapping :: Maybe MidiMapping
  }

derive instance eqSwitch :: Eq Switch

mkSwitch :: ControlId -> SwitchConfig -> Switch
mkSwitch id config = Switch
  { id
  , position: 0
  , config
  , midiMapping: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // xy pad
-- ═════════════════════════════════════════════════════════════════════════════

type XYPadConfig =
  { size :: Int                 -- Square size in pixels
  , xRange :: ControlRange
  , yRange :: ControlRange
  , showCrosshair :: Boolean
  , showValue :: Boolean
  , labelX :: String
  , labelY :: String
  }

data XYPad = XYPad
  { id :: ControlId
  , x :: ControlValue
  , y :: ControlValue
  , config :: XYPadConfig
  , midiMappingX :: Maybe MidiMapping
  , midiMappingY :: Maybe MidiMapping
  }

derive instance eqXYPad :: Eq XYPad

mkXYPad :: ControlId -> XYPadConfig -> XYPad
mkXYPad id config = XYPad
  { id
  , x: ControlValue 0.5
  , y: ControlValue 0.5
  , config
  , midiMappingX: Nothing
  , midiMappingY: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // encoder
-- ═════════════════════════════════════════════════════════════════════════════

type EncoderConfig =
  { style :: KnobStyle          -- Reuse knob visuals
  , clickable :: Boolean        -- Push to click
  , acceleration :: Boolean     -- Faster turn = bigger jumps
  , detents :: Maybe Int        -- Number of detents (None = smooth)
  , label :: String
  }

-- | Endless rotary encoder (no min/max, wraps or accumulates)
data Encoder = Encoder
  { id :: ControlId
  , value :: Int                -- Accumulated ticks (can be negative)
  , config :: EncoderConfig
  , midiMapping :: Maybe MidiMapping
  }

derive instance eqEncoder :: Eq Encoder

mkEncoder :: ControlId -> EncoderConfig -> Encoder
mkEncoder id config = Encoder
  { id
  , value: 0
  , config
  , midiMapping: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // midi mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | MIDI CC number (0-127)
newtype MidiCC = MidiCC Int

derive instance eqMidiCC :: Eq MidiCC

mkMidiCC :: Int -> Maybe MidiCC
mkMidiCC cc
  | cc >= 0 && cc <= 127 = Just (MidiCC cc)
  | otherwise = Nothing

-- | MIDI channel (1-16, stored as 0-15)
newtype MidiChannel = MidiChannel Int

derive instance eqMidiChannel :: Eq MidiChannel

mkMidiChannel :: Int -> Maybe MidiChannel
mkMidiChannel ch
  | ch >= 1 && ch <= 16 = Just (MidiChannel (ch - 1))
  | otherwise = Nothing

-- | MIDI mapping for a control
data MidiMapping = MidiMapping
  { channel :: MidiChannel
  , cc :: MidiCC
  , learn :: Boolean            -- In learn mode?
  }

derive instance eqMidiMapping :: Eq MidiMapping
