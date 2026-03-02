-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brush // input // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input Device Types — ADT for input device classification.
-- |
-- | ## Design Philosophy
-- |
-- | Input devices determine what dynamic data is available during brush strokes.
-- | This module defines the categorical types of input devices and stylus
-- | technologies that affect brush behavior.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Brush.Input.Types
  ( -- * Input Device
    InputDevice(..)
  , allInputDevices
  , inputDeviceDescription
  , inputDeviceDebugInfo
  , hasPressureCapability
  , hasTiltCapability
  , has3DCapability
  
  -- * Stylus Technology
  , StylusTechnology(..)
  , allStylusTechnologies
  , stylusTechnologyDescription
  , stylusTechnologyDebugInfo
  , requiresPower
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // input device
-- ═════════════════════════════════════════════════════════════════════════════

-- | Category of input device providing brush input.
-- | Determines what dynamic data (pressure, tilt, position) is available.
data InputDevice
  = Mouse              -- ^ Standard mouse, no pressure
  | Trackpad           -- ^ Laptop trackpad, force touch on some
  | Stylus             -- ^ Pressure-sensitive pen (professional tablet stylus)
  | Touch              -- ^ Finger on touchscreen
  | VRController       -- ^ 6DOF VR controller
  | VRHand             -- ^ Hand tracking in VR
  | Gamepad            -- ^ Analog stick input
  | MIDIController     -- ^ MIDI fader/knob input

derive instance eqInputDevice :: Eq InputDevice
derive instance ordInputDevice :: Ord InputDevice

instance showInputDevice :: Show InputDevice where
  show Mouse = "(InputDevice Mouse)"
  show Trackpad = "(InputDevice Trackpad)"
  show Stylus = "(InputDevice Stylus)"
  show Touch = "(InputDevice Touch)"
  show VRController = "(InputDevice VRController)"
  show VRHand = "(InputDevice VRHand)"
  show Gamepad = "(InputDevice Gamepad)"
  show MIDIController = "(InputDevice MIDIController)"

-- | All available input devices.
allInputDevices :: Array InputDevice
allInputDevices =
  [ Mouse
  , Trackpad
  , Stylus
  , Touch
  , VRController
  , VRHand
  , Gamepad
  , MIDIController
  ]

-- | Human-readable description of each input device.
inputDeviceDescription :: InputDevice -> String
inputDeviceDescription Mouse = "Standard mouse, position only, no pressure"
inputDeviceDescription Trackpad = "Laptop trackpad, may have force touch"
inputDeviceDescription Stylus = "Pressure-sensitive pen (professional tablet stylus, etc.)"
inputDeviceDescription Touch = "Finger on touchscreen, may have force touch"
inputDeviceDescription VRController = "6DOF VR controller with trigger pressure"
inputDeviceDescription VRHand = "Hand tracking in VR with pinch detection"
inputDeviceDescription Gamepad = "Analog stick input for brush control"
inputDeviceDescription MIDIController = "MIDI fader/knob for parameter control"

-- | Debug info string for input device (uses show and (<>)).
-- | Format: "(InputDevice <name> pressure:<bool> tilt:<bool> 3d:<bool>)"
inputDeviceDebugInfo :: InputDevice -> String
inputDeviceDebugInfo device = 
  show device 
    <> " pressure:" <> show (hasPressureCapability device)
    <> " tilt:" <> show (hasTiltCapability device)
    <> " 3d:" <> show (has3DCapability device)

-- | Does this device type support pressure input?
hasPressureCapability :: InputDevice -> Boolean
hasPressureCapability Mouse = false
hasPressureCapability Trackpad = true   -- Force Touch on some models
hasPressureCapability Stylus = true
hasPressureCapability Touch = true      -- 3D Touch / Force Touch on some
hasPressureCapability VRController = true
hasPressureCapability VRHand = true     -- Pinch pressure
hasPressureCapability Gamepad = true    -- Analog trigger
hasPressureCapability MIDIController = true

-- | Does this device type support tilt input?
hasTiltCapability :: InputDevice -> Boolean
hasTiltCapability Mouse = false
hasTiltCapability Trackpad = false
hasTiltCapability Stylus = true
hasTiltCapability Touch = false
hasTiltCapability VRController = false
hasTiltCapability VRHand = false
hasTiltCapability Gamepad = false
hasTiltCapability MIDIController = false

-- | Does this device type support 3D position input?
has3DCapability :: InputDevice -> Boolean
has3DCapability Mouse = false
has3DCapability Trackpad = false
has3DCapability Stylus = false
has3DCapability Touch = false
has3DCapability VRController = true
has3DCapability VRHand = true
has3DCapability Gamepad = false
has3DCapability MIDIController = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // stylus technology
-- ═════════════════════════════════════════════════════════════════════════════

-- | Technology type of pressure-sensitive stylus.
-- | Affects pressure resolution, tilt support, and power requirements.
data StylusTechnology
  = EMR               -- ^ Electromagnetic resonance no battery required
  | AES               -- ^ Active electrostatic requires battery
  | MPP               -- ^ Microsoft Pen Protocol, battery
  | USI               -- ^ Universal Stylus Initiative, battery
  | ApplePencil       -- ^ Apple proprietary, battery
  | Capacitive        -- ^ Passive capacitive, no features

derive instance eqStylusTechnology :: Eq StylusTechnology
derive instance ordStylusTechnology :: Ord StylusTechnology

instance showStylusTechnology :: Show StylusTechnology where
  show EMR = "(StylusTechnology EMR)"
  show AES = "(StylusTechnology AES)"
  show MPP = "(StylusTechnology MPP)"
  show USI = "(StylusTechnology USI)"
  show ApplePencil = "(StylusTechnology ApplePencil)"
  show Capacitive = "(StylusTechnology Capacitive)"

-- | All available stylus technologies.
allStylusTechnologies :: Array StylusTechnology
allStylusTechnologies =
  [ EMR
  , AES
  , MPP
  , USI
  , ApplePencil
  , Capacitive
  ]

-- | Human-readable description of each stylus technology.
stylusTechnologyDescription :: StylusTechnology -> String
stylusTechnologyDescription EMR = "Electromagnetic resonance, no battery required, up to 8192 levels"
stylusTechnologyDescription AES = "Active electrostatic, requires battery, up to 4096 levels"
stylusTechnologyDescription MPP = "Microsoft Pen Protocol, requires battery, up to 4096 levels"
stylusTechnologyDescription USI = "Universal Stylus Initiative, requires battery, up to 4096 levels"
stylusTechnologyDescription ApplePencil = "Apple proprietary, requires battery, up to 4096 levels"
stylusTechnologyDescription Capacitive = "Passive capacitive tip, no pressure or tilt support"

-- | Debug info string for stylus technology (uses show and (<>)).
-- | Format: "(StylusTechnology <name> requiresPower:<bool>)"
stylusTechnologyDebugInfo :: StylusTechnology -> String
stylusTechnologyDebugInfo tech = 
  show tech <> " requiresPower:" <> show (requiresPower tech)

-- | Does this stylus technology require power?
requiresPower :: StylusTechnology -> Boolean
requiresPower EMR = false
requiresPower AES = true
requiresPower MPP = true
requiresPower USI = true
requiresPower ApplePencil = true
requiresPower Capacitive = false
