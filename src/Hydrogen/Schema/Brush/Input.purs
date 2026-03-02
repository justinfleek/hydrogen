-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // brush // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Input — Input device types, capabilities, and graded channels.
-- |
-- | ## Design Philosophy
-- |
-- | Input devices determine what dynamic data is available during brush strokes.
-- | A mouse provides position only. A stylus provides pressure, tilt, rotation.
-- | A VR controller provides full 6DOF spatial data.
-- |
-- | Graded input channels provide a unified abstraction for heterogeneous input
-- | sources — from hardware sensors to neural interfaces to AI agents. The grade
-- | tracks provenance and certainty, enabling agents to reason about trust.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Types**: InputDevice ADT and StylusTechnology
-- | - **Capabilities**: DeviceCapabilities record and presets
-- | - **Channel**: Import directly from Hydrogen.Schema.Brush.Input.Channel
-- |   (not re-exported due to constructor name overlap with Types)
-- |
-- | ## Dependencies
-- |
-- | - Input.Types
-- | - Input.Capabilities
-- | - Input.Channel (import directly when graded channels are needed)

module Hydrogen.Schema.Brush.Input
  ( module Types
  , module Capabilities
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Input.Types 
  ( InputDevice(Mouse, Trackpad, Stylus, Touch, VRController, VRHand, Gamepad, MIDIController)
  , StylusTechnology(EMR, AES, MPP, USI, ApplePencil, Capacitive)
  , allInputDevices
  , allStylusTechnologies
  , has3DCapability
  , hasPressureCapability
  , hasTiltCapability
  , inputDeviceDebugInfo
  , inputDeviceDescription
  , requiresPower
  , stylusTechnologyDebugInfo
  , stylusTechnologyDescription
  ) as Types

import Hydrogen.Schema.Brush.Input.Capabilities 
  ( DeviceCapabilities
  , HoverHeight(HoverHeight)
  , PressureLevels(PressureLevels)
  , TiltRange(TiltRange)
  , TouchPoints(TouchPoints)
  , basicPressureLevels
  , deviceCapabilities
  , hoverHeight
  , hoverHeightBounds
  , maxTouchPoints
  , mouseCapabilities
  , noHoverHeight
  , noPressureLevels
  , noTiltRange
  , noTouchPoints
  , pressureLevels
  , pressureLevelsBounds
  , professionalPressureLevels
  , standardHoverHeight
  , standardPressureLevels
  , standardTiltRange
  , standardTouchPoints
  , stylusCapabilities
  , tiltRange
  , tiltRangeBounds
  , touchCapabilities
  , touchPoints
  , touchPointsBounds
  , trackpadCapabilities
  , unwrapHoverHeight
  , unwrapPressureLevels
  , unwrapTiltRange
  , unwrapTouchPoints
  , vrControllerCapabilities
  , vrHandCapabilities
  , wideTiltRange
  ) as Capabilities

-- Note: Hydrogen.Schema.Brush.Input.Channel is NOT re-exported here due to
-- constructor name conflicts (Mouse, Stylus, etc. exist in both InputDevice
-- and SensorSource). Import Channel directly when graded channels are needed:
--
--   import Hydrogen.Schema.Brush.Input.Channel as Channel
