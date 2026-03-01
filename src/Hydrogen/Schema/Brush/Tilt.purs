-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brush // tilt
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brush Tilt — Pen tilt dynamics for brush strokes.
-- |
-- | ## Design Philosophy
-- |
-- | Tilt describes the angle of a stylus relative to the drawing surface.
-- | This enables natural media simulation: a pencil held flat creates broad,
-- | soft shading strokes; a calligraphy brush rotates with the hand's angle;
-- | a marker tilted reveals its chisel edge.
-- |
-- | ## Device Agnosticism
-- |
-- | Tilt data comes from many sources:
-- | - **Stylus (EMR/AES)**: Direct tiltX/tiltY from pen sensor
-- | - **Apple Pencil**: Altitude/azimuth from internal IMU
-- | - **Smartphone/Watch**: Accelerometer pitch/roll, gyroscope heading
-- | - **VR Controllers**: Full 6DOF orientation quaternion
-- |
-- | The atoms and mappings work identically regardless of source — the runtime
-- | normalizes device-specific data to Altitude/Azimuth before applying mappings.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - **Atoms**: TiltX, TiltY, Altitude, Azimuth bounded newtypes
-- | - **Mapping**: TiltMapping configuration and presets
-- |
-- | ## Dependencies
-- |
-- | - Tilt.Atoms
-- | - Tilt.Mapping

module Hydrogen.Schema.Brush.Tilt
  ( module Atoms
  , module Mapping
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Brush.Tilt.Atoms
  ( TiltX(..)
  , tiltX
  , tiltXBounds
  , unwrapTiltX
  , noTiltX
  , maxTiltXLeft
  , maxTiltXRight
  , tiltXDebugInfo
  , TiltY(..)
  , tiltY
  , tiltYBounds
  , unwrapTiltY
  , noTiltY
  , maxTiltYForward
  , maxTiltYBack
  , tiltYDebugInfo
  , Altitude(..)
  , altitude
  , altitudeBounds
  , unwrapAltitude
  , flatAltitude
  , lowAltitude
  , midAltitude
  , perpendicularAltitude
  , altitudeDebugInfo
  , Azimuth(..)
  , azimuth
  , azimuthBounds
  , unwrapAzimuth
  , azimuthRight
  , azimuthDown
  , azimuthLeft
  , azimuthUp
  , azimuthDebugInfo
  ) as Atoms

import Hydrogen.Schema.Brush.Tilt.Mapping
  ( TiltMapping
  , defaultTiltMapping
  , tiltMappingDebugInfo
  , pencilShadingMapping
  , calligraphyMapping
  , airbrushMapping
  , markerMapping
  , disabledMapping
  , isFullyEnabled
  , isDisabled
  , affectsShape
  , affectsAppearance
  , showWithMapping
  ) as Mapping
