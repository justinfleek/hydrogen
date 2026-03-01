-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // brush // tilt // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tilt Atoms — Bounded numeric parameters for pen tilt dynamics.
-- |
-- | ## Design Philosophy
-- |
-- | Tilt describes the angle of a stylus relative to the drawing surface.
-- | Two coordinate systems are supported:
-- |
-- | 1. **Cartesian (TiltX, TiltY)**: Decomposed horizontal/vertical tilt
-- | 2. **Polar (Altitude, Azimuth)**: Angle from surface + direction
-- |
-- | Most hardware reports Cartesian; polar is often more intuitive for
-- | brush behavior (altitude = how flat, azimuth = which direction).
-- |
-- | ## Key Properties
-- |
-- | - **TiltX**: Horizontal tilt angle (-90 to 90 degrees, clamps)
-- | - **TiltY**: Vertical tilt angle (-90 to 90 degrees, clamps)
-- | - **Altitude**: Angle from surface (0=flat, 90=perpendicular, clamps)
-- | - **Azimuth**: Direction of tilt (0-360 degrees, wraps)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Tilt.Atoms
  ( -- * TiltX (-90 to 90 degrees)
    TiltX(..)
  , tiltX
  , tiltXBounds
  , unwrapTiltX
  , noTiltX
  , maxTiltXLeft
  , maxTiltXRight
  , tiltXDebugInfo
  
  -- * TiltY (-90 to 90 degrees)
  , TiltY(..)
  , tiltY
  , tiltYBounds
  , unwrapTiltY
  , noTiltY
  , maxTiltYForward
  , maxTiltYBack
  , tiltYDebugInfo
  
  -- * Altitude (0 to 90 degrees)
  , Altitude(..)
  , altitude
  , altitudeBounds
  , unwrapAltitude
  , flatAltitude
  , lowAltitude
  , midAltitude
  , perpendicularAltitude
  , altitudeDebugInfo
  
  -- * Azimuth (0 to 360 degrees)
  , Azimuth(..)
  , azimuth
  , azimuthBounds
  , unwrapAzimuth
  , azimuthRight
  , azimuthDown
  , azimuthLeft
  , azimuthUp
  , azimuthDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // tilt x
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal tilt angle in degrees (-90 to 90).
-- | -90 = pen tilted fully left
-- |   0 = pen vertical (no horizontal tilt)
-- | +90 = pen tilted fully right
newtype TiltX = TiltX Number

derive instance eqTiltX :: Eq TiltX
derive instance ordTiltX :: Ord TiltX

instance showTiltX :: Show TiltX where
  show (TiltX t) = "(TiltX " <> show t <> "deg)"

-- | Bounded specification for TiltX.
tiltXBounds :: Bounded.NumberBounds
tiltXBounds = Bounded.numberBounds (-90.0) 90.0 Bounded.Clamps
  "tiltX" "Horizontal tilt angle in degrees (-90 to 90)"

-- | Create a TiltX value (clamped to -90 to 90).
tiltX :: Number -> TiltX
tiltX n = TiltX (Bounded.clampNumber (-90.0) 90.0 n)

-- | Extract the raw TiltX value.
unwrapTiltX :: TiltX -> Number
unwrapTiltX (TiltX t) = t

-- | No horizontal tilt (pen vertical).
noTiltX :: TiltX
noTiltX = TiltX 0.0

-- | Maximum tilt to the left (-90 degrees).
maxTiltXLeft :: TiltX
maxTiltXLeft = TiltX (-90.0)

-- | Maximum tilt to the right (+90 degrees).
maxTiltXRight :: TiltX
maxTiltXRight = TiltX 90.0

-- | Debug info string for TiltX.
tiltXDebugInfo :: TiltX -> String
tiltXDebugInfo t = show t <> " raw:" <> show (unwrapTiltX t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // tilt y
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertical tilt angle in degrees (-90 to 90).
-- | -90 = pen tilted fully toward user (back)
-- |   0 = pen vertical (no vertical tilt)
-- | +90 = pen tilted fully away from user (forward)
newtype TiltY = TiltY Number

derive instance eqTiltY :: Eq TiltY
derive instance ordTiltY :: Ord TiltY

instance showTiltY :: Show TiltY where
  show (TiltY t) = "(TiltY " <> show t <> "deg)"

-- | Bounded specification for TiltY.
tiltYBounds :: Bounded.NumberBounds
tiltYBounds = Bounded.numberBounds (-90.0) 90.0 Bounded.Clamps
  "tiltY" "Vertical tilt angle in degrees (-90 to 90)"

-- | Create a TiltY value (clamped to -90 to 90).
tiltY :: Number -> TiltY
tiltY n = TiltY (Bounded.clampNumber (-90.0) 90.0 n)

-- | Extract the raw TiltY value.
unwrapTiltY :: TiltY -> Number
unwrapTiltY (TiltY t) = t

-- | No vertical tilt (pen vertical).
noTiltY :: TiltY
noTiltY = TiltY 0.0

-- | Maximum tilt forward (away from user, +90 degrees).
maxTiltYForward :: TiltY
maxTiltYForward = TiltY 90.0

-- | Maximum tilt back (toward user, -90 degrees).
maxTiltYBack :: TiltY
maxTiltYBack = TiltY (-90.0)

-- | Debug info string for TiltY.
tiltYDebugInfo :: TiltY -> String
tiltYDebugInfo t = show t <> " raw:" <> show (unwrapTiltY t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // altitude
-- ═════════════════════════════════════════════════════════════════════════════

-- | Altitude angle in degrees (0 to 90).
-- | The angle between the pen and the drawing surface:
-- |  0 = pen flat against surface (parallel)
-- | 90 = pen perpendicular to surface (straight up)
-- |
-- | This is computed from TiltX and TiltY:
-- |   altitude = 90 - sqrt(tiltX^2 + tiltY^2)
-- |
-- | Altitude is intuitive for brush behavior: lower altitude = flatter pen
-- | = broader strokes (like pencil shading).
newtype Altitude = Altitude Number

derive instance eqAltitude :: Eq Altitude
derive instance ordAltitude :: Ord Altitude

instance showAltitude :: Show Altitude where
  show (Altitude a) = "(Altitude " <> show a <> "deg)"

-- | Bounded specification for Altitude.
altitudeBounds :: Bounded.NumberBounds
altitudeBounds = Bounded.numberBounds 0.0 90.0 Bounded.Clamps
  "altitude" "Pen altitude angle in degrees (0=flat, 90=perpendicular)"

-- | Create an Altitude value (clamped to 0-90).
altitude :: Number -> Altitude
altitude n = Altitude (Bounded.clampNumber 0.0 90.0 n)

-- | Extract the raw Altitude value.
unwrapAltitude :: Altitude -> Number
unwrapAltitude (Altitude a) = a

-- | Pen flat against surface (0 degrees).
flatAltitude :: Altitude
flatAltitude = Altitude 0.0

-- | Low altitude, pen nearly flat (20 degrees).
lowAltitude :: Altitude
lowAltitude = Altitude 20.0

-- | Mid altitude, moderate tilt (45 degrees).
midAltitude :: Altitude
midAltitude = Altitude 45.0

-- | Pen perpendicular to surface (90 degrees).
perpendicularAltitude :: Altitude
perpendicularAltitude = Altitude 90.0

-- | Debug info string for Altitude.
altitudeDebugInfo :: Altitude -> String
altitudeDebugInfo a = show a <> " raw:" <> show (unwrapAltitude a)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // azimuth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Azimuth angle in degrees (0 to 360, wraps).
-- | The compass direction the pen is pointing:
-- |   0/360 = pen pointing right (3 o'clock)
-- |      90 = pen pointing down (6 o'clock)
-- |     180 = pen pointing left (9 o'clock)
-- |     270 = pen pointing up (12 o'clock)
-- |
-- | Azimuth determines which direction a tilted brush "faces",
-- | affecting where the wide edge of a calligraphy stroke appears.
newtype Azimuth = Azimuth Number

derive instance eqAzimuth :: Eq Azimuth
derive instance ordAzimuth :: Ord Azimuth

instance showAzimuth :: Show Azimuth where
  show (Azimuth a) = "(Azimuth " <> show a <> "deg)"

-- | Bounded specification for Azimuth.
azimuthBounds :: Bounded.NumberBounds
azimuthBounds = Bounded.numberBounds 0.0 360.0 Bounded.Wraps
  "azimuth" "Pen azimuth angle in degrees (0-360, wraps)"

-- | Create an Azimuth value (wraps at 360).
azimuth :: Number -> Azimuth
azimuth n = Azimuth (Bounded.wrapNumber 0.0 360.0 n)

-- | Extract the raw Azimuth value.
unwrapAzimuth :: Azimuth -> Number
unwrapAzimuth (Azimuth a) = a

-- | Pen pointing right (0 degrees, 3 o'clock).
azimuthRight :: Azimuth
azimuthRight = Azimuth 0.0

-- | Pen pointing down (90 degrees, 6 o'clock).
azimuthDown :: Azimuth
azimuthDown = Azimuth 90.0

-- | Pen pointing left (180 degrees, 9 o'clock).
azimuthLeft :: Azimuth
azimuthLeft = Azimuth 180.0

-- | Pen pointing up (270 degrees, 12 o'clock).
azimuthUp :: Azimuth
azimuthUp = Azimuth 270.0

-- | Debug info string for Azimuth.
azimuthDebugInfo :: Azimuth -> String
azimuthDebugInfo a = show a <> " raw:" <> show (unwrapAzimuth a)
