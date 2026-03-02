-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // brush // input // capabilities
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Device Capabilities — Bounded parameters for input device features.
-- |
-- | ## Design Philosophy
-- |
-- | Device capabilities determine what input data is available for brush
-- | dynamics. This module provides bounded types for pressure levels, tilt
-- | range, hover distance, and touch point counts.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Input.Capabilities
  ( -- * Pressure Levels
    PressureLevels(..)
  , pressureLevels
  , pressureLevelsBounds
  , unwrapPressureLevels
  , noPressureLevels
  , basicPressureLevels
  , standardPressureLevels
  , professionalPressureLevels
  
  -- * Tilt Range
  , TiltRange(..)
  , tiltRange
  , tiltRangeBounds
  , unwrapTiltRange
  , noTiltRange
  , standardTiltRange
  , wideTiltRange
  
  -- * Hover Height
  , HoverHeight(..)
  , hoverHeight
  , hoverHeightBounds
  , unwrapHoverHeight
  , noHoverHeight
  , standardHoverHeight
  
  -- * Touch Points
  , TouchPoints(..)
  , touchPoints
  , touchPointsBounds
  , unwrapTouchPoints
  , noTouchPoints
  , standardTouchPoints
  , maxTouchPoints
  
  -- * Device Capabilities Record
  , DeviceCapabilities
  , deviceCapabilities
  , mouseCapabilities
  , trackpadCapabilities
  , stylusCapabilities
  , touchCapabilities
  , vrControllerCapabilities
  , vrHandCapabilities
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

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // pressure levels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pressure sensitivity levels (0-8192).
-- | 0 = no pressure, 512 = basic, 2048 = standard, 8192 = professional.
newtype PressureLevels = PressureLevels Int

derive instance eqPressureLevels :: Eq PressureLevels
derive instance ordPressureLevels :: Ord PressureLevels

instance showPressureLevels :: Show PressureLevels where
  show (PressureLevels p) = "PressureLevels " <> show p

-- | Bounded specification for pressure levels.
pressureLevelsBounds :: Bounded.IntBounds
pressureLevelsBounds = Bounded.intBounds 0 8192 Bounded.Clamps
  "pressureLevels" "Pressure sensitivity levels (0-8192)"

-- | Create pressure levels value (clamped to 0-8192).
pressureLevels :: Int -> PressureLevels
pressureLevels n = PressureLevels (Bounded.clampInt 0 8192 n)

-- | Extract the raw pressure levels value.
unwrapPressureLevels :: PressureLevels -> Int
unwrapPressureLevels (PressureLevels p) = p

-- | No pressure sensitivity (mouse).
noPressureLevels :: PressureLevels
noPressureLevels = PressureLevels 0

-- | Basic pressure (256-512 levels).
basicPressureLevels :: PressureLevels
basicPressureLevels = PressureLevels 512

-- | Standard pressure (2048 levels, most tablets).
standardPressureLevels :: PressureLevels
standardPressureLevels = PressureLevels 2048

-- | Professional pressure (8192 levels, professional tablet).
professionalPressureLevels :: PressureLevels
professionalPressureLevels = PressureLevels 8192

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tilt range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum detectable tilt angle in degrees (0-90).
-- | 0 = no tilt detection, 60-80 = typical stylus range.
newtype TiltRange = TiltRange Number

derive instance eqTiltRange :: Eq TiltRange
derive instance ordTiltRange :: Ord TiltRange

instance showTiltRange :: Show TiltRange where
  show (TiltRange t) = "TiltRange " <> show t <> "°"

-- | Bounded specification for tilt range.
tiltRangeBounds :: Bounded.NumberBounds
tiltRangeBounds = Bounded.numberBounds 0.0 90.0 Bounded.Clamps
  "tiltRange" "Maximum tilt angle in degrees (0-90)"

-- | Create tilt range value (clamped to 0-90).
tiltRange :: Number -> TiltRange
tiltRange n = TiltRange (Bounded.clampNumber 0.0 90.0 n)

-- | Extract the raw tilt range value.
unwrapTiltRange :: TiltRange -> Number
unwrapTiltRange (TiltRange t) = t

-- | No tilt detection (mouse, trackpad).
noTiltRange :: TiltRange
noTiltRange = TiltRange 0.0

-- | Standard tilt range (60°, most styluses).
standardTiltRange :: TiltRange
standardTiltRange = TiltRange 60.0

-- | Wide tilt range (80°, professional styluses).
wideTiltRange :: TiltRange
wideTiltRange = TiltRange 80.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover height
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum hover detection distance in millimeters (0-50).
-- | 0 = no hover, 10-20 = typical stylus hover range.
newtype HoverHeight = HoverHeight Number

derive instance eqHoverHeight :: Eq HoverHeight
derive instance ordHoverHeight :: Ord HoverHeight

instance showHoverHeight :: Show HoverHeight where
  show (HoverHeight h) = "HoverHeight " <> show h <> "mm"

-- | Bounded specification for hover height.
hoverHeightBounds :: Bounded.NumberBounds
hoverHeightBounds = Bounded.numberBounds 0.0 50.0 Bounded.Clamps
  "hoverHeight" "Maximum hover detection in millimeters (0-50)"

-- | Create hover height value (clamped to 0-50).
hoverHeight :: Number -> HoverHeight
hoverHeight n = HoverHeight (Bounded.clampNumber 0.0 50.0 n)

-- | Extract the raw hover height value.
unwrapHoverHeight :: HoverHeight -> Number
unwrapHoverHeight (HoverHeight h) = h

-- | No hover detection (mouse, most touch).
noHoverHeight :: HoverHeight
noHoverHeight = HoverHeight 0.0

-- | Standard hover height (10mm, most styluses).
standardHoverHeight :: HoverHeight
standardHoverHeight = HoverHeight 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // touch points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum simultaneous touch points (0-20).
-- | 0 = no touch, 5 = typical mobile, 10 = professional touch device.
newtype TouchPoints = TouchPoints Int

derive instance eqTouchPoints :: Eq TouchPoints
derive instance ordTouchPoints :: Ord TouchPoints

instance showTouchPoints :: Show TouchPoints where
  show (TouchPoints t) = "TouchPoints " <> show t

-- | Bounded specification for touch points.
touchPointsBounds :: Bounded.IntBounds
touchPointsBounds = Bounded.intBounds 0 20 Bounded.Clamps
  "touchPoints" "Maximum simultaneous touch points (0-20)"

-- | Create touch points value (clamped to 0-20).
touchPoints :: Int -> TouchPoints
touchPoints n = TouchPoints (Bounded.clampInt 0 20 n)

-- | Extract the raw touch points value.
unwrapTouchPoints :: TouchPoints -> Int
unwrapTouchPoints (TouchPoints t) = t

-- | No touch capability (mouse, stylus-only).
noTouchPoints :: TouchPoints
noTouchPoints = TouchPoints 0

-- | Standard touch (5 points, typical mobile).
standardTouchPoints :: TouchPoints
standardTouchPoints = TouchPoints 5

-- | Maximum touch (10 points, professional touch).
maxTouchPoints :: TouchPoints
maxTouchPoints = TouchPoints 10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // device capabilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete device capability specification.
type DeviceCapabilities =
  { hasPressure :: Boolean
  , pressureLevels :: PressureLevels
  , hasTilt :: Boolean
  , tiltRange :: TiltRange
  , hasRotation :: Boolean
  , hasPosition :: Boolean
  , hasPosition3D :: Boolean
  , hasOrientation :: Boolean
  , hasVelocity :: Boolean
  , hasMultitouch :: Boolean
  , maxTouchPoints :: TouchPoints
  , hasForceTouch :: Boolean
  , hasHover :: Boolean
  , hoverHeight :: HoverHeight
  }

-- | Create device capabilities with all parameters.
deviceCapabilities
  :: Boolean
  -> PressureLevels
  -> Boolean
  -> TiltRange
  -> Boolean
  -> Boolean
  -> Boolean
  -> Boolean
  -> Boolean
  -> Boolean
  -> TouchPoints
  -> Boolean
  -> Boolean
  -> HoverHeight
  -> DeviceCapabilities
deviceCapabilities 
    hasPressure' 
    pressureLevels' 
    hasTilt' 
    tiltRange' 
    hasRotation' 
    hasPosition' 
    hasPosition3D' 
    hasOrientation' 
    hasVelocity' 
    hasMultitouch' 
    maxTouchPoints' 
    hasForceTouch' 
    hasHover' 
    hoverHeight' =
  { hasPressure: hasPressure'
  , pressureLevels: pressureLevels'
  , hasTilt: hasTilt'
  , tiltRange: tiltRange'
  , hasRotation: hasRotation'
  , hasPosition: hasPosition'
  , hasPosition3D: hasPosition3D'
  , hasOrientation: hasOrientation'
  , hasVelocity: hasVelocity'
  , hasMultitouch: hasMultitouch'
  , maxTouchPoints: maxTouchPoints'
  , hasForceTouch: hasForceTouch'
  , hasHover: hasHover'
  , hoverHeight: hoverHeight'
  }

-- | Mouse capabilities: position only.
mouseCapabilities :: DeviceCapabilities
mouseCapabilities =
  { hasPressure: false
  , pressureLevels: noPressureLevels
  , hasTilt: false
  , tiltRange: noTiltRange
  , hasRotation: false
  , hasPosition: true
  , hasPosition3D: false
  , hasOrientation: false
  , hasVelocity: true
  , hasMultitouch: false
  , maxTouchPoints: noTouchPoints
  , hasForceTouch: false
  , hasHover: false
  , hoverHeight: noHoverHeight
  }

-- | Trackpad capabilities: position, multi-touch, possibly force touch.
trackpadCapabilities :: DeviceCapabilities
trackpadCapabilities =
  { hasPressure: true
  , pressureLevels: basicPressureLevels
  , hasTilt: false
  , tiltRange: noTiltRange
  , hasRotation: false
  , hasPosition: true
  , hasPosition3D: false
  , hasOrientation: false
  , hasVelocity: true
  , hasMultitouch: true
  , maxTouchPoints: standardTouchPoints
  , hasForceTouch: true
  , hasHover: false
  , hoverHeight: noHoverHeight
  }

-- | Professional stylus capabilities: pressure, tilt, hover.
stylusCapabilities :: DeviceCapabilities
stylusCapabilities =
  { hasPressure: true
  , pressureLevels: professionalPressureLevels
  , hasTilt: true
  , tiltRange: wideTiltRange
  , hasRotation: true
  , hasPosition: true
  , hasPosition3D: false
  , hasOrientation: false
  , hasVelocity: true
  , hasMultitouch: false
  , maxTouchPoints: noTouchPoints
  , hasForceTouch: false
  , hasHover: true
  , hoverHeight: standardHoverHeight
  }

-- | Touch capabilities: multi-touch, possibly force touch.
touchCapabilities :: DeviceCapabilities
touchCapabilities =
  { hasPressure: true
  , pressureLevels: basicPressureLevels
  , hasTilt: false
  , tiltRange: noTiltRange
  , hasRotation: false
  , hasPosition: true
  , hasPosition3D: false
  , hasOrientation: false
  , hasVelocity: true
  , hasMultitouch: true
  , maxTouchPoints: standardTouchPoints
  , hasForceTouch: true
  , hasHover: false
  , hoverHeight: noHoverHeight
  }

-- | VR controller capabilities: 6DOF, trigger pressure.
vrControllerCapabilities :: DeviceCapabilities
vrControllerCapabilities =
  { hasPressure: true
  , pressureLevels: basicPressureLevels
  , hasTilt: false
  , tiltRange: noTiltRange
  , hasRotation: false
  , hasPosition: true
  , hasPosition3D: true
  , hasOrientation: true
  , hasVelocity: true
  , hasMultitouch: false
  , maxTouchPoints: noTouchPoints
  , hasForceTouch: false
  , hasHover: true
  , hoverHeight: noHoverHeight
  }

-- | VR hand tracking capabilities: 6DOF, pinch pressure.
vrHandCapabilities :: DeviceCapabilities
vrHandCapabilities =
  { hasPressure: true
  , pressureLevels: PressureLevels 64
  , hasTilt: false
  , tiltRange: noTiltRange
  , hasRotation: false
  , hasPosition: true
  , hasPosition3D: true
  , hasOrientation: true
  , hasVelocity: true
  , hasMultitouch: true
  , maxTouchPoints: standardTouchPoints
  , hasForceTouch: false
  , hasHover: true
  , hoverHeight: noHoverHeight
  }
