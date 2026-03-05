-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // motion // gesture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gesture — re-exports pure gesture types from Schema.
-- |
-- | Gesture recognition states and types are pure data structures.
-- | The Rust WASM runtime handles touch/pointer event processing and
-- | produces gesture state values in these formats.
-- |
-- | ## Architecture
-- |
-- | ```
-- | PureScript (Schema)     → Pure types (GesturePhase, TapState, SwipeState, etc.)
-- | Rust WASM (Runtime)     → Touch/pointer event processing, velocity tracking
-- | ```
-- |
-- | ## Gesture Types
-- |
-- | - **Tap**: Single, double, triple tap detection
-- | - **LongPress**: Press and hold recognition
-- | - **Swipe**: Directional swipe with velocity
-- | - **Pan**: Continuous drag with delta tracking
-- | - **Pinch**: Two-finger zoom gestures
-- | - **Rotate**: Two-finger rotation gestures
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Gesture as G
-- |
-- | -- Configure pan gesture (pure data)
-- | panConfig :: PanConfig
-- | panConfig = G.defaultPanConfig
-- |   { threshold = 10.0
-- |   , direction = G.DirectionAll
-- |   }
-- |
-- | -- Attach to element for runtime handling
-- | draggableElement = Element.withGesture panConfig OnPan baseElement
-- |
-- | -- Handle gesture state in update
-- | update (OnPan panState) model =
-- |   if G.isActive panState.phase
-- |     then model { position = model.position + panState.delta }
-- |     else model
-- | ```
-- |
-- | ## Migration from FFI version
-- |
-- | Old (effectful, required JS FFI):
-- | ```purescript
-- | gesture <- G.createPanGesture element callbacks
-- | ```
-- |
-- | New (pure config, runtime handles events):
-- | ```purescript
-- | config = G.defaultPanConfig
-- | element = Element.withGesture config OnGesture baseElement
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Gestural.Gesture (canonical types)
-- |
-- | ## Dependents
-- | - Draggable components
-- | - Zoomable views
-- | - Swipe navigation

module Hydrogen.Motion.Gesture
  ( -- * Re-exports from Schema.Gestural.Gesture
    module SchemaGesture
    -- * Two-finger gesture utilities
  , Point
  , TwoFingerData
  , computeTwoFingerData
  ) where

import Prelude
  ( (*), (-), (+), (/)
  )

import Data.Number (sqrt, atan2) as Num

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Gesture
  ( GesturePhase(Possible, Began, Changed, Ended, Cancelled, Failed)
  , isPossible
  , isBegan
  , isChanged
  , isEnded
  , isCancelled
  , isFailed
  , isActive
  , isTerminal
  , TapCount(TapCount)
  , tapCount
  , singleTap
  , doubleTap
  , tripleTap
  , unwrapTapCount
  , isSingleTap
  , isDoubleTap
  , isTripleTap
  , TapState
  , tapState
  , noTap
  , tapPosition
  , isTapRecognized
  , isSingleTap
  , isDoubleTap
  , isTripleTap
  , LongPressState
  , longPressState
  , noLongPress
  , longPressPosition
  , updateLongPressDuration
  , isLongPressTriggered
  , isLongPressActive
  , SwipeDirection(SwipeLeft, SwipeRight, SwipeUp, SwipeDown)
  , SwipeState
  , swipeState
  , noSwipe
  , swipeVelocity
  , isSwipeRecognized
  , PanState
  , panState
  , noPan
  , updatePanPosition
  , panTranslation
  , panVelocity
  , isPanning
  , panDistance
  , PinchGesture
  , pinchGesture
  , noPinchGesture
  , pinchGestureScale
  , pinchGestureVelocity
  , pinchGestureCenter
  , isPinchActive
  , RotateGesture
  , rotateGesture
  , noRotateGesture
  , rotateGestureAngle
  , rotateGestureVelocity
  , rotateGestureCenter
  , isRotateActive
  , normalizeAngle
  , GestureState
  , initialGestureState
  , resetGestures
  , hasActiveGesture
  , hasCompletedGesture
  , updateTapState
  , updateLongPressState
  , updateSwipeState
  , updatePanState
  , updatePinchState
  , updateRotateState
  ) as SchemaGesture

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // two-finger gesture utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D point.
type Point = { x :: Number, y :: Number }

-- | Data computed from two touch points.
-- |
-- | Used for pan/pinch/rotate gesture recognition.
type TwoFingerData =
  { center :: Point        -- ^ Center point between the two touches
  , distance :: Number     -- ^ Distance between the two touches
  , angle :: Number        -- ^ Angle of the line between touches (degrees)
  }

-- | Compute two-finger data from two touch points.
-- |
-- | ```purescript
-- | let data = computeTwoFingerData point1 point2
-- | -- data.center = midpoint
-- | -- data.distance = distance between points
-- | -- data.angle = angle in degrees (0-360)
-- | ```
computeTwoFingerData :: Point -> Point -> TwoFingerData
computeTwoFingerData p1 p2 =
  let
    dx = p2.x - p1.x
    dy = p2.y - p1.y
    centerX = (p1.x + p2.x) / 2.0
    centerY = (p1.y + p2.y) / 2.0
    distance = Num.sqrt (dx * dx + dy * dy)
    -- atan2 returns radians, convert to degrees
    angleRad = Num.atan2 dy dx
    angleDeg = angleRad * 180.0 / 3.14159265358979
  in
    { center: { x: centerX, y: centerY }
    , distance: distance
    , angle: angleDeg
    }
