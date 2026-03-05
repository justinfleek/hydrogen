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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Gestural.Gesture
  ( -- * Gesture Phase
    GesturePhase(Possible, Began, Changed, Ended, Cancelled, Failed)
  , isPossible
  , isBegan
  , isChanged
  , isEnded
  , isCancelled
  , isFailed
  , isActive
  , isTerminal
    -- * Tap
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
    -- * Long Press
  , LongPressState
  , longPressState
  , noLongPress
  , longPressPosition
  , longPressDuration
  , isLongPressRecognized
    -- * Swipe (from Schema.Gestural.Gesture.Swipe)
  , SwipeDirection(SwipeLeft, SwipeRight, SwipeUp, SwipeDown)
  , SwipeState
  , swipeState
  , noSwipe
  , swipeVelocity
  , isSwipeRecognized
  , swipeDirectionFromDelta
    -- * Pan (from Schema.Gestural.Gesture.Pan)
  , PanState
  , panState
  , noPan
  , panTranslation
  , panVelocity
  , panDistance
  , isPanning
  , updatePanPosition
    -- * Pinch (from Schema.Gestural.Gesture.Pinch)
  , PinchConfig
  , pinchConfig
  , defaultPinchConfig
  , PinchGesture
  , pinchGesture
  , noPinchGesture
  , beginPinch
  , updatePinch
  , endPinch
  , cancelPinch
  , pinchGestureScale
  , pinchGestureCenter
  , pinchGestureVelocity
  , isPinchActive
  , isPinchEnded
    -- * Rotate (from Schema.Gestural.Gesture.Rotate)
  , RotateConfig
  , rotateConfig
  , defaultRotateConfig
  , RotateGesture
  , rotateGesture
  , noRotateGesture
  , beginRotate
  , updateRotate
  , endRotate
  , cancelRotate
  , rotateGestureAngle
  , rotateGestureAngleDegrees
  , rotateGestureDelta
  , rotateGestureCenter
  , rotateGestureVelocity
  , isRotateActive
  , isRotateEnded
    -- * Combined Gesture State
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
