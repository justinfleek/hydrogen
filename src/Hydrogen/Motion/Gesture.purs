-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // motion // gesture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Touch and mouse gesture recognition
-- |
-- | Unified gesture system supporting touch, mouse, and pointer events
-- | with velocity tracking and gesture composition.
-- |
-- | ## Architecture Note
-- |
-- | This module exceeds the standard 500-line limit due to browser boundary
-- | coherence. All gesture recognizers (Pan, Pinch, Rotate, Swipe, LongPress,
-- | DoubleTap) share common types (Point, Velocity, GestureState) and must
-- | have their FFI declarations co-located with their PureScript wrappers.
-- | Splitting would fragment a cohesive browser integration API.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Gesture as G
-- |
-- | -- Create a pan gesture recognizer
-- | panGesture <- G.createPanGesture element
-- |   { onStart: \state -> Console.log "Pan started"
-- |   , onMove: \state -> Console.log $ "Moving: " <> show state.delta
-- |   , onEnd: \state -> Console.log "Pan ended"
-- |   , threshold: 10.0
-- |   }
-- |
-- | -- Create a pinch gesture for zooming
-- | pinchGesture <- G.createPinchGesture element
-- |   { onPinch: \state -> setScale state.scale
-- |   , onEnd: \state -> commitScale state.scale
-- |   }
-- |
-- | -- Swipe gesture with direction
-- | swipeGesture <- G.createSwipeGesture element
-- |   { onSwipe: \dir -> case dir of
-- |       G.SwipeLeft -> prevSlide
-- |       G.SwipeRight -> nextSlide
-- |       _ -> pure unit
-- |   , velocityThreshold: 0.5
-- |   }
-- |
-- | -- Compose gestures
-- | G.composeGestures [panGesture, pinchGesture]
-- |
-- | -- Clean up
-- | G.destroyGesture panGesture
-- | ```
module Hydrogen.Motion.Gesture
  ( -- * Gesture State
    GestureState(Idle, Active, Ended)
  , Point
  , Velocity
    -- * Pan Gesture (BROWSER BOUNDARY)
  , PanGesture
  , PanConfig
  , PanState
  , createPanGesture
  , defaultPanConfig
    -- * Pinch Gesture (BROWSER BOUNDARY)
  , PinchGesture
  , PinchConfig
  , PinchState
  , createPinchGesture
  , defaultPinchConfig
    -- * Rotate Gesture (BROWSER BOUNDARY)
  , RotateGesture
  , RotateConfig
  , RotateState
  , createRotateGesture
  , defaultRotateConfig
    -- * Swipe Gesture (BROWSER BOUNDARY)
  , SwipeGesture
  , SwipeConfig
  , SwipeDirection(SwipeLeft, SwipeRight, SwipeUp, SwipeDown)
  , createSwipeGesture
  , defaultSwipeConfig
    -- * Long Press (BROWSER BOUNDARY)
  , LongPressGesture
  , LongPressConfig
  , createLongPressGesture
  , defaultLongPressConfig
    -- * Double Tap (BROWSER BOUNDARY)
  , DoubleTapGesture
  , DoubleTapConfig
  , createDoubleTapGesture
  , defaultDoubleTapConfig
    -- * Gesture Composition (BROWSER BOUNDARY)
  , GestureRecognizer
  , composeGestures
  , enableGesture
  , disableGesture
  , destroyGesture
    -- * Velocity Tracking (BROWSER BOUNDARY for time)
  , VelocityTracker
  , TimestampedPoint
  , createVelocityTracker
  , trackPoint
  , getVelocity
  , resetTracker
    -- * Pure Velocity Computation
  , computeVelocityFromPoints
    -- * Pure Geometry Operations
  , TwoFingerData
  , pointDistance
  , pointCenter
  , pointAngle
  , computeTwoFingerData
  , normalizeAngle
    -- * Pure Swipe Computation
  , SwipeParams
  , detectSwipeDirection
    -- * Pure Scale Operations
  , clampScale
  , computePinchScale
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (abs, atan2, pi, sqrt)
import Data.Time.Duration (Milliseconds(Milliseconds))
import Effect (Effect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Web.DOM.Element (Element)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gesture lifecycle state
data GestureState
  = Idle       -- ^ No gesture in progress
  | Active     -- ^ Gesture is active
  | Ended      -- ^ Gesture has ended

derive instance eqGestureState :: Eq GestureState

instance showGestureState :: Show GestureState where
  show Idle = "Idle"
  show Active = "Active"
  show Ended = "Ended"

-- | 2D point
type Point =
  { x :: Number
  , y :: Number
  }

-- | 2D velocity (units per second)
type Velocity =
  { vx :: Number
  , vy :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // pan gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pan gesture recognizer
foreign import data PanGesture :: Type

-- | Pan gesture state
type PanState =
  { state :: GestureState
  , start :: Point
  , current :: Point
  , delta :: Point
  , offset :: Point
  , velocity :: Velocity
  }

-- | Pan gesture configuration
type PanConfig =
  { onStart :: PanState -> Effect Unit
  , onMove :: PanState -> Effect Unit
  , onEnd :: PanState -> Effect Unit
  , threshold :: Number           -- ^ Minimum distance before pan starts
  , lockAxis :: Boolean           -- ^ Lock to dominant axis
  , preventScroll :: Boolean      -- ^ Prevent page scrolling
  }

-- | Default pan configuration
defaultPanConfig :: PanConfig
defaultPanConfig =
  { onStart: \_ -> pure unit
  , onMove: \_ -> pure unit
  , onEnd: \_ -> pure unit
  , threshold: 0.0
  , lockAxis: false
  , preventScroll: true
  }

-- | Create a pan gesture recognizer on an element
-- | BROWSER BOUNDARY: Attaches pointer/touch/mouse event listeners
foreign import createPanGestureImpl
  :: Element
  -> { onStart :: PanStateJS -> Effect Unit
     , onMove :: PanStateJS -> Effect Unit
     , onEnd :: PanStateJS -> Effect Unit
     , threshold :: Number
     , lockAxis :: Boolean
     , preventScroll :: Boolean
     }
  -> Effect PanGesture

-- Internal JS state type
type PanStateJS =
  { state :: String
  , startX :: Number
  , startY :: Number
  , currentX :: Number
  , currentY :: Number
  , deltaX :: Number
  , deltaY :: Number
  , offsetX :: Number
  , offsetY :: Number
  , velocityX :: Number
  , velocityY :: Number
  }

panStateFromJS :: PanStateJS -> PanState
panStateFromJS js =
  { state: stateFromString js.state
  , start: { x: js.startX, y: js.startY }
  , current: { x: js.currentX, y: js.currentY }
  , delta: { x: js.deltaX, y: js.deltaY }
  , offset: { x: js.offsetX, y: js.offsetY }
  , velocity: { vx: js.velocityX, vy: js.velocityY }
  }
  where
  stateFromString "active" = Active
  stateFromString "ended" = Ended
  stateFromString _ = Idle

createPanGesture :: Element -> PanConfig -> Effect PanGesture
createPanGesture element config =
  createPanGestureImpl element
    { onStart: \js -> config.onStart (panStateFromJS js)
    , onMove: \js -> config.onMove (panStateFromJS js)
    , onEnd: \js -> config.onEnd (panStateFromJS js)
    , threshold: config.threshold
    , lockAxis: config.lockAxis
    , preventScroll: config.preventScroll
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pinch gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pinch gesture recognizer
foreign import data PinchGesture :: Type

-- | Pinch gesture state
type PinchState =
  { state :: GestureState
  , scale :: Number           -- ^ Current scale (1.0 = no scale)
  , initialScale :: Number    -- ^ Scale at gesture start
  , center :: Point           -- ^ Center point between fingers
  , distance :: Number        -- ^ Distance between fingers
  }

-- | Pinch gesture configuration
type PinchConfig =
  { onStart :: PinchState -> Effect Unit
  , onPinch :: PinchState -> Effect Unit
  , onEnd :: PinchState -> Effect Unit
  , minScale :: Number        -- ^ Minimum scale limit
  , maxScale :: Number        -- ^ Maximum scale limit
  }

-- | Default pinch configuration
defaultPinchConfig :: PinchConfig
defaultPinchConfig =
  { onStart: \_ -> pure unit
  , onPinch: \_ -> pure unit
  , onEnd: \_ -> pure unit
  , minScale: 0.1
  , maxScale: 10.0
  }

-- Internal JS state type
type PinchStateJS =
  { state :: String
  , scale :: Number
  , initialScale :: Number
  , centerX :: Number
  , centerY :: Number
  , distance :: Number
  }

pinchStateFromJS :: PinchStateJS -> PinchState
pinchStateFromJS js =
  { state: stateFromString js.state
  , scale: js.scale
  , initialScale: js.initialScale
  , center: { x: js.centerX, y: js.centerY }
  , distance: js.distance
  }
  where
  stateFromString "active" = Active
  stateFromString "ended" = Ended
  stateFromString _ = Idle

-- | BROWSER BOUNDARY: Attaches touch event listeners for pinch detection
foreign import createPinchGestureImpl
  :: Element
  -> { onStart :: PinchStateJS -> Effect Unit
     , onPinch :: PinchStateJS -> Effect Unit
     , onEnd :: PinchStateJS -> Effect Unit
     , minScale :: Number
     , maxScale :: Number
     }
  -> Effect PinchGesture

createPinchGesture :: Element -> PinchConfig -> Effect PinchGesture
createPinchGesture element config =
  createPinchGestureImpl element
    { onStart: \js -> config.onStart (pinchStateFromJS js)
    , onPinch: \js -> config.onPinch (pinchStateFromJS js)
    , onEnd: \js -> config.onEnd (pinchStateFromJS js)
    , minScale: config.minScale
    , maxScale: config.maxScale
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // rotate gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate gesture recognizer
foreign import data RotateGesture :: Type

-- | Rotate gesture state
type RotateState =
  { state :: GestureState
  , rotation :: Number        -- ^ Current rotation in degrees
  , initialRotation :: Number -- ^ Rotation at gesture start
  , center :: Point           -- ^ Center point of rotation
  , velocity :: Number        -- ^ Angular velocity (degrees/second)
  }

-- | Rotate gesture configuration
type RotateConfig =
  { onStart :: RotateState -> Effect Unit
  , onRotate :: RotateState -> Effect Unit
  , onEnd :: RotateState -> Effect Unit
  , threshold :: Number       -- ^ Minimum rotation before gesture activates
  }

-- | Default rotate configuration
defaultRotateConfig :: RotateConfig
defaultRotateConfig =
  { onStart: \_ -> pure unit
  , onRotate: \_ -> pure unit
  , onEnd: \_ -> pure unit
  , threshold: 0.0
  }

-- Internal JS state type
type RotateStateJS =
  { state :: String
  , rotation :: Number
  , initialRotation :: Number
  , centerX :: Number
  , centerY :: Number
  , velocity :: Number
  }

rotateStateFromJS :: RotateStateJS -> RotateState
rotateStateFromJS js =
  { state: stateFromString js.state
  , rotation: js.rotation
  , initialRotation: js.initialRotation
  , center: { x: js.centerX, y: js.centerY }
  , velocity: js.velocity
  }
  where
  stateFromString "active" = Active
  stateFromString "ended" = Ended
  stateFromString _ = Idle

-- | BROWSER BOUNDARY: Attaches touch event listeners for rotation detection
foreign import createRotateGestureImpl
  :: Element
  -> { onStart :: RotateStateJS -> Effect Unit
     , onRotate :: RotateStateJS -> Effect Unit
     , onEnd :: RotateStateJS -> Effect Unit
     , threshold :: Number
     }
  -> Effect RotateGesture

createRotateGesture :: Element -> RotateConfig -> Effect RotateGesture
createRotateGesture element config =
  createRotateGestureImpl element
    { onStart: \js -> config.onStart (rotateStateFromJS js)
    , onRotate: \js -> config.onRotate (rotateStateFromJS js)
    , onEnd: \js -> config.onEnd (rotateStateFromJS js)
    , threshold: config.threshold
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // swipe gesture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swipe gesture recognizer
foreign import data SwipeGesture :: Type

-- | Swipe direction
data SwipeDirection
  = SwipeLeft
  | SwipeRight
  | SwipeUp
  | SwipeDown

derive instance eqSwipeDirection :: Eq SwipeDirection

instance showSwipeDirection :: Show SwipeDirection where
  show SwipeLeft = "SwipeLeft"
  show SwipeRight = "SwipeRight"
  show SwipeUp = "SwipeUp"
  show SwipeDown = "SwipeDown"

swipeDirectionFromString :: String -> Maybe SwipeDirection
swipeDirectionFromString "left" = Just SwipeLeft
swipeDirectionFromString "right" = Just SwipeRight
swipeDirectionFromString "up" = Just SwipeUp
swipeDirectionFromString "down" = Just SwipeDown
swipeDirectionFromString _ = Nothing

-- | Swipe gesture configuration
type SwipeConfig =
  { onSwipe :: SwipeDirection -> Effect Unit
  , velocityThreshold :: Number   -- ^ Minimum velocity to trigger swipe
  , distanceThreshold :: Number   -- ^ Minimum distance for swipe
  , maxDuration :: Milliseconds   -- ^ Maximum swipe duration
  }

-- | Default swipe configuration
defaultSwipeConfig :: SwipeConfig
defaultSwipeConfig =
  { onSwipe: \_ -> pure unit
  , velocityThreshold: 0.5
  , distanceThreshold: 50.0
  , maxDuration: Milliseconds 300.0
  }

-- | BROWSER BOUNDARY: Attaches pointer/touch/mouse event listeners for swipe detection
foreign import createSwipeGestureImpl
  :: Element
  -> { onSwipe :: String -> Effect Unit
     , velocityThreshold :: Number
     , distanceThreshold :: Number
     , maxDuration :: Number
     }
  -> Effect SwipeGesture

createSwipeGesture :: Element -> SwipeConfig -> Effect SwipeGesture
createSwipeGesture element config =
  createSwipeGestureImpl element
    { onSwipe: \dir -> case swipeDirectionFromString dir of
        Just d -> config.onSwipe d
        Nothing -> pure unit
    , velocityThreshold: config.velocityThreshold
    , distanceThreshold: config.distanceThreshold
    , maxDuration: unwrapMs config.maxDuration
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // long press
-- ═════════════════════════════════════════════════════════════════════════════

-- | Long press gesture recognizer
foreign import data LongPressGesture :: Type

-- | Long press configuration
type LongPressConfig =
  { onLongPress :: Point -> Effect Unit
  , onStart :: Point -> Effect Unit    -- ^ Touch started (before threshold)
  , onCancel :: Effect Unit            -- ^ Touch moved too much or ended early
  , duration :: Milliseconds           -- ^ Hold duration to trigger
  , maxDistance :: Number              -- ^ Max movement allowed during press
  }

-- | Default long press configuration
defaultLongPressConfig :: LongPressConfig
defaultLongPressConfig =
  { onLongPress: \_ -> pure unit
  , onStart: \_ -> pure unit
  , onCancel: pure unit
  , duration: Milliseconds 500.0
  , maxDistance: 10.0
  }

-- | BROWSER BOUNDARY: Attaches pointer/touch/mouse events with setTimeout
foreign import createLongPressGestureImpl
  :: Element
  -> { onLongPress :: { x :: Number, y :: Number } -> Effect Unit
     , onStart :: { x :: Number, y :: Number } -> Effect Unit
     , onCancel :: Effect Unit
     , duration :: Number
     , maxDistance :: Number
     }
  -> Effect LongPressGesture

createLongPressGesture :: Element -> LongPressConfig -> Effect LongPressGesture
createLongPressGesture element config =
  createLongPressGestureImpl element
    { onLongPress: config.onLongPress
    , onStart: config.onStart
    , onCancel: config.onCancel
    , duration: unwrapMs config.duration
    , maxDistance: config.maxDistance
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // double tap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Double tap gesture recognizer
foreign import data DoubleTapGesture :: Type

-- | Double tap configuration
type DoubleTapConfig =
  { onDoubleTap :: Point -> Effect Unit
  , onSingleTap :: Point -> Effect Unit   -- ^ Called if no second tap
  , maxDelay :: Milliseconds              -- ^ Max time between taps
  , maxDistance :: Number                 -- ^ Max distance between taps
  }

-- | Default double tap configuration
defaultDoubleTapConfig :: DoubleTapConfig
defaultDoubleTapConfig =
  { onDoubleTap: \_ -> pure unit
  , onSingleTap: \_ -> pure unit
  , maxDelay: Milliseconds 300.0
  , maxDistance: 40.0
  }

-- | BROWSER BOUNDARY: Attaches pointer/touch/mouse events with setTimeout
foreign import createDoubleTapGestureImpl
  :: Element
  -> { onDoubleTap :: { x :: Number, y :: Number } -> Effect Unit
     , onSingleTap :: { x :: Number, y :: Number } -> Effect Unit
     , maxDelay :: Number
     , maxDistance :: Number
     }
  -> Effect DoubleTapGesture

createDoubleTapGesture :: Element -> DoubleTapConfig -> Effect DoubleTapGesture
createDoubleTapGesture element config =
  createDoubleTapGestureImpl element
    { onDoubleTap: config.onDoubleTap
    , onSingleTap: config.onSingleTap
    , maxDelay: unwrapMs config.maxDelay
    , maxDistance: config.maxDistance
    }
  where
  unwrapMs (Milliseconds ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gesture composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic gesture recognizer (for composition)
foreign import data GestureRecognizer :: Type

-- | Compose multiple gestures to work together
-- | Handles conflicts between gestures (e.g., pan vs swipe)
-- | BROWSER BOUNDARY: Manages gesture enable/disable state
foreign import composeGestures :: Array GestureRecognizer -> Effect Unit

-- | Enable a gesture recognizer
-- | BROWSER BOUNDARY: Enables event listener processing
foreign import enableGesture :: GestureRecognizer -> Effect Unit

-- | Disable a gesture recognizer
-- | BROWSER BOUNDARY: Disables event listener processing
foreign import disableGesture :: GestureRecognizer -> Effect Unit

-- | Destroy a gesture recognizer and clean up event listeners
-- | BROWSER BOUNDARY: Removes all event listeners from DOM
foreign import destroyGesture :: GestureRecognizer -> Effect Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // velocity tracking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Velocity tracker for smooth gesture animations
type VelocityTracker =
  { points :: Ref (Array { point :: Point, time :: Number })
  , maxSamples :: Int
  }

-- | Create a velocity tracker
createVelocityTracker :: Int -> Effect VelocityTracker
createVelocityTracker maxSamples = do
  points <- Ref.new []
  pure { points, maxSamples }

-- | Track a point with timestamp
-- | BROWSER BOUNDARY: Requires `performance.now()` from runtime
foreign import trackPointImpl
  :: Ref (Array { point :: Point, time :: Number })
  -> Int
  -> Point
  -> Effect Unit

trackPoint :: VelocityTracker -> Point -> Effect Unit
trackPoint tracker point =
  trackPointImpl tracker.points tracker.maxSamples point

-- | Get current velocity from tracker
-- | BROWSER BOUNDARY: Reads mutable state populated by browser events
foreign import getVelocityImpl
  :: Ref (Array { point :: Point, time :: Number })
  -> Effect Velocity

getVelocity :: VelocityTracker -> Effect Velocity
getVelocity tracker = getVelocityImpl tracker.points

-- | Reset the velocity tracker
resetTracker :: VelocityTracker -> Effect Unit
resetTracker tracker = Ref.write [] tracker.points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // pure velocity computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timestamped point for velocity tracking
type TimestampedPoint =
  { point :: Point
  , time :: Number  -- milliseconds
  }

-- | Compute velocity from an array of timestamped points — PURE FUNCTION
-- |
-- | Uses the first and last points to compute average velocity.
-- | Returns zero velocity if fewer than 2 points or zero time delta.
computeVelocityFromPoints :: Array TimestampedPoint -> Velocity
computeVelocityFromPoints points = case Array.length points of
  n | n < 2 -> { vx: 0.0, vy: 0.0 }
  _ ->
    let
      first = Array.index points 0
      last = Array.index points (Array.length points - 1)
    in case first, last of
      Just f, Just l ->
        let
          dt = (l.time - f.time) / 1000.0  -- Convert ms to seconds
        in
          if dt <= 0.0
            then { vx: 0.0, vy: 0.0 }
            else
              { vx: (l.point.x - f.point.x) / dt
              , vy: (l.point.y - f.point.y) / dt
              }
      _, _ -> { vx: 0.0, vy: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // pure geometry operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Two-finger gesture data — PURE DATA
type TwoFingerData =
  { center :: Point       -- ^ Center point between fingers
  , distance :: Number    -- ^ Distance between fingers (pixels)
  , angle :: Number       -- ^ Angle between fingers (degrees)
  }

-- | Compute distance between two points — PURE FUNCTION
pointDistance :: Point -> Point -> Number
pointDistance p1 p2 =
  let
    dx = p2.x - p1.x
    dy = p2.y - p1.y
  in
    sqrt (dx * dx + dy * dy)

-- | Compute center point between two points — PURE FUNCTION
pointCenter :: Point -> Point -> Point
pointCenter p1 p2 =
  { x: (p1.x + p2.x) / 2.0
  , y: (p1.y + p2.y) / 2.0
  }

-- | Compute angle between two points in degrees — PURE FUNCTION
pointAngle :: Point -> Point -> Number
pointAngle p1 p2 =
  let
    dx = p2.x - p1.x
    dy = p2.y - p1.y
  in
    atan2 dy dx * (180.0 / pi)

-- | Compute two-finger data from two touch points — PURE FUNCTION
computeTwoFingerData :: Point -> Point -> TwoFingerData
computeTwoFingerData p1 p2 =
  { center: pointCenter p1 p2
  , distance: pointDistance p1 p2
  , angle: pointAngle p1 p2
  }

-- | Normalize angle to -180..180 range — PURE FUNCTION
normalizeAngle :: Number -> Number
normalizeAngle angle
  | angle > 180.0 = angle - 360.0
  | angle < (-180.0) = angle + 360.0
  | otherwise = angle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // pure swipe computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swipe parameters for detection — PURE DATA
type SwipeParams =
  { startPoint :: Point
  , endPoint :: Point
  , duration :: Number     -- milliseconds
  , maxDuration :: Number  -- milliseconds
  , distanceThreshold :: Number
  , velocityThreshold :: Number
  }

-- | Detect swipe direction from parameters — PURE FUNCTION
-- |
-- | Returns Nothing if swipe constraints not met (too slow, too short, too long)
detectSwipeDirection :: SwipeParams -> Maybe SwipeDirection
detectSwipeDirection params =
  let
    dx = params.endPoint.x - params.startPoint.x
    dy = params.endPoint.y - params.startPoint.y
    distance = sqrt (dx * dx + dy * dy)
    velocity = if params.duration > 0.0
               then distance / (params.duration / 1000.0)
               else 0.0
  in
    if params.duration > params.maxDuration then Nothing
    else if distance < params.distanceThreshold then Nothing
    else if velocity < params.velocityThreshold * 1000.0 then Nothing
    else
      let
        absDx = abs dx
        absDy = abs dy
      in
        if absDx > absDy
          then if dx > 0.0 then Just SwipeRight else Just SwipeLeft
          else if dy > 0.0 then Just SwipeDown else Just SwipeUp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // pure scale clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp scale to min/max bounds — PURE FUNCTION
clampScale :: Number -> Number -> Number -> Number
clampScale minScale maxScale rawScale
  | rawScale < minScale = minScale
  | rawScale > maxScale = maxScale
  | otherwise = rawScale

-- | Compute new scale from pinch gesture — PURE FUNCTION
computePinchScale 
  :: { initialScale :: Number, initialDistance :: Number, currentDistance :: Number }
  -> { minScale :: Number, maxScale :: Number }
  -> Number
computePinchScale gesture bounds =
  let
    rawScale = gesture.initialScale * (gesture.currentDistance / gesture.initialDistance)
  in
    clampScale bounds.minScale bounds.maxScale rawScale
