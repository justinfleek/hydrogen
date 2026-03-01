-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gestural // event
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Event - unified gestural event types for input handling.
-- |
-- | Provides a comprehensive event taxonomy for mouse, pointer, touch, keyboard,
-- | wheel, and gesture events. This module unifies the W3C event specifications
-- | into a coherent type system for deterministic input handling at billion-agent
-- | scale.
-- |
-- | ## Event Philosophy
-- |
-- | At billion-agent scale, events must be:
-- | - **Deterministic**: Same event data → same handling behavior
-- | - **Bounded**: All values within defined ranges
-- | - **Complete**: No undefined states or missing variants
-- |
-- | ## W3C Specifications Implemented
-- |
-- | - UIEvents (MouseEvent, KeyboardEvent, WheelEvent)
-- | - Pointer Events Level 2 (PointerEvent)
-- | - Touch Events (TouchEvent)
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Generic.Rep (Generic)
-- | - Data.Show.Generic (genericShow)
-- | - Gestural.Pointer (PointerState, PointerPosition, MouseButton)
-- | - Gestural.Touch (TouchPoint)
-- | - Gestural.Keyboard (KeyEventType, KeyCode, ModifierState)
-- | - Gestural.Gesture.Phase (GesturePhase)
-- | - Gestural.Scroll (ScrollDelta)
-- |
-- | ## Dependents
-- | - Runtime.EventDispatcher (dispatches GesturalEvent to handlers)
-- | - Component.* (event handlers receive GesturalEvent)
-- | - Interaction.* (gesture recognizers consume GesturalEvent)

module Hydrogen.Schema.Gestural.Event
  ( -- * Mouse Event Types
    MouseEventType
      ( MouseDown
      , MouseUp
      , MouseMove
      , MouseEnter
      , MouseLeave
      , MouseOver
      , MouseOut
      , MouseClick
      , MouseDblClick
      , MouseContextMenu
      )
  , allMouseEventTypes
  , isMouseButtonEvent
  , isMouseMoveEvent
  , isMouseBoundaryEvent
  , isMouseClickEvent
  
    -- * Pointer Event Types (W3C Pointer Events)
  , PointerEventType
      ( PointerDown
      , PointerUp
      , PointerMove
      , PointerEnter
      , PointerLeave
      , PointerOver
      , PointerOut
      , PointerCancel
      , GotPointerCapture
      , LostPointerCapture
      )
  , allPointerEventTypes
  , isPointerButtonEvent
  , isPointerMoveEvent
  , isPointerBoundaryEvent
  , isPointerCaptureEvent
  , pointerEventToMouse
  
    -- * Touch Event Types
  , TouchEventType
      ( TouchStart
      , TouchMove
      , TouchEnd
      , TouchCancel
      )
  , allTouchEventTypes
  , isTouchStartOrEnd
  , isTouchActive
  
    -- * Wheel Delta
  , WheelDelta
  , wheelDelta
  , wheelDeltaX
  , wheelDeltaY
  , wheelDeltaZ
  , wheelDeltaMode
  , noWheelDelta
  , wheelDeltaPixels
  , wheelDeltaLines
  , wheelDeltaPages
  , normalizeWheelDelta
  
    -- * Gesture Data
  , GestureData
  , gestureData
  , noGestureData
  , gestureScale
  , gestureRotation
  , gestureTranslationX
  , gestureTranslationY
  , gestureVelocityX
  , gestureVelocityY
  
    -- * Unified Gestural Event
  , GesturalEvent
      ( PointerEvt
      , MouseEvt
      , TouchEvt
      , KeyboardEvt
      , WheelEvt
      , GestureEvt
      )
  , isPointerEvent
  , isMouseEvent
  , isTouchEvent
  , isKeyboardEvent
  , isWheelEvent
  , isGestureEvent
  , eventTimestamp
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude

import Data.Array (foldl)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)

import Hydrogen.Schema.Gestural.Gesture.Phase (GesturePhase)
import Hydrogen.Schema.Gestural.Keyboard.Event (KeyEventType)
import Hydrogen.Schema.Gestural.Keyboard.Keys (KeyCode)
import Hydrogen.Schema.Gestural.Keyboard.Modifiers (ModifierState)
import Hydrogen.Schema.Gestural.Pointer
  ( MouseButton
  , PointerPosition
  , PointerState
  )
import Hydrogen.Schema.Gestural.Touch (TouchPoint)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // mouse // event // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mouse event lifecycle types per W3C UIEvents specification
-- |
-- | ## Event Categories
-- |
-- | **Button Events**: MouseDown, MouseUp, MouseClick, MouseDblClick, MouseContextMenu
-- | - Fired when mouse buttons are pressed, released, or clicked
-- |
-- | **Movement Events**: MouseMove
-- | - Fired when the mouse cursor moves
-- |
-- | **Boundary Events**: MouseEnter, MouseLeave, MouseOver, MouseOut
-- | - Fired when the cursor enters or leaves an element
-- | - Enter/Leave don't bubble; Over/Out do bubble
-- |
-- | ## Event Ordering
-- |
-- | For a click: MouseDown → MouseUp → MouseClick
-- | For double-click: MouseDown → MouseUp → MouseClick → MouseDown → MouseUp → MouseClick → MouseDblClick
data MouseEventType
  = MouseDown        -- ^ Mouse button pressed
  | MouseUp          -- ^ Mouse button released
  | MouseMove        -- ^ Mouse cursor moved
  | MouseEnter       -- ^ Cursor entered element (no bubble)
  | MouseLeave       -- ^ Cursor left element (no bubble)
  | MouseOver        -- ^ Cursor over element (bubbles)
  | MouseOut         -- ^ Cursor left element (bubbles)
  | MouseClick       -- ^ Click completed (down + up on same element)
  | MouseDblClick    -- ^ Double-click (two clicks within threshold)
  | MouseContextMenu -- ^ Context menu requested (typically right-click)

derive instance eqMouseEventType :: Eq MouseEventType
derive instance ordMouseEventType :: Ord MouseEventType
derive instance genericMouseEventType :: Generic MouseEventType _

instance showMouseEventType :: Show MouseEventType where
  show = genericShow

-- | All mouse event types for enumeration
allMouseEventTypes :: Array MouseEventType
allMouseEventTypes = 
  [ MouseDown
  , MouseUp
  , MouseMove
  , MouseEnter
  , MouseLeave
  , MouseOver
  , MouseOut
  , MouseClick
  , MouseDblClick
  , MouseContextMenu
  ]

-- | Is this a button-related event (down, up, click, dblclick, contextmenu)?
isMouseButtonEvent :: MouseEventType -> Boolean
isMouseButtonEvent MouseDown = true
isMouseButtonEvent MouseUp = true
isMouseButtonEvent MouseClick = true
isMouseButtonEvent MouseDblClick = true
isMouseButtonEvent MouseContextMenu = true
isMouseButtonEvent _ = false

-- | Is this a movement event?
isMouseMoveEvent :: MouseEventType -> Boolean
isMouseMoveEvent MouseMove = true
isMouseMoveEvent _ = false

-- | Is this a boundary crossing event?
isMouseBoundaryEvent :: MouseEventType -> Boolean
isMouseBoundaryEvent MouseEnter = true
isMouseBoundaryEvent MouseLeave = true
isMouseBoundaryEvent MouseOver = true
isMouseBoundaryEvent MouseOut = true
isMouseBoundaryEvent _ = false

-- | Is this a click event (click or dblclick)?
isMouseClickEvent :: MouseEventType -> Boolean
isMouseClickEvent MouseClick = true
isMouseClickEvent MouseDblClick = true
isMouseClickEvent _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // pointer // event // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pointer event types per W3C Pointer Events Level 2
-- |
-- | Pointer Events unify mouse, touch, and pen input into a single event model.
-- | This provides consistent handling across input modalities while preserving
-- | device-specific properties (pressure, tilt, etc).
-- |
-- | ## Pointer vs Mouse Events
-- |
-- | Pointer events mirror mouse events but:
-- | - Include pointerId for multi-touch tracking
-- | - Include pointer-specific properties (pressure, tilt, etc)
-- | - Fire for all input types (mouse, touch, pen)
-- |
-- | ## Capture Events
-- |
-- | GotPointerCapture/LostPointerCapture fire when pointer capture is acquired
-- | or released via setPointerCapture/releasePointerCapture.
data PointerEventType
  = PointerDown         -- ^ Pointer activated (finger down, button pressed)
  | PointerUp           -- ^ Pointer deactivated (finger up, button released)
  | PointerMove         -- ^ Pointer moved
  | PointerEnter        -- ^ Pointer entered element (no bubble)
  | PointerLeave        -- ^ Pointer left element (no bubble)
  | PointerOver         -- ^ Pointer over element (bubbles)
  | PointerOut          -- ^ Pointer left element (bubbles)
  | PointerCancel       -- ^ Pointer cancelled (system gesture, interrupted)
  | GotPointerCapture   -- ^ Element received pointer capture
  | LostPointerCapture  -- ^ Element lost pointer capture

derive instance eqPointerEventType :: Eq PointerEventType
derive instance ordPointerEventType :: Ord PointerEventType
derive instance genericPointerEventType :: Generic PointerEventType _

instance showPointerEventType :: Show PointerEventType where
  show = genericShow

-- | All pointer event types for enumeration
allPointerEventTypes :: Array PointerEventType
allPointerEventTypes =
  [ PointerDown
  , PointerUp
  , PointerMove
  , PointerEnter
  , PointerLeave
  , PointerOver
  , PointerOut
  , PointerCancel
  , GotPointerCapture
  , LostPointerCapture
  ]

-- | Is this a button-related pointer event?
isPointerButtonEvent :: PointerEventType -> Boolean
isPointerButtonEvent PointerDown = true
isPointerButtonEvent PointerUp = true
isPointerButtonEvent PointerCancel = true
isPointerButtonEvent _ = false

-- | Is this a movement pointer event?
isPointerMoveEvent :: PointerEventType -> Boolean
isPointerMoveEvent PointerMove = true
isPointerMoveEvent _ = false

-- | Is this a boundary crossing pointer event?
isPointerBoundaryEvent :: PointerEventType -> Boolean
isPointerBoundaryEvent PointerEnter = true
isPointerBoundaryEvent PointerLeave = true
isPointerBoundaryEvent PointerOver = true
isPointerBoundaryEvent PointerOut = true
isPointerBoundaryEvent _ = false

-- | Is this a capture-related pointer event?
isPointerCaptureEvent :: PointerEventType -> Boolean
isPointerCaptureEvent GotPointerCapture = true
isPointerCaptureEvent LostPointerCapture = true
isPointerCaptureEvent _ = false

-- | Convert pointer event type to equivalent mouse event type
-- |
-- | Pointer events map 1:1 to mouse events except:
-- | - PointerCancel has no mouse equivalent (returns Nothing)
-- | - Capture events have no mouse equivalent (returns Nothing)
pointerEventToMouse :: PointerEventType -> Maybe MouseEventType
pointerEventToMouse PointerDown = Just MouseDown
pointerEventToMouse PointerUp = Just MouseUp
pointerEventToMouse PointerMove = Just MouseMove
pointerEventToMouse PointerEnter = Just MouseEnter
pointerEventToMouse PointerLeave = Just MouseLeave
pointerEventToMouse PointerOver = Just MouseOver
pointerEventToMouse PointerOut = Just MouseOut
pointerEventToMouse PointerCancel = Nothing
pointerEventToMouse GotPointerCapture = Nothing
pointerEventToMouse LostPointerCapture = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // touch // event // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Touch event types per W3C Touch Events specification
-- |
-- | Touch events are specifically for multi-touch surfaces. For unified handling
-- | across input types, prefer PointerEvents.
-- |
-- | ## Touch Event Lifecycle
-- |
-- | TouchStart → (TouchMove)* → TouchEnd | TouchCancel
-- |
-- | ## TouchCancel
-- |
-- | Fired when the touch is interrupted by the system (e.g., incoming call,
-- | system gesture, too many simultaneous touches).
data TouchEventType
  = TouchStart   -- ^ Finger touched screen
  | TouchMove    -- ^ Finger moved on screen
  | TouchEnd     -- ^ Finger lifted from screen
  | TouchCancel  -- ^ Touch interrupted by system

derive instance eqTouchEventType :: Eq TouchEventType
derive instance ordTouchEventType :: Ord TouchEventType
derive instance genericTouchEventType :: Generic TouchEventType _

instance showTouchEventType :: Show TouchEventType where
  show = genericShow

-- | All touch event types for enumeration
allTouchEventTypes :: Array TouchEventType
allTouchEventTypes = [ TouchStart, TouchMove, TouchEnd, TouchCancel ]

-- | Is this a touch start or end event?
isTouchStartOrEnd :: TouchEventType -> Boolean
isTouchStartOrEnd TouchStart = true
isTouchStartOrEnd TouchEnd = true
isTouchStartOrEnd TouchCancel = true
isTouchStartOrEnd _ = false

-- | Is touch currently active (start or move, not ended)?
isTouchActive :: TouchEventType -> Boolean
isTouchActive TouchStart = true
isTouchActive TouchMove = true
isTouchActive _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // wheel // delta
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wheel event delta values per W3C UIEvents WheelEvent
-- |
-- | ## Delta Modes
-- |
-- | - Pixel (0): Delta is in pixels
-- | - Line (1): Delta is in lines (typically 1 line = 16-20 pixels)
-- | - Page (2): Delta is in pages (typically 1 page = viewport height)
-- |
-- | ## Delta Axes
-- |
-- | - deltaX: Horizontal scroll (left = negative, right = positive)
-- | - deltaY: Vertical scroll (up = negative, down = positive)
-- | - deltaZ: Depth scroll (rarely used, for 3D input devices)
-- |
-- | ## Platform Variations
-- |
-- | - macOS trackpad: Pixel mode with inertia
-- | - Windows mouse wheel: Line mode, typically 3 lines per notch
-- | - Linux: Varies by driver
type WheelDelta =
  { deltaX :: Number     -- ^ Horizontal scroll amount
  , deltaY :: Number     -- ^ Vertical scroll amount
  , deltaZ :: Number     -- ^ Depth scroll amount (3D devices)
  , deltaMode :: Int     -- ^ 0=pixels, 1=lines, 2=pages
  }

-- | Create wheel delta with all values
wheelDelta :: Number -> Number -> Number -> Int -> WheelDelta
wheelDelta deltaX deltaY deltaZ deltaMode =
  { deltaX
  , deltaY
  , deltaZ
  , deltaMode: clampDeltaMode deltaMode
  }
  where
  clampDeltaMode :: Int -> Int
  clampDeltaMode m
    | m < 0 = 0
    | m > 2 = 2
    | otherwise = m

-- | Get horizontal delta
wheelDeltaX :: WheelDelta -> Number
wheelDeltaX wd = wd.deltaX

-- | Get vertical delta
wheelDeltaY :: WheelDelta -> Number
wheelDeltaY wd = wd.deltaY

-- | Get depth delta
wheelDeltaZ :: WheelDelta -> Number
wheelDeltaZ wd = wd.deltaZ

-- | Get delta mode (0=pixels, 1=lines, 2=pages)
wheelDeltaMode :: WheelDelta -> Int
wheelDeltaMode wd = wd.deltaMode

-- | No wheel delta (zero values, pixel mode)
noWheelDelta :: WheelDelta
noWheelDelta = wheelDelta 0.0 0.0 0.0 0

-- | Create pixel-mode wheel delta
wheelDeltaPixels :: Number -> Number -> WheelDelta
wheelDeltaPixels deltaX deltaY = wheelDelta deltaX deltaY 0.0 0

-- | Create line-mode wheel delta
wheelDeltaLines :: Number -> Number -> WheelDelta
wheelDeltaLines deltaX deltaY = wheelDelta deltaX deltaY 0.0 1

-- | Create page-mode wheel delta
wheelDeltaPages :: Number -> Number -> WheelDelta
wheelDeltaPages deltaX deltaY = wheelDelta deltaX deltaY 0.0 2

-- | Normalize wheel delta to pixels
-- |
-- | Uses standard conversions:
-- | - 1 line = 16 pixels (CSS line-height default)
-- | - 1 page = 800 pixels (approximate viewport)
-- |
-- | For more accurate page-mode conversion, pass actual viewport dimensions.
normalizeWheelDelta :: WheelDelta -> WheelDelta
normalizeWheelDelta wd = case wd.deltaMode of
  1 -> wd  -- Line mode: multiply by 16
    { deltaX = wd.deltaX * 16.0
    , deltaY = wd.deltaY * 16.0
    , deltaZ = wd.deltaZ * 16.0
    , deltaMode = 0
    }
  2 -> wd  -- Page mode: multiply by 800
    { deltaX = wd.deltaX * 800.0
    , deltaY = wd.deltaY * 800.0
    , deltaZ = wd.deltaZ * 800.0
    , deltaMode = 0
    }
  _ -> wd  -- Already pixels or unknown mode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // gesture // data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gesture recognition data
-- |
-- | Contains the computed parameters from a recognized gesture.
-- | This is the payload carried by GestureEvt.
-- |
-- | ## Scale
-- |
-- | Scale factor from pinch gesture. 1.0 = no scaling, <1.0 = pinch in, >1.0 = pinch out.
-- |
-- | ## Rotation
-- |
-- | Rotation angle in radians from rotate gesture. Positive = clockwise.
-- |
-- | ## Translation
-- |
-- | Pan translation in pixels from drag/pan gesture.
-- |
-- | ## Velocity
-- |
-- | Velocity in pixels per millisecond for momentum calculations.
type GestureData =
  { scale :: Number          -- ^ Pinch scale factor (1.0 = no change)
  , rotation :: Number       -- ^ Rotation in radians (positive = clockwise)
  , translationX :: Number   -- ^ Pan X translation (pixels)
  , translationY :: Number   -- ^ Pan Y translation (pixels)
  , velocityX :: Number      -- ^ X velocity (pixels/ms)
  , velocityY :: Number      -- ^ Y velocity (pixels/ms)
  , centerX :: Number        -- ^ Gesture center X (pixels)
  , centerY :: Number        -- ^ Gesture center Y (pixels)
  , timestamp :: Number      -- ^ Gesture timestamp (ms)
  }

-- | Create gesture data with all values
gestureData
  :: Number  -- ^ scale
  -> Number  -- ^ rotation
  -> Number  -- ^ translationX
  -> Number  -- ^ translationY
  -> Number  -- ^ velocityX
  -> Number  -- ^ velocityY
  -> Number  -- ^ centerX
  -> Number  -- ^ centerY
  -> Number  -- ^ timestamp
  -> GestureData
gestureData scale rotation translationX translationY velocityX velocityY centerX centerY timestamp =
  { scale
  , rotation
  , translationX
  , translationY
  , velocityX
  , velocityY
  , centerX
  , centerY
  , timestamp
  }

-- | No gesture data (identity values)
noGestureData :: GestureData
noGestureData = gestureData 1.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0 0.0

-- | Get gesture scale factor
gestureScale :: GestureData -> Number
gestureScale gd = gd.scale

-- | Get gesture rotation (radians)
gestureRotation :: GestureData -> Number
gestureRotation gd = gd.rotation

-- | Get gesture X translation
gestureTranslationX :: GestureData -> Number
gestureTranslationX gd = gd.translationX

-- | Get gesture Y translation
gestureTranslationY :: GestureData -> Number
gestureTranslationY gd = gd.translationY

-- | Get gesture X velocity
gestureVelocityX :: GestureData -> Number
gestureVelocityX gd = gd.velocityX

-- | Get gesture Y velocity
gestureVelocityY :: GestureData -> Number
gestureVelocityY gd = gd.velocityY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // unified // gestural event
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified gestural event type
-- |
-- | This is THE KEY TYPE for event handling in Hydrogen. All input events are
-- | normalized into this unified representation for consistent handling.
-- |
-- | ## Event Variants
-- |
-- | - **PointerEvt**: W3C Pointer Events (unified mouse/touch/pen)
-- | - **MouseEvt**: Legacy mouse events (for compatibility)
-- | - **TouchEvt**: Multi-touch events with touch point arrays
-- | - **KeyboardEvt**: Keyboard events with key codes and modifiers
-- | - **WheelEvt**: Scroll wheel events
-- | - **GestureEvt**: Recognized gesture events (pinch, rotate, pan)
-- |
-- | ## Determinism
-- |
-- | Same GesturalEvent value → same behavior. No hidden state, no race conditions.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | handleEvent :: GesturalEvent -> Msg
-- | handleEvent = case _ of
-- |   PointerEvt PointerDown state -> PointerPressed state.pointerId
-- |   MouseEvt MouseClick button pos mods -> Clicked button
-- |   KeyboardEvt KeyDown code mods -> KeyPressed code
-- |   WheelEvt delta -> Scrolled (wheelDeltaY delta)
-- |   GestureEvt Began data -> GestureStarted (gestureScale data)
-- |   _ -> NoOp
-- | ```
data GesturalEvent
  = PointerEvt PointerEventType PointerState
      -- ^ W3C Pointer Event with full pointer state
  | MouseEvt MouseEventType MouseButton PointerPosition ModifierState
      -- ^ Mouse event with button, position, and modifiers
  | TouchEvt TouchEventType (Array TouchPoint)
      -- ^ Touch event with array of active touch points
  | KeyboardEvt KeyEventType KeyCode ModifierState
      -- ^ Keyboard event with key code and modifiers
  | WheelEvt WheelDelta
      -- ^ Wheel/scroll event with delta values
  | GestureEvt GesturePhase GestureData
      -- ^ Recognized gesture with phase and computed data

derive instance eqGesturalEvent :: Eq GesturalEvent
derive instance genericGesturalEvent :: Generic GesturalEvent _

instance showGesturalEvent :: Show GesturalEvent where
  show = genericShow

-- | Is this a pointer event?
isPointerEvent :: GesturalEvent -> Boolean
isPointerEvent (PointerEvt _ _) = true
isPointerEvent _ = false

-- | Is this a mouse event?
isMouseEvent :: GesturalEvent -> Boolean
isMouseEvent (MouseEvt _ _ _ _) = true
isMouseEvent _ = false

-- | Is this a touch event?
isTouchEvent :: GesturalEvent -> Boolean
isTouchEvent (TouchEvt _ _) = true
isTouchEvent _ = false

-- | Is this a keyboard event?
isKeyboardEvent :: GesturalEvent -> Boolean
isKeyboardEvent (KeyboardEvt _ _ _) = true
isKeyboardEvent _ = false

-- | Is this a wheel event?
isWheelEvent :: GesturalEvent -> Boolean
isWheelEvent (WheelEvt _) = true
isWheelEvent _ = false

-- | Is this a gesture event?
isGestureEvent :: GesturalEvent -> Boolean
isGestureEvent (GestureEvt _ _) = true
isGestureEvent _ = false

-- | Extract timestamp from event (if available)
-- |
-- | Returns the timestamp embedded in the event data, or Nothing
-- | if the event type doesn't carry timestamp information.
eventTimestamp :: GesturalEvent -> Maybe Number
eventTimestamp (PointerEvt _ state) = state.timestamp
eventTimestamp (MouseEvt _ _ _ _) = Nothing  -- Mouse events don't carry timestamp in this model
eventTimestamp (TouchEvt _ touches) = case touches of
  [] -> Nothing
  _ -> Just (foldlTouchTimestamp touches)
eventTimestamp (KeyboardEvt _ _ _) = Nothing  -- Keyboard events don't carry timestamp in this model
eventTimestamp (WheelEvt _) = Nothing  -- Wheel events don't carry timestamp in this model
eventTimestamp (GestureEvt _ gd) = Just gd.timestamp

-- | Get the latest timestamp from touch points
foldlTouchTimestamp :: Array TouchPoint -> Number
foldlTouchTimestamp touches = foldl maxTimestamp 0.0 touches
  where
  maxTimestamp :: Number -> TouchPoint -> Number
  maxTimestamp acc tp = if tp.timestamp > acc then tp.timestamp else acc
