-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // render // element // events
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Event Handler Constructors
-- |
-- | Functions for attaching event handlers to elements. Event handlers produce
-- | messages of type `msg` which are dispatched to the update function.
-- |
-- | ## Event Categories
-- |
-- | - **Mouse events**: click, double-click, mouse movement
-- | - **Focus events**: focus, blur
-- | - **Input events**: input, change, submit
-- | - **Keyboard events**: key down, key up, key press
-- | - **Scroll events**: scroll, wheel
-- | - **Drag events**: drag start, drag, drop
-- | - **Touch events**: touch start, touch move, touch end
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element.Events (onClick, onInput)
-- |
-- | myButton :: Msg -> Element Msg
-- | myButton msg = button_ [ onClick msg ] [ text "Click me" ]
-- |
-- | myInput :: Element Msg
-- | myInput = input_ [ onInput UpdateText ]
-- | ```
module Hydrogen.Render.Element.Events
  ( -- * Mouse Events
    onClick
  , onDoubleClick
  , onMouseDown
  , onMouseUp
  , onMouseMove
  , onMouseEnter
  , onMouseLeave
  
  -- * Focus Events
  , onFocus
  , onBlur
  
  -- * Input Events
  , onInput
  , onChange
  , onSubmit
  
  -- * Keyboard Events
  , onKeyDown
  , onKeyUp
  , onKeyPress
  
  -- * Scroll Events
  , onScroll
  , onWheel
  
  -- * Drag Events
  , onDragStart
  , onDrag
  , onDragEnd
  , onDragEnter
  , onDragLeave
  , onDragOver
  , onDrop
  
  -- * Touch Events
  , onTouchStart
  , onTouchMove
  , onTouchEnd
  , onTouchCancel
  ) where

import Prelude ((<<<))

import Hydrogen.Render.Element.Types
  ( Attribute(Handler)
  , EventHandler
      ( OnBlur
      , OnChange
      , OnClick
      , OnDoubleClick
      , OnDrag
      , OnDragEnd
      , OnDragEnter
      , OnDragLeave
      , OnDragOver
      , OnDragStart
      , OnDrop
      , OnFocus
      , OnInput
      , OnKeyDown
      , OnKeyPress
      , OnKeyUp
      , OnMouseDown
      , OnMouseEnter
      , OnMouseLeave
      , OnMouseMove
      , OnMouseUp
      , OnScroll
      , OnSubmit
      , OnTouchCancel
      , OnTouchEnd
      , OnTouchMove
      , OnTouchStart
      , OnWheel
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // mouse // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle click events
onClick :: forall msg. msg -> Attribute msg
onClick = Handler <<< OnClick

-- | Handle double-click events
onDoubleClick :: forall msg. msg -> Attribute msg
onDoubleClick = Handler <<< OnDoubleClick

-- | Handle mouse down events
onMouseDown :: forall msg. msg -> Attribute msg
onMouseDown = Handler <<< OnMouseDown

-- | Handle mouse up events
onMouseUp :: forall msg. msg -> Attribute msg
onMouseUp = Handler <<< OnMouseUp

-- | Handle mouse move events
onMouseMove :: forall msg. msg -> Attribute msg
onMouseMove = Handler <<< OnMouseMove

-- | Handle mouse enter events (does not bubble)
onMouseEnter :: forall msg. msg -> Attribute msg
onMouseEnter = Handler <<< OnMouseEnter

-- | Handle mouse leave events (does not bubble)
onMouseLeave :: forall msg. msg -> Attribute msg
onMouseLeave = Handler <<< OnMouseLeave

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // focus // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle focus events
onFocus :: forall msg. msg -> Attribute msg
onFocus = Handler <<< OnFocus

-- | Handle blur events (loss of focus)
onBlur :: forall msg. msg -> Attribute msg
onBlur = Handler <<< OnBlur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // input // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle input events
-- |
-- | Fires on every keystroke. The callback receives the current input value.
onInput :: forall msg. (String -> msg) -> Attribute msg
onInput = Handler <<< OnInput

-- | Handle change events
-- |
-- | Fires when the input loses focus after being changed, or for select/checkbox
-- | when the selection changes.
onChange :: forall msg. (String -> msg) -> Attribute msg
onChange = Handler <<< OnChange

-- | Handle form submit events
-- |
-- | The default form submission is typically prevented by the runtime.
onSubmit :: forall msg. msg -> Attribute msg
onSubmit = Handler <<< OnSubmit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // keyboard // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle key down events
-- |
-- | The callback receives the key code/identifier.
onKeyDown :: forall msg. (String -> msg) -> Attribute msg
onKeyDown = Handler <<< OnKeyDown

-- | Handle key up events
-- |
-- | The callback receives the key code/identifier.
onKeyUp :: forall msg. (String -> msg) -> Attribute msg
onKeyUp = Handler <<< OnKeyUp

-- | Handle key press events
-- |
-- | The callback receives the key code/identifier.
-- | Note: keypress is deprecated in favor of keydown for most uses.
onKeyPress :: forall msg. (String -> msg) -> Attribute msg
onKeyPress = Handler <<< OnKeyPress

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // scroll // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle scroll events
onScroll :: forall msg. msg -> Attribute msg
onScroll = Handler <<< OnScroll

-- | Handle wheel events
onWheel :: forall msg. msg -> Attribute msg
onWheel = Handler <<< OnWheel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drag // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle drag start events
onDragStart :: forall msg. msg -> Attribute msg
onDragStart = Handler <<< OnDragStart

-- | Handle drag events (fires continuously during drag)
onDrag :: forall msg. msg -> Attribute msg
onDrag = Handler <<< OnDrag

-- | Handle drag end events
onDragEnd :: forall msg. msg -> Attribute msg
onDragEnd = Handler <<< OnDragEnd

-- | Handle drag enter events (element enters drop zone)
onDragEnter :: forall msg. msg -> Attribute msg
onDragEnter = Handler <<< OnDragEnter

-- | Handle drag leave events (element leaves drop zone)
onDragLeave :: forall msg. msg -> Attribute msg
onDragLeave = Handler <<< OnDragLeave

-- | Handle drag over events (element is over drop zone)
onDragOver :: forall msg. msg -> Attribute msg
onDragOver = Handler <<< OnDragOver

-- | Handle drop events
onDrop :: forall msg. msg -> Attribute msg
onDrop = Handler <<< OnDrop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // touch // events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle touch start events
onTouchStart :: forall msg. msg -> Attribute msg
onTouchStart = Handler <<< OnTouchStart

-- | Handle touch move events
onTouchMove :: forall msg. msg -> Attribute msg
onTouchMove = Handler <<< OnTouchMove

-- | Handle touch end events
onTouchEnd :: forall msg. msg -> Attribute msg
onTouchEnd = Handler <<< OnTouchEnd

-- | Handle touch cancel events
onTouchCancel :: forall msg. msg -> Attribute msg
onTouchCancel = Handler <<< OnTouchCancel
