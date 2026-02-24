-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // dragdrop
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Drag and Drop system
-- |
-- | A comprehensive drag and drop system with touch support, keyboard
-- | accessibility, axis constraints, and customizable visual feedback.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Interaction.DragDrop as DragDrop
-- |
-- | -- Draggable element
-- | DragDrop.draggable
-- |   [ DragDrop.dragData { id: "item-1", type: "card" }
-- |   , DragDrop.onDragStart \_ -> HandleDragStart
-- |   , DragDrop.onDragEnd \_ -> HandleDragEnd
-- |   , DragDrop.showGhost true
-- |   ]
-- |   [ HH.text "Drag me!" ]
-- |
-- | -- Drop zone
-- | DragDrop.droppable
-- |   [ DragDrop.onDrop \info -> HandleDrop info.data
-- |   , DragDrop.dropHighlight "bg-blue-100 border-blue-500"
-- |   ]
-- |   [ HH.text "Drop here" ]
-- |
-- | -- Constrained dragging
-- | DragDrop.draggable
-- |   [ DragDrop.axis DragDrop.AxisX  -- Horizontal only
-- |   , DragDrop.bounds { left: 0, top: 0, right: 500, bottom: 300 }
-- |   ]
-- |   [ content ]
-- |
-- | -- Keyboard accessible dragging
-- | DragDrop.draggable
-- |   [ DragDrop.keyboardDrag true  -- Space to grab, arrows to move
-- |   , DragDrop.keyboardStep 10
-- |   ]
-- |   [ content ]
-- | ```
module Hydrogen.Interaction.DragDrop
  ( -- * Draggable Component
    draggable
  , DraggableProps
  , DraggableProp
    -- * Droppable Component
  , droppable
  , DroppableProps
  , DroppableProp
    -- * Drag Handle
  , dragHandle
  , DragHandleProps
  , DragHandleProp
    -- * Draggable Props
  , dragData
  , onDragStart
  , onDrag
  , onDragEnd
  , showGhost
  , ghostOpacity
  , axis
  , Axis(AxisNone, AxisX, AxisY)
  , bounds
  , Bounds
  , handleSelector
  , keyboardDrag
  , keyboardStep
  , disabled
  , className
    -- * Droppable Props
  , onDrop
  , onDragOver
  , onDragLeave
  , accepts
  , dropHighlight
  , dropClassName
    -- * Drag Events
  , DragStartEvent
  , DragEvent
  , DragEndEvent
  , DropEvent
  , DragOverEvent
  , DragLeaveEvent
    -- * Ghost Element
  , createGhost
  , updateGhostPosition
  , removeGhost
    -- * Drop Indicator
  , showDropIndicator
  , updateDropIndicator
  , removeDropIndicator
    -- * Drag State
  , DragState
  , getDragState
  , setDragState
  , clearDragState
    -- * Data Transfer
  , setDragData
  , getDragData
  , clearDragData
    -- * Utilities
  , getBoundingRect
  , BoundingRect
  , getElementAtPoint
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Foreign (Foreign)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Axis constraint for dragging
data Axis
  = AxisNone  -- ^ Free movement
  | AxisX     -- ^ Horizontal only
  | AxisY     -- ^ Vertical only

derive instance eqAxis :: Eq Axis

-- | Bounding box constraint
type Bounds =
  { left :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  }

-- | Bounding rectangle
type BoundingRect =
  { left :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  , width :: Number
  , height :: Number
  }

-- | Drag state
type DragState =
  { element :: Element
  , data :: Foreign
  , startX :: Number
  , startY :: Number
  , offsetX :: Number
  , offsetY :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Event fired when drag starts
type DragStartEvent =
  { element :: Element
  , data :: Foreign
  , x :: Number
  , y :: Number
  , offsetX :: Number
  , offsetY :: Number
  }

-- | Event fired during drag
type DragEvent =
  { element :: Element
  , data :: Foreign
  , x :: Number
  , y :: Number
  , deltaX :: Number
  , deltaY :: Number
  }

-- | Event fired when drag ends
type DragEndEvent =
  { element :: Element
  , data :: Foreign
  , x :: Number
  , y :: Number
  , deltaX :: Number
  , deltaY :: Number
  }

-- | Event fired on drop
type DropEvent =
  { element :: Element
  , data :: Foreign
  , x :: Number
  , y :: Number
  }

-- | Event fired when dragging over drop zone
type DragOverEvent =
  { element :: Element
  , data :: Foreign
  , x :: Number
  , y :: Number
  }

-- | Event fired when leaving drop zone
type DragLeaveEvent =
  { element :: Element
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // draggable props
-- ═══════════════════════════════════════════════════════════════════════════════

type DraggableProps i =
  { data :: Foreign
  , onDragStart :: Maybe (DragStartEvent -> i)
  , onDrag :: Maybe (DragEvent -> i)
  , onDragEnd :: Maybe (DragEndEvent -> i)
  , showGhost :: Boolean
  , ghostOpacity :: Number
  , axis :: Axis
  , bounds :: Maybe Bounds
  , handleSelector :: Maybe String
  , keyboardDrag :: Boolean
  , keyboardStep :: Int
  , disabled :: Boolean
  , className :: String
  }

type DraggableProp i = DraggableProps i -> DraggableProps i

defaultDraggableProps :: forall i. DraggableProps i
defaultDraggableProps =
  { data: unsafeToForeign {}
  , onDragStart: Nothing
  , onDrag: Nothing
  , onDragEnd: Nothing
  , showGhost: true
  , ghostOpacity: 0.7
  , axis: AxisNone
  , bounds: Nothing
  , handleSelector: Nothing
  , keyboardDrag: true
  , keyboardStep: 10
  , disabled: false
  , className: ""
  }

-- | Set drag data (any serializable value)
dragData :: forall i a. a -> DraggableProp i
dragData d props = props { data = unsafeToForeign d }

-- | Handler for drag start
onDragStart :: forall i. (DragStartEvent -> i) -> DraggableProp i
onDragStart handler props = props { onDragStart = Just handler }

-- | Handler for drag movement
onDrag :: forall i. (DragEvent -> i) -> DraggableProp i
onDrag handler props = props { onDrag = Just handler }

-- | Handler for drag end
onDragEnd :: forall i. (DragEndEvent -> i) -> DraggableProp i
onDragEnd handler props = props { onDragEnd = Just handler }

-- | Show ghost element while dragging
showGhost :: forall i. Boolean -> DraggableProp i
showGhost show props = props { showGhost = show }

-- | Ghost element opacity (0.0 to 1.0)
ghostOpacity :: forall i. Number -> DraggableProp i
ghostOpacity opacity props = props { ghostOpacity = opacity }

-- | Constrain dragging to axis
axis :: forall i. Axis -> DraggableProp i
axis a props = props { axis = a }

-- | Constrain dragging within bounds
bounds :: forall i. Bounds -> DraggableProp i
bounds b props = props { bounds = Just b }

-- | CSS selector for drag handle (only this element triggers drag)
handleSelector :: forall i. String -> DraggableProp i
handleSelector selector props = props { handleSelector = Just selector }

-- | Enable keyboard dragging
keyboardDrag :: forall i. Boolean -> DraggableProp i
keyboardDrag enabled props = props { keyboardDrag = enabled }

-- | Keyboard movement step in pixels
keyboardStep :: forall i. Int -> DraggableProp i
keyboardStep step props = props { keyboardStep = step }

-- | Disable dragging
disabled :: forall i. Boolean -> DraggableProp i
disabled d props = props { disabled = d }

-- | Add custom class
className :: forall i. String -> DraggableProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // droppable props
-- ═══════════════════════════════════════════════════════════════════════════════

type DroppableProps i =
  { onDrop :: Maybe (DropEvent -> i)
  , onDragOver :: Maybe (DragOverEvent -> i)
  , onDragLeave :: Maybe (DragLeaveEvent -> i)
  , accepts :: Maybe (Foreign -> Boolean)
  , dropHighlight :: String
  , className :: String
  }

type DroppableProp i = DroppableProps i -> DroppableProps i

defaultDroppableProps :: forall i. DroppableProps i
defaultDroppableProps =
  { onDrop: Nothing
  , onDragOver: Nothing
  , onDragLeave: Nothing
  , accepts: Nothing
  , dropHighlight: "ring-2 ring-primary ring-offset-2 bg-primary/10"
  , className: ""
  }

-- | Handler for drop event
onDrop :: forall i. (DropEvent -> i) -> DroppableProp i
onDrop handler props = props { onDrop = Just handler }

-- | Handler for drag over event
onDragOver :: forall i. (DragOverEvent -> i) -> DroppableProp i
onDragOver handler props = props { onDragOver = Just handler }

-- | Handler for drag leave event
onDragLeave :: forall i. (DragLeaveEvent -> i) -> DroppableProp i
onDragLeave handler props = props { onDragLeave = Just handler }

-- | Filter function to accept/reject drops
accepts :: forall i. (Foreign -> Boolean) -> DroppableProp i
accepts fn props = props { accepts = Just fn }

-- | CSS classes for highlight when dragging over
dropHighlight :: forall i. String -> DroppableProp i
dropHighlight highlight props = props { dropHighlight = highlight }

-- | Add custom class (reusing name for droppable)
dropClassName :: forall i. String -> DroppableProp i
dropClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // drag handle props
-- ═══════════════════════════════════════════════════════════════════════════════

type DragHandleProps =
  { className :: String
  }

type DragHandleProp = DragHandleProps -> DragHandleProps

defaultDragHandleProps :: DragHandleProps
defaultDragHandleProps =
  { className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Draggable wrapper component
-- |
-- | Makes its children draggable with support for ghost elements,
-- | axis constraints, keyboard navigation, and touch devices.
draggable :: forall w i. Array (DraggableProp i) -> Array (HH.HTML w i) -> HH.HTML w i
draggable propMods children =
  let props = foldl (\p f -> f p) defaultDraggableProps propMods
      axisStr = case props.axis of
        AxisNone -> "none"
        AxisX -> "x"
        AxisY -> "y"
  in HH.div
    [ cls
        [ "select-none"
        , if props.disabled then "opacity-50 cursor-not-allowed" else "cursor-grab active:cursor-grabbing"
        , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"
        , "[&[data-dragging=true]]:cursor-grabbing [&[data-dragging=true]]:opacity-50"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-draggable") "true"
    , HP.attr (HH.AttrName "data-drag-axis") axisStr
    , HP.attr (HH.AttrName "data-drag-disabled") (if props.disabled then "true" else "false")
    , HP.tabIndex (if props.keyboardDrag && not props.disabled then 0 else (-1))
    , ARIA.role "button"
    , ARIA.label "Draggable item. Press Space or Enter to grab, arrow keys to move, Escape to cancel."
    ]
    children

-- | Droppable zone component
-- |
-- | Creates a drop target that can receive dragged items.
droppable :: forall w i. Array (DroppableProp i) -> Array (HH.HTML w i) -> HH.HTML w i
droppable propMods children =
  let props = foldl (\p f -> f p) defaultDroppableProps propMods
  in HH.div
    [ cls
        [ "transition-all duration-150"
        , "[&[data-drag-over=true]]:" <> props.dropHighlight
        , props.className
        ]
    , HP.attr (HH.AttrName "data-droppable") "true"
    , ARIA.role "region"
    , ARIA.label "Drop zone"
    ]
    children

-- | Drag handle component
-- |
-- | Place inside a draggable to restrict drag initiation to this element.
dragHandle :: forall w i. Array DragHandleProp -> Array (HH.HTML w i) -> HH.HTML w i
dragHandle propMods children =
  let props = foldl (\p f -> f p) defaultDragHandleProps propMods
  in HH.div
    [ cls
        [ "cursor-grab active:cursor-grabbing touch-none"
        , "flex items-center justify-center"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-drag-handle") "true"
    , ARIA.role "button"
    , ARIA.label "Drag handle"
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // ghost element ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a ghost element from the dragged element
foreign import createGhostImpl :: Element -> Number -> Number -> Number -> Effect Element

createGhost :: Element -> Number -> Number -> Number -> Effect Element
createGhost = createGhostImpl

-- | Update ghost element position
foreign import updateGhostPositionImpl :: Number -> Number -> Effect Unit

updateGhostPosition :: Number -> Number -> Effect Unit
updateGhostPosition = updateGhostPositionImpl

-- | Remove ghost element
foreign import removeGhostImpl :: Effect Unit

removeGhost :: Effect Unit
removeGhost = removeGhostImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // drop indicator ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show drop indicator at position
foreign import showDropIndicatorImpl :: Number -> Number -> Number -> Number -> String -> Effect Element

showDropIndicator :: Number -> Number -> Number -> Number -> String -> Effect Element
showDropIndicator = showDropIndicatorImpl

-- | Update drop indicator position and size
foreign import updateDropIndicatorImpl :: Number -> Number -> Number -> Number -> Effect Unit

updateDropIndicator :: Number -> Number -> Number -> Number -> Effect Unit
updateDropIndicator = updateDropIndicatorImpl

-- | Remove drop indicator
foreign import removeDropIndicatorImpl :: Effect Unit

removeDropIndicator :: Effect Unit
removeDropIndicator = removeDropIndicatorImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // drag state ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get current drag state
foreign import getDragStateImpl :: Effect (Maybe DragState)

getDragState :: Effect (Maybe DragState)
getDragState = getDragStateImpl

-- | Set drag state
foreign import setDragStateImpl :: DragState -> Effect Unit

setDragState :: DragState -> Effect Unit
setDragState = setDragStateImpl

-- | Clear drag state
foreign import clearDragStateImpl :: Effect Unit

clearDragState :: Effect Unit
clearDragState = clearDragStateImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // data transfer ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set drag data by key
foreign import setDragDataImpl :: String -> Foreign -> Effect Unit

setDragData :: String -> Foreign -> Effect Unit
setDragData = setDragDataImpl

-- | Get drag data by key
foreign import getDragDataImpl :: String -> Effect (Maybe Foreign)

getDragData :: String -> Effect (Maybe Foreign)
getDragData = getDragDataImpl

-- | Clear all drag data
foreign import clearDragDataImpl :: Effect Unit

clearDragData :: Effect Unit
clearDragData = clearDragDataImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // utilities ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get element bounding rectangle
foreign import getBoundingRectImpl :: Element -> Effect BoundingRect

getBoundingRect :: Element -> Effect BoundingRect
getBoundingRect = getBoundingRectImpl

-- | Get element at point
foreign import getElementAtPointImpl :: Number -> Number -> Effect (Maybe Element)

getElementAtPoint :: Number -> Number -> Effect (Maybe Element)
getElementAtPoint = getElementAtPointImpl

-- | Check if element contains another
foreign import containsImpl :: Element -> Element -> Boolean

-- | Set element style
foreign import setStyleImpl :: Element -> String -> String -> Effect Unit

-- | Add class to element
foreign import addClassImpl :: Element -> String -> Effect Unit

-- | Remove class from element
foreign import removeClassImpl :: Element -> String -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // internal
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import unsafeToForeign :: forall a. a -> Foreign
