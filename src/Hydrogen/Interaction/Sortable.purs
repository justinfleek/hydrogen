-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // sortable
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sortable lists
-- |
-- | Sortable list components with drag-and-drop reordering, keyboard
-- | accessibility, and smooth animations. Supports both vertical and
-- | horizontal layouts, and dragging between multiple lists.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Interaction.Sortable as Sortable
-- |
-- | -- Basic sortable list
-- | Sortable.sortableList
-- |   [ Sortable.onReorder \e -> HandleReorder e.oldIndex e.newIndex
-- |   , Sortable.animate true
-- |   ]
-- |   [ Sortable.sortableItem [ Sortable.itemId "1" ] [ HH.text "Item 1" ]
-- |   , Sortable.sortableItem [ Sortable.itemId "2" ] [ HH.text "Item 2" ]
-- |   , Sortable.sortableItem [ Sortable.itemId "3" ] [ HH.text "Item 3" ]
-- |   ]
-- |
-- | -- Horizontal sortable
-- | Sortable.sortableList
-- |   [ Sortable.direction Sortable.Horizontal
-- |   , Sortable.onReorder handleReorder
-- |   ]
-- |   items
-- |
-- | -- With drag handles
-- | Sortable.sortableItem [ Sortable.itemId "1" ]
-- |   [ Sortable.sortableHandle [] [ Icon.gripVertical ]
-- |   , HH.span_ [ HH.text "Item 1" ]
-- |   ]
-- |
-- | -- Disabled items
-- | Sortable.sortableItem 
-- |   [ Sortable.itemId "locked"
-- |   , Sortable.itemDisabled true
-- |   ]
-- |   [ HH.text "Cannot be moved" ]
-- |
-- | -- Keyboard reordering
-- | -- Press Space/Enter to grab, arrow keys to move, Space/Enter to drop
-- | ```
module Hydrogen.Interaction.Sortable
  ( -- * Sortable List
    sortableList
  , SortableListProps
  , SortableListProp
    -- * Sortable Item
  , sortableItem
  , SortableItemProps
  , SortableItemProp
    -- * Sortable Handle
  , sortableHandle
  , SortableHandleProps
  , SortableHandleProp
    -- * List Props
  , listId
  , direction
  , Direction(Vertical, Horizontal)
  , onReorder
  , onSortStart
  , onSortMove
  , onSortEnd
  , animate
  , showGhost
  , showPlaceholder
  , placeholderClass
  , handleSelector
  , listClassName
    -- * Item Props
  , itemId
  , itemDisabled
  , itemClassName
    -- * Events
  , ReorderEvent
  , SortStartEvent
  , SortMoveEvent
  , SortEndEvent
  , CrossListMoveEvent
    -- * Utilities
  , reorderArray
  , getItems
  , getItemIndex
  , setItemDisabled
    -- * Sort State
  , SortState
  , getSortState
  , clearSortState
    -- * Placeholder
  , createPlaceholder
  , insertPlaceholder
  , removePlaceholder
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Effect (Effect)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sort direction
data Direction
  = Vertical    -- ^ Vertical list (default)
  | Horizontal  -- ^ Horizontal list

derive instance eqDirection :: Eq Direction

-- | Sort state
type SortState =
  { container :: Element
  , item :: Element
  , fromIndex :: Int
  , toIndex :: Int
  , listId :: String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // events
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Event fired when items are reordered
type ReorderEvent =
  { item :: Element
  , oldIndex :: Int
  , newIndex :: Int
  , listId :: String
  }

-- | Event fired when sorting starts
type SortStartEvent =
  { item :: Element
  , index :: Int
  , listId :: String
  }

-- | Event fired during sort movement
type SortMoveEvent =
  { item :: Element
  , fromIndex :: Int
  , toIndex :: Int
  , listId :: String
  }

-- | Event fired when sorting ends
type SortEndEvent =
  { item :: Element
  , fromIndex :: Int
  , toIndex :: Int
  , listId :: String
  }

-- | Event fired when moving between lists
type CrossListMoveEvent =
  { item :: Element
  , fromListId :: String
  , toListId :: String
  , fromIndex :: Int
  , toIndex :: Int
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // sortable list props
-- ═══════════════════════════════════════════════════════════════════════════════

type SortableListProps i =
  { listId :: String
  , direction :: Direction
  , onReorder :: Maybe (ReorderEvent -> i)
  , onSortStart :: Maybe (SortStartEvent -> i)
  , onSortMove :: Maybe (SortMoveEvent -> i)
  , onSortEnd :: Maybe (SortEndEvent -> i)
  , animate :: Boolean
  , showGhost :: Boolean
  , showPlaceholder :: Boolean
  , placeholderClass :: String
  , handleSelector :: Maybe String
  , className :: String
  }

type SortableListProp i = SortableListProps i -> SortableListProps i

defaultSortableListProps :: forall i. SortableListProps i
defaultSortableListProps =
  { listId: "sortable-list"
  , direction: Vertical
  , onReorder: Nothing
  , onSortStart: Nothing
  , onSortMove: Nothing
  , onSortEnd: Nothing
  , animate: true
  , showGhost: true
  , showPlaceholder: true
  , placeholderClass: "bg-muted/50 border-2 border-dashed border-muted-foreground/30 rounded-md"
  , handleSelector: Nothing
  , className: ""
  }

-- | Set list identifier (for multi-list support)
listId :: forall i. String -> SortableListProp i
listId id props = props { listId = id }

-- | Set sort direction
direction :: forall i. Direction -> SortableListProp i
direction dir props = props { direction = dir }

-- | Handler for reorder event
onReorder :: forall i. (ReorderEvent -> i) -> SortableListProp i
onReorder handler props = props { onReorder = Just handler }

-- | Handler for sort start event
onSortStart :: forall i. (SortStartEvent -> i) -> SortableListProp i
onSortStart handler props = props { onSortStart = Just handler }

-- | Handler for sort move event
onSortMove :: forall i. (SortMoveEvent -> i) -> SortableListProp i
onSortMove handler props = props { onSortMove = Just handler }

-- | Handler for sort end event
onSortEnd :: forall i. (SortEndEvent -> i) -> SortableListProp i
onSortEnd handler props = props { onSortEnd = Just handler }

-- | Enable/disable animations
animate :: forall i. Boolean -> SortableListProp i
animate enabled props = props { animate = enabled }

-- | Show ghost element while dragging
showGhost :: forall i. Boolean -> SortableListProp i
showGhost show props = props { showGhost = show }

-- | Show placeholder in list while dragging
showPlaceholder :: forall i. Boolean -> SortableListProp i
showPlaceholder show props = props { showPlaceholder = show }

-- | CSS classes for placeholder element
placeholderClass :: forall i. String -> SortableListProp i
placeholderClass c props = props { placeholderClass = c }

-- | CSS selector for drag handles
handleSelector :: forall i. String -> SortableListProp i
handleSelector selector props = props { handleSelector = Just selector }

-- | Add custom class to list
listClassName :: forall i. String -> SortableListProp i
listClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // sortable item props
-- ═══════════════════════════════════════════════════════════════════════════════

type SortableItemProps =
  { id :: String
  , disabled :: Boolean
  , className :: String
  }

type SortableItemProp = SortableItemProps -> SortableItemProps

defaultSortableItemProps :: SortableItemProps
defaultSortableItemProps =
  { id: ""
  , disabled: false
  , className: ""
  }

-- | Set item identifier
itemId :: String -> SortableItemProp
itemId id props = props { id = id }

-- | Disable item (cannot be dragged)
itemDisabled :: Boolean -> SortableItemProp
itemDisabled disabled props = props { disabled = disabled }

-- | Add custom class to item
itemClassName :: String -> SortableItemProp
itemClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // sortable handle props
-- ═══════════════════════════════════════════════════════════════════════════════

type SortableHandleProps =
  { className :: String
  }

type SortableHandleProp = SortableHandleProps -> SortableHandleProps

defaultSortableHandleProps :: SortableHandleProps
defaultSortableHandleProps =
  { className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sortable list container
-- |
-- | Contains sortable items that can be reordered via drag and drop
-- | or keyboard navigation.
sortableList :: forall w i. Array (SortableListProp i) -> Array (HH.HTML w i) -> HH.HTML w i
sortableList propMods children =
  let props = foldl (\p f -> f p) defaultSortableListProps propMods
      dirClass = case props.direction of
        Vertical -> "flex flex-col"
        Horizontal -> "flex flex-row"
  in HH.div
    [ cls
        [ dirClass
        , "gap-2"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-sortable-list") props.listId
    , HP.attr (HH.AttrName "data-direction") (if props.direction == Horizontal then "horizontal" else "vertical")
    , ARIA.role "listbox"
    , ARIA.label "Sortable list. Use arrow keys to reorder items."
    ]
    children

-- | Sortable item wrapper
-- |
-- | Wrap content in this component to make it sortable within a sortableList.
sortableItem :: forall w i. Array SortableItemProp -> Array (HH.HTML w i) -> HH.HTML w i
sortableItem propMods children =
  let props = foldl (\p f -> f p) defaultSortableItemProps propMods
  in HH.div
    [ cls
        [ "relative select-none"
        , if props.disabled
            then "opacity-50 cursor-not-allowed"
            else "cursor-grab active:cursor-grabbing"
        , "focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2"
        , "[&[data-sorting=true]]:opacity-50"
        , "[&[data-keyboard-sorting=true]]:ring-2 [&[data-keyboard-sorting=true]]:ring-primary"
        , "transition-transform duration-200"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-sortable-item") props.id
    , if props.disabled
        then HP.attr (HH.AttrName "data-sortable-disabled") "true"
        else HP.attr (HH.AttrName "data-sortable-disabled") "false"
    , HP.tabIndex (if props.disabled then (-1) else 0)
    , ARIA.role "option"
    , ARIA.label "Sortable item. Press Space or Enter to grab, arrow keys to reorder, Space or Enter to drop, Escape to cancel."
    ]
    children

-- | Sortable handle component
-- |
-- | When placed inside a sortable item, only this element will initiate dragging.
sortableHandle :: forall w i. Array SortableHandleProp -> Array (HH.HTML w i) -> HH.HTML w i
sortableHandle propMods children =
  let props = foldl (\p f -> f p) defaultSortableHandleProps propMods
  in HH.div
    [ cls
        [ "cursor-grab active:cursor-grabbing touch-none"
        , "flex items-center justify-center"
        , "text-muted-foreground hover:text-foreground"
        , "transition-colors"
        , props.className
        ]
    , HP.attr (HH.AttrName "data-sortable-handle") "true"
    , ARIA.role "button"
    , ARIA.label "Drag handle"
    ]
    children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // sort state ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get current sort state
foreign import getSortStateImpl :: Effect (Maybe SortState)

getSortState :: Effect (Maybe SortState)
getSortState = getSortStateImpl

-- | Clear sort state
foreign import clearSortStateImpl :: Effect Unit

clearSortState :: Effect Unit
clearSortState = clearSortStateImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // placeholder ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create placeholder element
foreign import createPlaceholderImpl :: Number -> Number -> String -> Effect Element

createPlaceholder :: Number -> Number -> String -> Effect Element
createPlaceholder = createPlaceholderImpl

-- | Insert placeholder at index
foreign import insertPlaceholderImpl :: Element -> Int -> Effect Unit

insertPlaceholder :: Element -> Int -> Effect Unit
insertPlaceholder = insertPlaceholderImpl

-- | Remove placeholder
foreign import removePlaceholderImpl :: Effect Unit

removePlaceholder :: Effect Unit
removePlaceholder = removePlaceholderImpl

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // utilities ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Reorder array from one index to another
foreign import reorderArrayImpl :: forall a. Array a -> Int -> Int -> Array a

reorderArray :: forall a. Array a -> Int -> Int -> Array a
reorderArray = reorderArrayImpl

-- | Get all sortable items in container
foreign import getItemsImpl :: Element -> Effect (Array Element)

getItems :: Element -> Effect (Array Element)
getItems = getItemsImpl

-- | Get index of item in container
foreign import getItemIndexImpl :: Element -> Element -> Effect Int

getItemIndex :: Element -> Element -> Effect Int
getItemIndex = getItemIndexImpl

-- | Set item disabled state
foreign import setItemDisabledImpl :: Element -> Boolean -> Effect Unit

setItemDisabled :: Element -> Boolean -> Effect Unit
setItemDisabled = setItemDisabledImpl
