-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // element // accordion // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AccordionState — Pure state atoms for accordion controls.
-- |
-- | ## Design Philosophy
-- |
-- | An Accordion is a disclosure widget with collapsible sections.
-- | State tracks which items are expanded and interaction states.
-- |
-- | ## State Model
-- |
-- | - **ExpansionMode**: Single (only one open) or Multiple (any number open)
-- | - **ItemState**: Per-item state (expanded, disabled, focused)
-- | - **ReducedMotion**: Global preference for motion
-- |
-- | ## Verified Atoms
-- |
-- | - DisabledFlag, FocusedFlag (Reactive.Flags)
-- | - Boolean for expanded state (binary, not partial)

module Hydrogen.Schema.Element.Accordion.State
  ( -- * Expansion Mode
    ExpansionMode
      ( SingleExpansion
      , MultipleExpansion
      )
  
  -- * Item State
  , AccordionItemState
  , defaultItemState
  , expandedItemState
  
  -- * Item State Accessors
  , isExpanded
  , isItemDisabled
  , isItemFocused
  , getItemValue
  
  -- * Item State Modifiers
  , setExpanded
  , setItemDisabled
  , setItemFocused
  , toggleExpanded
  
  -- * Accordion State (collection)
  , AccordionState
  , defaultAccordionState
  , singleAccordionState
  , multipleAccordionState
  
  -- * Accordion State Accessors
  , getExpansionMode
  , getReducedMotion
  , getItems
  , getExpandedValues
  , isAnyExpanded
  
  -- * Accordion State Modifiers
  , setExpansionMode
  , setReducedMotion
  , addItem
  , removeItem
  , expandItem
  , collapseItem
  , toggleItem
  , collapseAll
  , expandAll
  
  -- * Re-exports
  , module Hydrogen.Schema.Reactive.Flags
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , (==)
  , (&&)
  , (<>)
  )

import Prim (Array, Boolean, String)

import Data.Array (filter, any, snoc) as Array
import Data.Functor (map) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Reactive.Flags
  ( DisabledFlag(DisabledFlag)
  , FocusedFlag(FocusedFlag)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // expansion mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How many items can be expanded simultaneously.
-- |
-- | - SingleExpansion: Only one item open at a time (like tabs)
-- | - MultipleExpansion: Any number of items can be open
data ExpansionMode
  = SingleExpansion      -- ^ At most one item expanded
  | MultipleExpansion    -- ^ Any number of items can be expanded

derive instance eqExpansionMode :: Eq ExpansionMode

instance showExpansionMode :: Show ExpansionMode where
  show SingleExpansion = "single"
  show MultipleExpansion = "multiple"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // item state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for a single accordion item.
-- |
-- | Each item has:
-- | - value: Unique identifier (used for UUID5 generation)
-- | - expanded: Whether content is visible
-- | - disabled: Cannot be toggled
-- | - focused: Has keyboard focus
type AccordionItemState =
  { value :: String
  , expanded :: Boolean
  , disabled :: DisabledFlag
  , focused :: FocusedFlag
  }

-- | Default item state — collapsed, enabled, unfocused.
defaultItemState :: String -> AccordionItemState
defaultItemState val =
  { value: val
  , expanded: false
  , disabled: DisabledFlag false
  , focused: FocusedFlag false
  }

-- | Item state starting expanded.
expandedItemState :: String -> AccordionItemState
expandedItemState val =
  { value: val
  , expanded: true
  , disabled: DisabledFlag false
  , focused: FocusedFlag false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // item state accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the item expanded?
isExpanded :: AccordionItemState -> Boolean
isExpanded item = item.expanded

-- | Is the item disabled?
isItemDisabled :: AccordionItemState -> Boolean
isItemDisabled item = case item.disabled of
  DisabledFlag d -> d

-- | Is the item focused?
isItemFocused :: AccordionItemState -> Boolean
isItemFocused item = case item.focused of
  FocusedFlag f -> f

-- | Get item value.
getItemValue :: AccordionItemState -> String
getItemValue item = item.value

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // item state modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set expanded state.
setExpanded :: Boolean -> AccordionItemState -> AccordionItemState
setExpanded e item = item { expanded = e }

-- | Set disabled state.
setItemDisabled :: Boolean -> AccordionItemState -> AccordionItemState
setItemDisabled d item = item { disabled = DisabledFlag d }

-- | Set focused state.
setItemFocused :: Boolean -> AccordionItemState -> AccordionItemState
setItemFocused f item = item { focused = FocusedFlag f }

-- | Toggle expanded state.
toggleExpanded :: AccordionItemState -> AccordionItemState
toggleExpanded item = item { expanded = not item.expanded }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // accordion state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete accordion state — collection of items with expansion behavior.
-- |
-- | ## Invariants
-- |
-- | - In SingleExpansion mode, at most one item.expanded = true
-- | - Item values are unique within the accordion
type AccordionState =
  { expansionMode :: ExpansionMode
  , reducedMotion :: Boolean
  , items :: Array AccordionItemState
  }

-- | Default accordion state — multiple expansion, no items.
defaultAccordionState :: AccordionState
defaultAccordionState =
  { expansionMode: MultipleExpansion
  , reducedMotion: false
  , items: []
  }

-- | Single-expansion accordion state.
singleAccordionState :: AccordionState
singleAccordionState =
  { expansionMode: SingleExpansion
  , reducedMotion: false
  , items: []
  }

-- | Multiple-expansion accordion state.
multipleAccordionState :: AccordionState
multipleAccordionState =
  { expansionMode: MultipleExpansion
  , reducedMotion: false
  , items: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // accordion state accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get expansion mode.
getExpansionMode :: AccordionState -> ExpansionMode
getExpansionMode acc = acc.expansionMode

-- | Get reduced motion preference.
getReducedMotion :: AccordionState -> Boolean
getReducedMotion acc = acc.reducedMotion

-- | Get all items.
getItems :: AccordionState -> Array AccordionItemState
getItems acc = acc.items

-- | Get values of all expanded items.
getExpandedValues :: AccordionState -> Array String
getExpandedValues acc =
  Array.map getItemValue (Array.filter isExpanded acc.items)

-- | Is any item expanded?
isAnyExpanded :: AccordionState -> Boolean
isAnyExpanded acc = Array.any isExpanded acc.items

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // accordion state modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set expansion mode.
setExpansionMode :: ExpansionMode -> AccordionState -> AccordionState
setExpansionMode mode acc = acc { expansionMode = mode }

-- | Set reduced motion preference.
setReducedMotion :: Boolean -> AccordionState -> AccordionState
setReducedMotion r acc = acc { reducedMotion = r }

-- | Add an item to the accordion.
addItem :: AccordionItemState -> AccordionState -> AccordionState
addItem item acc = acc { items = Array.snoc acc.items item }

-- | Remove an item by value.
removeItem :: String -> AccordionState -> AccordionState
removeItem val acc =
  acc { items = Array.filter (\i -> i.value == val) acc.items }

-- | Expand an item by value.
-- |
-- | In SingleExpansion mode, collapses all other items first.
expandItem :: String -> AccordionState -> AccordionState
expandItem val acc =
  let
    -- In single mode, collapse others first
    baseItems = case acc.expansionMode of
      SingleExpansion -> Array.map (setExpanded false) acc.items
      MultipleExpansion -> acc.items
    
    -- Expand the target item
    updatedItems = Array.map
      (\i -> if i.value == val then setExpanded true i else i)
      baseItems
  in
    acc { items = updatedItems }

-- | Collapse an item by value.
collapseItem :: String -> AccordionState -> AccordionState
collapseItem val acc =
  let
    updatedItems = Array.map
      (\i -> if i.value == val then setExpanded false i else i)
      acc.items
  in
    acc { items = updatedItems }

-- | Toggle an item by value.
-- |
-- | In SingleExpansion mode, if expanding, collapses all others first.
toggleItem :: String -> AccordionState -> AccordionState
toggleItem val acc =
  let
    -- Find if target is currently expanded
    isTargetExpanded = Array.any (\i -> i.value == val && isExpanded i) acc.items
  in
    if isTargetExpanded
      then collapseItem val acc
      else expandItem val acc

-- | Collapse all items.
collapseAll :: AccordionState -> AccordionState
collapseAll acc =
  acc { items = Array.map (setExpanded false) acc.items }

-- | Expand all items (only in MultipleExpansion mode).
-- |
-- | In SingleExpansion mode, this is a no-op to preserve invariant.
expandAll :: AccordionState -> AccordionState
expandAll acc = case acc.expansionMode of
  SingleExpansion -> acc  -- Cannot expand all in single mode
  MultipleExpansion -> acc { items = Array.map (setExpanded true) acc.items }
