-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // render // element // manipulation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Manipulation Functions
-- |
-- | Utility functions for transforming and querying elements. These functions
-- | work on the pure Element data structure without side effects.
-- |
-- | ## Categories
-- |
-- | - **Message mapping**: Transform the message type of elements
-- | - **Child manipulation**: Add, remove, or filter children
-- | - **Attribute manipulation**: Add attributes to elements
-- | - **Lazy evaluation**: Force lazy elements to evaluate
-- | - **Queries**: Check element properties
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element.Manipulation (mapMsg, appendChild, isEmpty)
-- |
-- | -- Transform messages from a child component
-- | childElement :: Element ChildMsg
-- | parentElement :: Element ParentMsg
-- | parentElement = mapMsg ChildAction childElement
-- | ```
module Hydrogen.Render.Element.Manipulation
  ( -- * Message Mapping
    mapMsg
  
  -- * Child Manipulation
  , filterChildren
  , prependChild
  , appendChild
  
  -- * Attribute Manipulation
  , withAttribute
  , withAttributes
  
  -- * Lazy Evaluation
  , forceLazy
  , forceAllLazy
  
  -- * Queries
  , childCount
  , firstChild
  , lastChild
  , isEmpty
  ) where

import Prelude
  ( map
  , unit
  , (==)
  , (<>)
  )

import Data.Array (cons, filter, snoc)
import Data.Array as Array
import Data.Maybe (Maybe(Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element.Types
  ( Attribute
  , Element(Element, Empty, Keyed, Lazy, Text)
  , mapAttrMsg
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // message // mapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over the message type of an element
-- |
-- | This is useful when composing components with different message types.
-- | The provided function transforms messages from the child type to the
-- | parent type.
-- |
-- | ```purescript
-- | childView :: Element ChildMsg
-- | parentView :: Element ParentMsg
-- | parentView = mapMsg ChildAction childView
-- | ```
mapMsg :: forall a b. (a -> b) -> Element a -> Element b
mapMsg = map

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // child // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter children of an element
-- |
-- | Returns a new element with only the children that satisfy the predicate.
-- | For non-container elements (Text, Empty, Lazy), returns the element unchanged.
filterChildren :: forall msg. (Element msg -> Boolean) -> Element msg -> Element msg
filterChildren pred = case _ of
  Element r -> Element r { children = filter pred r.children }
  Keyed r -> Keyed r { children = filter (\(Tuple _ e) -> pred e) r.children }
  other -> other

-- | Prepend a child to an element
-- |
-- | Adds the child to the beginning of the children array.
-- | For non-container elements, returns the element unchanged.
prependChild :: forall msg. Element msg -> Element msg -> Element msg
prependChild child = case _ of
  Element r -> Element r { children = cons child r.children }
  other -> other

-- | Append a child to an element
-- |
-- | Adds the child to the end of the children array.
-- | For non-container elements, returns the element unchanged.
appendChild :: forall msg. Element msg -> Element msg -> Element msg
appendChild child = case _ of
  Element r -> Element r { children = snoc r.children child }
  other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // attribute // manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add an attribute to an element
-- |
-- | Appends the attribute to the existing attributes array.
-- | For Text, Empty, and Lazy elements, returns the element unchanged.
withAttribute :: forall msg. Attribute msg -> Element msg -> Element msg
withAttribute newAttr = case _ of
  Element r -> Element r { attributes = snoc r.attributes newAttr }
  Keyed r -> Keyed r { attributes = snoc r.attributes newAttr }
  other -> other

-- | Add multiple attributes to an element
-- |
-- | Appends all attributes to the existing attributes array.
-- | For Text, Empty, and Lazy elements, returns the element unchanged.
withAttributes :: forall msg. Array (Attribute msg) -> Element msg -> Element msg
withAttributes newAttrs = case _ of
  Element r -> Element r { attributes = r.attributes <> newAttrs }
  Keyed r -> Keyed r { attributes = r.attributes <> newAttrs }
  other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // lazy // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Force evaluation of a lazy element
-- |
-- | If the element is Lazy, evaluates the thunk and returns the result.
-- | Otherwise returns the element unchanged.
-- |
-- | Note: This only forces one level of laziness. Nested lazy elements
-- | are not forced. Use `forceAllLazy` for recursive forcing.
forceLazy :: forall msg. Element msg -> Element msg
forceLazy = case _ of
  Lazy r -> r.thunk unit
  other -> other

-- | Recursively force all lazy elements in a tree
-- |
-- | Traverses the entire element tree and evaluates all Lazy elements.
-- | This is useful for serialization or testing where you need the
-- | complete evaluated tree.
forceAllLazy :: forall msg. Element msg -> Element msg
forceAllLazy = case _ of
  Lazy r -> forceAllLazy (r.thunk unit)
  Element r -> Element r { children = map forceAllLazy r.children }
  Keyed r -> Keyed r { children = map (\(Tuple k e) -> Tuple k (forceAllLazy e)) r.children }
  other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the number of direct children of an element
-- |
-- | For Text, Empty, and Lazy elements, returns 0.
childCount :: forall msg. Element msg -> Int
childCount = case _ of
  Element r -> Array.length r.children
  Keyed r -> Array.length r.children
  _ -> 0

-- | Get the first child of an element if it exists
-- |
-- | Returns Nothing for elements without children or with an empty children array.
firstChild :: forall msg. Element msg -> Maybe (Element msg)
firstChild = case _ of
  Element r -> Array.head r.children
  Keyed r -> map (\(Tuple _ e) -> e) (Array.head r.children)
  _ -> Nothing

-- | Get the last child of an element if it exists
-- |
-- | Returns Nothing for elements without children or with an empty children array.
lastChild :: forall msg. Element msg -> Maybe (Element msg)
lastChild = case _ of
  Element r -> Array.last r.children
  Keyed r -> map (\(Tuple _ e) -> e) (Array.last r.children)
  _ -> Nothing

-- | Check if an element has no children or is empty
-- |
-- | - For Element/Keyed: true if children array is empty
-- | - For Text: true if string is empty
-- | - For Empty: always true
-- | - For Lazy: always false (cannot know without forcing)
isEmpty :: forall msg. Element msg -> Boolean
isEmpty = case _ of
  Element r -> Array.null r.children
  Keyed r -> Array.null r.children
  Text s -> s == ""
  Empty -> true
  Lazy _ -> false
