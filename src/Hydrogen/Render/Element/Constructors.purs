-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // render // element // constructors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Constructors
-- |
-- | Core constructors for creating Hydrogen elements. These are the primitive
-- | building blocks that all higher-level element helpers are built upon.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element.Constructors (element, text, empty)
-- |
-- | myDiv :: forall msg. Element msg
-- | myDiv = element "div" [] [ text "Hello" ]
-- | ```
module Hydrogen.Render.Element.Constructors
  ( -- * Core Constructors
    element
  , elementNS
  , text
  , empty
  , keyed
  , lazy
  ) where

import Prelude (Unit)

import Data.Maybe (Maybe(Nothing, Just))
import Data.Tuple (Tuple)

import Hydrogen.Render.Element.Types
  ( Attribute
  , Element(Element, Empty, Keyed, Lazy, Text)
  , Namespace
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // element // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an element with a tag name, attributes, and children
-- |
-- | This is the fundamental element constructor. All HTML element helpers
-- | (like `div_`, `span_`, etc.) are built on top of this.
-- |
-- | ```purescript
-- | element "div" [ class_ "container" ] [ text "Hello" ]
-- | ```
element :: forall msg. String -> Array (Attribute msg) -> Array (Element msg) -> Element msg
element tag attributes children = Element
  { namespace: Nothing
  , tag
  , attributes
  , children
  }

-- | Create a namespaced element
-- |
-- | Used for SVG, MathML, or custom XML namespaces.
-- |
-- | ```purescript
-- | elementNS SVG "circle" [ attr "r" "50" ] []
-- | ```
elementNS :: forall msg. Namespace -> String -> Array (Attribute msg) -> Array (Element msg) -> Element msg
elementNS ns tag attributes children = Element
  { namespace: Just ns
  , tag
  , attributes
  , children
  }

-- | Create a text node
-- |
-- | Text nodes contain only string content and cannot have attributes or children.
-- |
-- | ```purescript
-- | text "Hello, world!"
-- | ```
text :: forall msg. String -> Element msg
text = Text

-- | Empty element (renders nothing)
-- |
-- | Useful for conditional rendering where you want to show nothing.
-- |
-- | ```purescript
-- | if showContent then div_ [] [ text "Content" ] else empty
-- | ```
empty :: forall msg. Element msg
empty = Empty

-- | Create a keyed element for efficient list diffing
-- |
-- | Keys help the diffing algorithm identify which items have changed,
-- | moved, or been added/removed. Use unique, stable keys.
-- |
-- | ```purescript
-- | keyed "ul" []
-- |   [ Tuple "item-1" (li_ [] [ text "First" ])
-- |   , Tuple "item-2" (li_ [] [ text "Second" ])
-- |   ]
-- | ```
keyed :: forall msg. String -> Array (Attribute msg) -> Array (Tuple String (Element msg)) -> Element msg
keyed tag attributes children = Keyed
  { namespace: Nothing
  , tag
  , attributes
  , children
  }

-- | Create a lazy element that defers rendering
-- |
-- | The thunk is only evaluated when the element needs to be rendered.
-- | The key is used to determine if the element needs to be re-evaluated.
-- |
-- | ```purescript
-- | lazy "expensive-list" \_ -> renderExpensiveList items
-- | ```
lazy :: forall msg. String -> (Unit -> Element msg) -> Element msg
lazy key thunk = Lazy { thunk, key }
