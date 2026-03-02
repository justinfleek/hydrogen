-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // render // element // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Types for Hydrogen Elements
-- |
-- | This module defines the fundamental data types for describing UI as pure data:
-- |
-- | - `Element` — Pure data description of a UI node
-- | - `Attribute` — Properties, attributes, styles, and event handlers
-- | - `EventHandler` — Event handler with message production
-- | - `Namespace` — HTML vs SVG vs MathML namespaces
-- |
-- | These types are not tied to any rendering target — they can be interpreted to
-- | DOM, static HTML, Canvas, WebGL, or native views.
module Hydrogen.Render.Element.Types
  ( -- * Core Types
    Element
      ( Text
      , Element
      , Keyed
      , Lazy
      , Empty
      )
  , Attribute
      ( Attr
      , AttrNS
      , Prop
      , PropBool
      , Handler
      , Style
      )
  , EventHandler
      ( OnClick
      , OnDoubleClick
      , OnMouseDown
      , OnMouseUp
      , OnMouseMove
      , OnMouseEnter
      , OnMouseLeave
      , OnFocus
      , OnBlur
      , OnInput
      , OnChange
      , OnSubmit
      , OnKeyDown
      , OnKeyUp
      , OnKeyPress
      , OnScroll
      , OnWheel
      , OnDragStart
      , OnDrag
      , OnDragEnd
      , OnDragEnter
      , OnDragLeave
      , OnDragOver
      , OnDrop
      , OnTouchStart
      , OnTouchMove
      , OnTouchEnd
      , OnTouchCancel
      , CustomEvent
      )
  , Namespace
      ( HTML
      , SVG
      , MathML
      , Custom
      )
  
  -- * Internal Helpers
  , mapAttrMsg
  , mapHandlerMsg
  ) where

import Prelude
  ( class Eq
  , class Functor
  , class Show
  , Unit
  , map
  , show
  , (<>)
  , (<<<)
  )


import Data.Maybe (Maybe)
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace for elements (HTML vs SVG vs MathML)
data Namespace
  = HTML
  | SVG
  | MathML
  | Custom String

derive instance eqNamespace :: Eq Namespace

instance showNamespace :: Show Namespace where
  show HTML = "HTML"
  show SVG = "SVG"
  show MathML = "MathML"
  show (Custom ns) = "Custom " <> show ns

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // element
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hydrogen Element — pure data description of a UI node
-- |
-- | The `msg` type parameter represents the message type that event handlers
-- | can produce. This follows the Elm architecture pattern.
-- |
-- | Variants:
-- | - `Text` — A text node containing a string
-- | - `Element` — A standard element with tag, attributes, and children
-- | - `Keyed` — A keyed element for efficient list diffing
-- | - `Lazy` — A deferred element that delays rendering until needed
-- | - `Empty` — Renders nothing (useful for conditional rendering)
data Element msg
  = Text String
  | Element
      { namespace :: Maybe Namespace
      , tag :: String
      , attributes :: Array (Attribute msg)
      , children :: Array (Element msg)
      }
  | Keyed
      { namespace :: Maybe Namespace
      , tag :: String
      , attributes :: Array (Attribute msg)
      , children :: Array (Tuple String (Element msg))
      }
  | Lazy
      { thunk :: Unit -> Element msg
      , key :: String
      }
  | Empty

instance functorElement :: Functor Element where
  map f = case _ of
    Text s -> Text s
    Element r -> Element r
      { attributes = map (mapAttrMsg f) r.attributes
      , children = map (map f) r.children
      }
    Keyed r -> Keyed r
      { attributes = map (mapAttrMsg f) r.attributes
      , children = map (\(Tuple k v) -> Tuple k (map f v)) r.children
      }
    Lazy r -> Lazy { thunk: map f <<< r.thunk, key: r.key }
    Empty -> Empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // attribute
-- ═════════════════════════════════════════════════════════════════════════════

-- | Attribute on an element — either a property, attribute, or event handler
-- |
-- | Variants:
-- | - `Attr` — HTML attribute (name, value)
-- | - `AttrNS` — Namespaced attribute (ns, name, value) e.g., xlink:href
-- | - `Prop` — DOM property (name, value)
-- | - `PropBool` — Boolean DOM property (renders as present/absent)
-- | - `Handler` — Event handler that produces messages
-- | - `Style` — Inline style (property, value)
data Attribute msg
  = Attr String String
  | AttrNS String String String
  | Prop String String
  | PropBool String Boolean
  | Handler (EventHandler msg)
  | Style String String

instance functorAttribute :: Functor Attribute where
  map f = case _ of
    Attr n v -> Attr n v
    AttrNS ns n v -> AttrNS ns n v
    Prop n v -> Prop n v
    PropBool n v -> PropBool n v
    Handler h -> Handler (mapHandlerMsg f h)
    Style p v -> Style p v

-- | Map over the message type of an attribute
mapAttrMsg :: forall a b. (a -> b) -> Attribute a -> Attribute b
mapAttrMsg = map

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // event handler
-- ═════════════════════════════════════════════════════════════════════════════

-- | Event handler with message production
-- |
-- | Each variant corresponds to a DOM event type. Some handlers receive
-- | event data (like input value or key code) and transform it to a message.
data EventHandler msg
  = OnClick msg
  | OnDoubleClick msg
  | OnMouseDown msg
  | OnMouseUp msg
  | OnMouseMove msg
  | OnMouseEnter msg
  | OnMouseLeave msg
  | OnFocus msg
  | OnBlur msg
  | OnInput (String -> msg)
  | OnChange (String -> msg)
  | OnSubmit msg
  | OnKeyDown (String -> msg)
  | OnKeyUp (String -> msg)
  | OnKeyPress (String -> msg)
  | OnScroll msg
  | OnWheel msg
  | OnDragStart msg
  | OnDrag msg
  | OnDragEnd msg
  | OnDragEnter msg
  | OnDragLeave msg
  | OnDragOver msg
  | OnDrop msg
  | OnTouchStart msg
  | OnTouchMove msg
  | OnTouchEnd msg
  | OnTouchCancel msg
  | CustomEvent String msg

-- | Map over the message type of an event handler
mapHandlerMsg :: forall a b. (a -> b) -> EventHandler a -> EventHandler b
mapHandlerMsg f = case _ of
  OnClick m -> OnClick (f m)
  OnDoubleClick m -> OnDoubleClick (f m)
  OnMouseDown m -> OnMouseDown (f m)
  OnMouseUp m -> OnMouseUp (f m)
  OnMouseMove m -> OnMouseMove (f m)
  OnMouseEnter m -> OnMouseEnter (f m)
  OnMouseLeave m -> OnMouseLeave (f m)
  OnFocus m -> OnFocus (f m)
  OnBlur m -> OnBlur (f m)
  OnInput g -> OnInput (f <<< g)
  OnChange g -> OnChange (f <<< g)
  OnSubmit m -> OnSubmit (f m)
  OnKeyDown g -> OnKeyDown (f <<< g)
  OnKeyUp g -> OnKeyUp (f <<< g)
  OnKeyPress g -> OnKeyPress (f <<< g)
  OnScroll m -> OnScroll (f m)
  OnWheel m -> OnWheel (f m)
  OnDragStart m -> OnDragStart (f m)
  OnDrag m -> OnDrag (f m)
  OnDragEnd m -> OnDragEnd (f m)
  OnDragEnter m -> OnDragEnter (f m)
  OnDragLeave m -> OnDragLeave (f m)
  OnDragOver m -> OnDragOver (f m)
  OnDrop m -> OnDrop (f m)
  OnTouchStart m -> OnTouchStart (f m)
  OnTouchMove m -> OnTouchMove (f m)
  OnTouchEnd m -> OnTouchEnd (f m)
  OnTouchCancel m -> OnTouchCancel (f m)
  CustomEvent n m -> CustomEvent n (f m)
