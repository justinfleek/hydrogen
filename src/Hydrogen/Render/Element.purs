-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // render // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hydrogen Element — Pure Data Description of UI
-- |
-- | This module defines the core Element type that describes UI as pure data.
-- | Elements are not tied to any rendering target — they can be interpreted to:
-- |
-- | - Halogen HTML (reactive web components)
-- | - Direct DOM (browser FFI)
-- | - Static HTML strings (SSG)
-- | - Canvas 2D (motion graphics)
-- | - WebGL (3D rendering)
-- | - Native views (React Native, Flutter)
-- |
-- | ## Design Principles
-- |
-- | Following libevring's pattern: **separate what from how**.
-- |
-- | ```
-- | Element × Event → Element × [Effect]
-- | ```
-- |
-- | Elements are pure, testable, serializable. Targets execute against reality.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element as E
-- |
-- | myButton :: forall msg. msg -> String -> Element msg
-- | myButton onClick label =
-- |   E.element "button"
-- |     [ E.onClick onClick
-- |     , E.class_ "btn btn-primary"
-- |     ]
-- |     [ E.text label ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- |
-- | - `Hydrogen.Render.Element.Types` — Core data types
-- | - `Hydrogen.Render.Element.Constructors` — Element creation
-- | - `Hydrogen.Render.Element.HTML` — HTML element helpers
-- | - `Hydrogen.Render.Element.SVG` — SVG element helpers
-- | - `Hydrogen.Render.Element.Attributes` — Attribute constructors
-- | - `Hydrogen.Render.Element.Events` — Event handler constructors
-- | - `Hydrogen.Render.Element.Manipulation` — Element utilities
module Hydrogen.Render.Element
  ( -- * Core Types (from Types)
    module Hydrogen.Render.Element.Types
  
  -- * Element Constructors (from Constructors)
  , module Hydrogen.Render.Element.Constructors
  
  -- * Common Elements (from HTML)
  , module Hydrogen.Render.Element.HTML
  
  -- * SVG Elements (from SVG)
  , module Hydrogen.Render.Element.SVG
  
  -- * Attributes (from Attributes)
  , module Hydrogen.Render.Element.Attributes
  
  -- * Event Handlers (from Events)
  , module Hydrogen.Render.Element.Events
  
  -- * Element Manipulation (from Manipulation)
  , module Hydrogen.Render.Element.Manipulation
  ) where

import Hydrogen.Render.Element.Types
  ( Element(Element, Empty, Keyed, Lazy, Text)
  , Attribute(Attr, AttrNS, Handler, Prop, PropBool, Style)
  , EventHandler
      ( CustomEvent
      , OnBlur
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
  , Namespace(Custom, HTML, MathML, SVG)
  , mapAttrMsg
  , mapHandlerMsg
  )

import Hydrogen.Render.Element.Constructors
  ( element
  , elementNS
  , text
  , empty
  , keyed
  , lazy
  )

import Hydrogen.Render.Element.HTML
  ( div_
  , span_
  , p_
  , a_
  , button_
  , input_
  , img_
  , canvas_
  , form_
  , label_
  , h1_
  , h2_
  , h3_
  , h4_
  , h5_
  , h6_
  , ul_
  , ol_
  , li_
  , table_
  , tr_
  , td_
  , th_
  , thead_
  , tbody_
  , tfoot_
  , caption_
  , section_
  , article_
  , header_
  , footer_
  , nav_
  , main_
  , aside_
  , strong_
  , em_
  , code_
  , pre_
  , blockquote_
  , hr_
  , br_
  , meta_
  , link_
  , script_
  , textarea_
  )

import Hydrogen.Render.Element.SVG
  ( svgNS
  , svg_
  , svgElement
  , circle_
  , rect_
  , path_
  , line_
  , g_
  , defs_
  , use_
  , clipPath_
  , mask_
  , linearGradient_
  , radialGradient_
  , stop_
  , text_
  , tspan_
  , polyline_
  , polygon_
  )

import Hydrogen.Render.Element.Attributes
  ( attr
  , attrNS
  , prop
  , propBool
  , class_
  , classes
  , id_
  , style
  , styles
  , href
  , src
  , alt
  , title
  , placeholder
  , value
  , type_
  , name
  , min_
  , max_
  , step_
  , disabled
  , checked
  , selected
  , readonly
  , required
  , autofocus
  , tabIndex
  , role
  , ariaLabel
  , ariaHidden
  , ariaDescribedBy
  , ariaLabelledBy
  , ariaLive
  , ariaAtomic
  , ariaRole
  , dataAttr
  )

import Hydrogen.Render.Element.Events
  ( onClick
  , onDoubleClick
  , onMouseDown
  , onMouseUp
  , onMouseMove
  , onMouseEnter
  , onMouseLeave
  , onFocus
  , onBlur
  , onInput
  , onChange
  , onSubmit
  , onKeyDown
  , onKeyUp
  , onKeyPress
  , onScroll
  , onWheel
  , onDragStart
  , onDrag
  , onDragEnd
  , onDragEnter
  , onDragLeave
  , onDragOver
  , onDrop
  , onTouchStart
  , onTouchMove
  , onTouchEnd
  , onTouchCancel
  )

import Hydrogen.Render.Element.Manipulation
  ( mapMsg
  , filterChildren
  , prependChild
  , appendChild
  , withAttribute
  , withAttributes
  , forceLazy
  , forceAllLazy
  , childCount
  , firstChild
  , lastChild
  , isEmpty
  )
