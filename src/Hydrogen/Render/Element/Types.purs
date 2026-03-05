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
      , StyleAtom
      )
  , StyleValue
      ( StyleColor
      , StyleColorA
      , StyleFill
      , StyleFontSize
      , StyleFontWeight
      , StyleFontFamily
      , StyleLineHeight
      , StyleSpacing
      , StyleRadius
      , StyleBorder
      , StyleTransform
      , StyleTransition
      , StyleOpacity
      , StyleShadow
      , StylePixel
      , StyleDisplay
      , StyleFlexDirection
      , StyleFlexAlign
      , StyleFlexJustify
      , StyleCursor
      , StyleVisibility
      , StyleOverflow
      , StyleTextAlign
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
  , StyleProperty
      ( PropBackgroundColor
      , PropColor
      , PropFill
      , PropFontSize
      , PropFontWeight
      , PropFontFamily
      , PropLineHeight
      , PropPadding
      , PropPaddingTop
      , PropPaddingRight
      , PropPaddingBottom
      , PropPaddingLeft
      , PropMargin
      , PropMarginTop
      , PropMarginRight
      , PropMarginBottom
      , PropMarginLeft
      , PropBorderRadius
      , PropBorder
      , PropBorderTop
      , PropBorderRight
      , PropBorderBottom
      , PropBorderLeft
      , PropTransform
      , PropTransition
      , PropOpacity
      , PropBoxShadow
      , PropWidth
      , PropHeight
      , PropMinWidth
      , PropMinHeight
      , PropMaxWidth
      , PropMaxHeight
      , PropDisplay
      , PropFlexDirection
      , PropAlignItems
      , PropJustifyContent
      , PropCursor
      , PropVisibility
      , PropOverflow
      , PropTextAlign
      )
  , Display
      ( DisplayNone
      , DisplayBlock
      , DisplayInline
      , DisplayInlineBlock
      , DisplayFlex
      , DisplayInlineFlex
      , DisplayGrid
      , DisplayInlineGrid
      , DisplayContents
      )
  , FlexDirection
      ( FlexRow
      , FlexRowReverse
      , FlexColumn
      , FlexColumnReverse
      )
  , FlexAlign
      ( AlignStart
      , AlignEnd
      , AlignCenter
      , AlignStretch
      , AlignBaseline
      )
  , FlexJustify
      ( JustifyStart
      , JustifyEnd
      , JustifyCenter
      , JustifySpaceBetween
      , JustifySpaceAround
      , JustifySpaceEvenly
      )
  , Cursor
      ( CursorAuto
      , CursorDefault
      , CursorPointer
      , CursorWait
      , CursorText
      , CursorMove
      , CursorNotAllowed
      , CursorGrab
      , CursorGrabbing
      )
  , Visibility
      ( VisibilityVisible
      , VisibilityHidden
      , VisibilityCollapse
      )
  , Overflow
      ( OverflowVisible
      , OverflowHidden
      , OverflowScroll
      , OverflowAuto
      )
  , TextAlign
      ( TextAlignLeft
      , TextAlignRight
      , TextAlignCenter
      , TextAlignJustify
      , TextAlignStart
      , TextAlignEnd
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

-- Schema atoms for typed styles
import Hydrogen.Schema.Color.RGB (RGB, RGBA) as Color
import Hydrogen.Schema.Typography.FontSize (FontSize) as Typography
import Hydrogen.Schema.Typography.FontWeight (FontWeight) as Typography
import Hydrogen.Schema.Typography.LineHeight (LineHeight) as Typography
import Hydrogen.Schema.Typography.FontFamily (FontFamily) as Typography
import Hydrogen.Schema.Geometry.Spacing (SpacingValue) as Geometry
import Hydrogen.Schema.Geometry.Radius (Corners) as Geometry
import Hydrogen.Schema.Geometry.Border (Border) as Geometry
import Hydrogen.Schema.Motion.Transform (LayerTransform2D) as Motion
import Hydrogen.Schema.Motion.Transition (TransitionConfig) as Motion
import Hydrogen.Schema.Color.Opacity (Opacity) as ColorOpacity
import Hydrogen.Schema.Motion.Transform (Opacity) as MotionOpacity
import Hydrogen.Schema.Surface.Fill (Fill) as Surface
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow) as Elevation
import Hydrogen.Schema.Dimension.Device (Pixel) as Dimension

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
--                                                                 // style value
-- ═════════════════════════════════════════════════════════════════════════════

-- | StyleValue — Typed style values using Schema atoms.
-- |
-- | NO STRINGS. Each variant wraps a bounded Schema atom.
-- | The runtime interprets these to the target format (CSS, Canvas, WebGPU).
data StyleValue
  -- Color atoms
  = StyleColor Color.RGB
  | StyleColorA Color.RGBA
  | StyleFill Surface.Fill
  
  -- Typography atoms
  | StyleFontSize Typography.FontSize
  | StyleFontWeight Typography.FontWeight
  | StyleFontFamily Typography.FontFamily
  | StyleLineHeight Typography.LineHeight
  
  -- Geometry atoms
  | StyleSpacing Geometry.SpacingValue
  | StyleRadius Geometry.Corners
  | StyleBorder Geometry.Border
  
  -- Motion atoms
  | StyleTransform Motion.LayerTransform2D
  | StyleTransition Motion.TransitionConfig
  | StyleOpacity MotionOpacity.Opacity
  
  -- Elevation atoms
  | StyleShadow Elevation.LayeredShadow
  
  -- Dimension atoms
  | StylePixel Dimension.Pixel
  
  -- Layout enums (bounded)
  | StyleDisplay Display
  | StyleFlexDirection FlexDirection
  | StyleFlexAlign FlexAlign
  | StyleFlexJustify FlexJustify
  | StyleCursor Cursor
  | StyleVisibility Visibility
  | StyleOverflow Overflow
  | StyleTextAlign TextAlign

-- | Display mode — bounded enum
data Display
  = DisplayNone
  | DisplayBlock
  | DisplayInline
  | DisplayInlineBlock
  | DisplayFlex
  | DisplayInlineFlex
  | DisplayGrid
  | DisplayInlineGrid
  | DisplayContents

derive instance eqDisplay :: Eq Display

-- | Flex direction — bounded enum
data FlexDirection
  = FlexRow
  | FlexRowReverse
  | FlexColumn
  | FlexColumnReverse

derive instance eqFlexDirection :: Eq FlexDirection

-- | Flex alignment — bounded enum
data FlexAlign
  = AlignStart
  | AlignEnd
  | AlignCenter
  | AlignStretch
  | AlignBaseline

derive instance eqFlexAlign :: Eq FlexAlign

-- | Flex justify — bounded enum
data FlexJustify
  = JustifyStart
  | JustifyEnd
  | JustifyCenter
  | JustifySpaceBetween
  | JustifySpaceAround
  | JustifySpaceEvenly

derive instance eqFlexJustify :: Eq FlexJustify

-- | Cursor — bounded enum
data Cursor
  = CursorAuto
  | CursorDefault
  | CursorPointer
  | CursorWait
  | CursorText
  | CursorMove
  | CursorNotAllowed
  | CursorGrab
  | CursorGrabbing

derive instance eqCursor :: Eq Cursor

-- | Visibility — bounded enum
data Visibility
  = VisibilityVisible
  | VisibilityHidden
  | VisibilityCollapse

derive instance eqVisibility :: Eq Visibility

-- | Overflow — bounded enum
data Overflow
  = OverflowVisible
  | OverflowHidden
  | OverflowScroll
  | OverflowAuto

derive instance eqOverflow :: Eq Overflow

-- | Text alignment — bounded enum
data TextAlign
  = TextAlignLeft
  | TextAlignRight
  | TextAlignCenter
  | TextAlignJustify
  | TextAlignStart
  | TextAlignEnd

derive instance eqTextAlign :: Eq TextAlign

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
-- | - `StyleAtom` — Typed style using Schema atoms (NO STRINGS)
data Attribute msg
  = Attr String String
  | AttrNS String String String
  | Prop String String
  | PropBool String Boolean
  | Handler (EventHandler msg)
  | StyleAtom StyleProperty StyleValue

-- | Style property — what aspect of the element this style affects
data StyleProperty
  = PropBackgroundColor
  | PropColor
  | PropFill
  | PropFontSize
  | PropFontWeight
  | PropFontFamily
  | PropLineHeight
  | PropPadding
  | PropPaddingTop
  | PropPaddingRight
  | PropPaddingBottom
  | PropPaddingLeft
  | PropMargin
  | PropMarginTop
  | PropMarginRight
  | PropMarginBottom
  | PropMarginLeft
  | PropBorderRadius
  | PropBorder
  | PropBorderTop
  | PropBorderRight
  | PropBorderBottom
  | PropBorderLeft
  | PropTransform
  | PropTransition
  | PropOpacity
  | PropBoxShadow
  | PropWidth
  | PropHeight
  | PropMinWidth
  | PropMinHeight
  | PropMaxWidth
  | PropMaxHeight
  | PropDisplay
  | PropFlexDirection
  | PropAlignItems
  | PropJustifyContent
  | PropCursor
  | PropVisibility
  | PropOverflow
  | PropTextAlign

derive instance eqStyleProperty :: Eq StyleProperty

instance functorAttribute :: Functor Attribute where
  map f = case _ of
    Attr n v -> Attr n v
    AttrNS ns n v -> AttrNS ns n v
    Prop n v -> Prop n v
    PropBool n v -> PropBool n v
    Handler h -> Handler (mapHandlerMsg f h)
    StyleAtom p v -> StyleAtom p v

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
