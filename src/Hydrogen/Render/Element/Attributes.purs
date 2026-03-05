-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // render // element // attributes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Attribute Constructors
-- |
-- | Functions for creating HTML attributes, DOM properties, and inline styles.
-- |
-- | ## Attributes vs Properties
-- |
-- | - **Attributes** are set via `setAttribute` and appear in the HTML
-- | - **Properties** are set directly on the DOM object
-- |
-- | For most cases, use the specific helpers (`class_`, `href`, etc.) which
-- | choose the correct approach for each attribute.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element.Attributes (class_, href, disabled)
-- |
-- | myLink :: forall msg. Element msg
-- | myLink = a_ [ href "/about", class_ "nav-link" ] [ text "About" ]
-- | ```
module Hydrogen.Render.Element.Attributes
  ( -- * Generic Constructors
    attr
  , attrNS
  , prop
  , propBool
  
  -- * Common Attributes
  , class_
  , classes
  , id_
  , href
  , src
  , alt
  , title
  , placeholder
  , value
  , type_
  , name
  
  -- * Range/Number Attributes
  , min_
  , max_
  , step_
  
  -- * Boolean Attributes
  , disabled
  , checked
  , selected
  , readonly
  , required
  , autofocus
  
  -- * Accessibility Attributes
  , tabIndex
  , role
  , ariaLabel
  , ariaHidden
  , ariaDescribedBy
  , ariaLabelledBy
  , ariaLive
  , ariaAtomic
  , ariaRole
  
  -- * Data Attributes
  , dataAttr
  
  -- * Typed Style Attributes (Schema atoms)
  -- Color
  , backgroundColor
  , color
  -- Typography
  , fontSize
  , fontWeight
  -- Spacing
  , padding
  , margin
  -- Border
  , border
  , borderBottom
  -- Dimension
  , width
  , height
  , maxWidth
  , maxHeight
  -- Transform
  , transform
  , transition
  , opacity
  -- Layout
  , display
  , flexDirection
  , alignItems
  , justifyContent
  , cursor
  , visibility
  , overflow
  , textAlign
  ) where

import Prelude
  ( show
  , (<>)
  , (==)
  )

import Data.Array (filter) as Array
import Data.Functor (map) as Array
import Data.String (joinWith)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element.Types
  ( Attribute(Attr, AttrNS, Prop, PropBool, StyleAtom)
  , StyleProperty
      ( PropBackgroundColor
      , PropColor
      , PropFontSize
      , PropFontWeight
      , PropPadding
      , PropMargin
      , PropBorder
      , PropBorderBottom
      , PropTransform
      , PropTransition
      , PropOpacity
      , PropWidth
      , PropHeight
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
  , StyleValue
      ( StyleColor
      , StyleFontSize
      , StyleFontWeight
      , StyleSpacing
      , StyleBorder
      , StyleTransform
      , StyleTransition
      , StyleOpacity
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
  , Display
  , FlexDirection
  , FlexAlign
  , FlexJustify
  , Cursor
  , Visibility
  , Overflow
  , TextAlign
  )
import Hydrogen.Schema.Color.RGB (RGB) as Color
import Hydrogen.Schema.Typography.FontSize (FontSize) as Typography
import Hydrogen.Schema.Typography.FontWeight (FontWeight) as Typography
import Hydrogen.Schema.Geometry.Spacing (SpacingValue) as Geometry
import Hydrogen.Schema.Geometry.Border (Border) as Geometry
import Hydrogen.Schema.Motion.Transform (Opacity, LayerTransform2D) as Motion
import Hydrogen.Schema.Motion.Transition (TransitionConfig) as Motion
import Hydrogen.Schema.Dimension.Device (Pixel) as Dimension

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // generic // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an HTML attribute
-- |
-- | Rendered as `name="value"` in HTML output.
attr :: forall msg. String -> String -> Attribute msg
attr = Attr

-- | Create a namespaced attribute
-- |
-- | Used for attributes like `xlink:href` in SVG.
attrNS :: forall msg. String -> String -> String -> Attribute msg
attrNS = AttrNS

-- | Create a DOM property
-- |
-- | Set directly on the DOM object, not via setAttribute.
prop :: forall msg. String -> String -> Attribute msg
prop = Prop

-- | Create a boolean DOM property
-- |
-- | Boolean properties render as present (attribute name only) when true,
-- | and are omitted entirely when false.
propBool :: forall msg. String -> Boolean -> Attribute msg
propBool = PropBool

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // common // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the class attribute
class_ :: forall msg. String -> Attribute msg
class_ = Attr "class"

-- | Set multiple classes (joined with space)
-- |
-- | Empty strings are filtered out.
classes :: forall msg. Array String -> Attribute msg
classes cs = Attr "class" (joinWith " " (Array.filter (\s -> (s == "") == false) cs))

-- | Set the id attribute
id_ :: forall msg. String -> Attribute msg
id_ = Attr "id"

-- | Set href attribute (for links)
href :: forall msg. String -> Attribute msg
href = Attr "href"

-- | Set src attribute (for images, scripts, etc.)
src :: forall msg. String -> Attribute msg
src = Attr "src"

-- | Set alt attribute (for images)
alt :: forall msg. String -> Attribute msg
alt = Attr "alt"

-- | Set title attribute (tooltip text)
title :: forall msg. String -> Attribute msg
title = Attr "title"

-- | Set placeholder attribute (for inputs)
placeholder :: forall msg. String -> Attribute msg
placeholder = Attr "placeholder"

-- | Set value property (for form inputs)
-- |
-- | Note: This is a property, not an attribute, to properly handle
-- | dynamic updates after user input.
value :: forall msg. String -> Attribute msg
value = Prop "value"

-- | Set type attribute (for inputs, buttons)
type_ :: forall msg. String -> Attribute msg
type_ = Attr "type"

-- | Set name attribute (for form elements)
name :: forall msg. String -> Attribute msg
name = Attr "name"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // range // number // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set min attribute (for range/number inputs)
min_ :: forall msg. String -> Attribute msg
min_ = Attr "min"

-- | Set max attribute (for range/number inputs)
max_ :: forall msg. String -> Attribute msg
max_ = Attr "max"

-- | Set step attribute (for range/number inputs)
step_ :: forall msg. String -> Attribute msg
step_ = Attr "step"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // boolean // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set disabled property
disabled :: forall msg. Boolean -> Attribute msg
disabled = PropBool "disabled"

-- | Set checked property (for checkboxes/radio buttons)
checked :: forall msg. Boolean -> Attribute msg
checked = PropBool "checked"

-- | Set selected property (for options)
selected :: forall msg. Boolean -> Attribute msg
selected = PropBool "selected"

-- | Set readonly property
readonly :: forall msg. Boolean -> Attribute msg
readonly = PropBool "readOnly"

-- | Set required property
required :: forall msg. Boolean -> Attribute msg
required = PropBool "required"

-- | Set autofocus property
autofocus :: forall msg. Boolean -> Attribute msg
autofocus = PropBool "autofocus"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // accessibility // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tabindex attribute
tabIndex :: forall msg. Int -> Attribute msg
tabIndex i = Attr "tabindex" (show i)

-- | Set ARIA role
role :: forall msg. String -> Attribute msg
role = Attr "role"

-- | Set aria-label (accessible name)
ariaLabel :: forall msg. String -> Attribute msg
ariaLabel = Attr "aria-label"

-- | Set aria-hidden
ariaHidden :: forall msg. Boolean -> Attribute msg
ariaHidden b = Attr "aria-hidden" (if b then "true" else "false")

-- | Set aria-describedby (reference to description element)
ariaDescribedBy :: forall msg. String -> Attribute msg
ariaDescribedBy = Attr "aria-describedby"

-- | Set aria-labelledby (reference to label element)
ariaLabelledBy :: forall msg. String -> Attribute msg
ariaLabelledBy = Attr "aria-labelledby"

-- | Set aria-live for live regions
-- |
-- | Values: "off", "polite", "assertive"
ariaLive :: forall msg. String -> Attribute msg
ariaLive = Attr "aria-live"

-- | Set aria-atomic for live regions
-- |
-- | Values: "true", "false"
ariaAtomic :: forall msg. String -> Attribute msg
ariaAtomic = Attr "aria-atomic"

-- | Set aria role (alias for role)
ariaRole :: forall msg. String -> Attribute msg
ariaRole = Attr "role"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // data // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set a data-* attribute
-- |
-- | ```purescript
-- | dataAttr "user-id" "123"  -- renders as data-user-id="123"
-- | ```
dataAttr :: forall msg. String -> String -> Attribute msg
dataAttr key = Attr ("data-" <> key)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // style // attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- Color styles
-- | Set background color using Schema RGB atom
backgroundColor :: forall msg. Color.RGB -> Attribute msg
backgroundColor c = StyleAtom PropBackgroundColor (StyleColor c)

-- | Set text color using Schema RGB atom
color :: forall msg. Color.RGB -> Attribute msg
color c = StyleAtom PropColor (StyleColor c)

-- Typography styles
-- | Set font size using Typography.FontSize atom
fontSize :: forall msg. Typography.FontSize -> Attribute msg
fontSize s = StyleAtom PropFontSize (StyleFontSize s)

-- | Set font weight using Typography.FontWeight atom
fontWeight :: forall msg. Typography.FontWeight -> Attribute msg
fontWeight w = StyleAtom PropFontWeight (StyleFontWeight w)

-- Spacing styles
-- | Set padding using Geometry.SpacingValue atom
padding :: forall msg. Geometry.SpacingValue -> Attribute msg
padding s = StyleAtom PropPadding (StyleSpacing s)

-- | Set margin using Geometry.SpacingValue atom
margin :: forall msg. Geometry.SpacingValue -> Attribute msg
margin s = StyleAtom PropMargin (StyleSpacing s)

-- Border styles
-- | Set border using Geometry.Border atom
border :: forall msg. Geometry.Border -> Attribute msg
border b = StyleAtom PropBorder (StyleBorder b)

-- | Set bottom border using Geometry.Border atom
borderBottom :: forall msg. Geometry.Border -> Attribute msg
borderBottom b = StyleAtom PropBorderBottom (StyleBorder b)

-- Dimension styles
-- | Set width using Dimension.Pixel atom
width :: forall msg. Dimension.Pixel -> Attribute msg
width p = StyleAtom PropWidth (StylePixel p)

-- | Set height using Dimension.Pixel atom
height :: forall msg. Dimension.Pixel -> Attribute msg
height p = StyleAtom PropHeight (StylePixel p)

-- | Set max-width using Dimension.Pixel atom
maxWidth :: forall msg. Dimension.Pixel -> Attribute msg
maxWidth p = StyleAtom PropMaxWidth (StylePixel p)

-- | Set max-height using Dimension.Pixel atom
maxHeight :: forall msg. Dimension.Pixel -> Attribute msg
maxHeight p = StyleAtom PropMaxHeight (StylePixel p)

-- Transform styles
-- | Set transform using Motion.LayerTransform2D atom
transform :: forall msg. Motion.LayerTransform2D -> Attribute msg
transform t = StyleAtom PropTransform (StyleTransform t)

-- | Set transition using Motion.TransitionConfig atom
transition :: forall msg. Motion.TransitionConfig -> Attribute msg
transition t = StyleAtom PropTransition (StyleTransition t)

-- | Set opacity using Motion.Opacity (0.0 to 1.0, clamped)
opacity :: forall msg. Motion.Opacity -> Attribute msg
opacity o = StyleAtom PropOpacity (StyleOpacity o)

-- Layout styles
-- | Set display mode using bounded enum
display :: forall msg. Display -> Attribute msg
display d = StyleAtom PropDisplay (StyleDisplay d)

-- | Set flex direction using bounded enum
flexDirection :: forall msg. FlexDirection -> Attribute msg
flexDirection d = StyleAtom PropFlexDirection (StyleFlexDirection d)

-- | Set align-items using bounded enum
alignItems :: forall msg. FlexAlign -> Attribute msg
alignItems a = StyleAtom PropAlignItems (StyleFlexAlign a)

-- | Set justify-content using bounded enum
justifyContent :: forall msg. FlexJustify -> Attribute msg
justifyContent j = StyleAtom PropJustifyContent (StyleFlexJustify j)

-- | Set cursor using bounded enum
cursor :: forall msg. Cursor -> Attribute msg
cursor c = StyleAtom PropCursor (StyleCursor c)

-- | Set visibility using bounded enum
visibility :: forall msg. Visibility -> Attribute msg
visibility v = StyleAtom PropVisibility (StyleVisibility v)

-- | Set overflow using bounded enum
overflow :: forall msg. Overflow -> Attribute msg
overflow o = StyleAtom PropOverflow (StyleOverflow o)

-- | Set text-align using bounded enum
textAlign :: forall msg. TextAlign -> Attribute msg
textAlign t = StyleAtom PropTextAlign (StyleTextAlign t)
