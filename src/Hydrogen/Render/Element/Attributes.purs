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
  
  -- * Style Attributes
  , style
  , styles
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
  ( Attribute(Attr, AttrNS, Prop, PropBool, Style)
  )

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

-- | Set a single inline style
-- |
-- | ```purescript
-- | style "color" "red"
-- | style "margin-top" "10px"
-- | ```
style :: forall msg. String -> String -> Attribute msg
style = Style

-- | Set multiple inline styles
-- |
-- | ```purescript
-- | styles
-- |   [ Tuple "color" "red"
-- |   , Tuple "margin-top" "10px"
-- |   ]
-- | ```
styles :: forall msg. Array (Tuple String String) -> Array (Attribute msg)
styles = Array.map (\(Tuple p v) -> Style p v)
