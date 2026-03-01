-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // render // element // html
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTML Element Helpers
-- |
-- | Convenience functions for creating common HTML elements. Each function
-- | is a thin wrapper around `element` with the tag name pre-filled.
-- |
-- | ## Naming Convention
-- |
-- | All element helpers end with an underscore (`_`) to avoid conflicts
-- | with PureScript keywords and common variable names.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element.HTML (div_, span_, p_)
-- |
-- | myComponent :: forall msg. Element msg
-- | myComponent =
-- |   div_ [ class_ "container" ]
-- |     [ h1_ [] [ text "Title" ]
-- |     , p_ [] [ text "Content" ]
-- |     ]
-- | ```
module Hydrogen.Render.Element.HTML
  ( -- * Container Elements
    div_
  , span_
  , section_
  , article_
  , header_
  , footer_
  , nav_
  , main_
  , aside_
  
  -- * Text Elements
  , p_
  , h1_
  , h2_
  , h3_
  , h4_
  , h5_
  , h6_
  , strong_
  , em_
  , code_
  , pre_
  , blockquote_
  
  -- * List Elements
  , ul_
  , ol_
  , li_
  
  -- * Table Elements
  , table_
  , tr_
  , td_
  , th_
  , thead_
  , tbody_
  , tfoot_
  , caption_
  
  -- * Interactive Elements
  , a_
  , button_
  , form_
  , label_
  
  -- * Input Elements
  , input_
  , textarea_
  
  -- * Media Elements
  , img_
  
  -- * Void Elements
  , hr_
  , br_
  , meta_
  , link_
  
  -- * Script Elements
  , script_
  ) where

import Hydrogen.Render.Element.Types (Attribute, Element)
import Hydrogen.Render.Element.Constructors (element)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // container // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generic container element
div_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
div_ = element "div"

-- | Inline container element
span_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
span_ = element "span"

-- | Generic section element
section_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
section_ = element "section"

-- | Article element (self-contained content)
article_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
article_ = element "article"

-- | Header element
header_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
header_ = element "header"

-- | Footer element
footer_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
footer_ = element "footer"

-- | Navigation element
nav_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
nav_ = element "nav"

-- | Main content element
main_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
main_ = element "main"

-- | Aside element (tangential content)
aside_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
aside_ = element "aside"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // text // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paragraph element
p_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
p_ = element "p"

-- | Heading level 1
h1_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h1_ = element "h1"

-- | Heading level 2
h2_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h2_ = element "h2"

-- | Heading level 3
h3_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h3_ = element "h3"

-- | Heading level 4
h4_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h4_ = element "h4"

-- | Heading level 5
h5_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h5_ = element "h5"

-- | Heading level 6
h6_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
h6_ = element "h6"

-- | Strong importance element (typically bold)
strong_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
strong_ = element "strong"

-- | Emphasis element (typically italic)
em_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
em_ = element "em"

-- | Inline code element
code_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
code_ = element "code"

-- | Preformatted text element
pre_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
pre_ = element "pre"

-- | Block quotation element
blockquote_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
blockquote_ = element "blockquote"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // list // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unordered list element
ul_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
ul_ = element "ul"

-- | Ordered list element
ol_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
ol_ = element "ol"

-- | List item element
li_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
li_ = element "li"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // table // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Table element
table_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
table_ = element "table"

-- | Table row element
tr_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tr_ = element "tr"

-- | Table data cell element
td_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
td_ = element "td"

-- | Table header cell element
th_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
th_ = element "th"

-- | Table head element
thead_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
thead_ = element "thead"

-- | Table body element
tbody_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tbody_ = element "tbody"

-- | Table foot element
tfoot_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tfoot_ = element "tfoot"

-- | Table caption element
caption_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
caption_ = element "caption"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // interactive // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor (link) element
a_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
a_ = element "a"

-- | Button element
button_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
button_ = element "button"

-- | Form element
form_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
form_ = element "form"

-- | Label element (for form inputs)
label_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
label_ = element "label"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // input // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Input element (void element - no children)
input_ :: forall msg. Array (Attribute msg) -> Element msg
input_ attrs = element "input" attrs []

-- | Textarea element
textarea_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
textarea_ = element "textarea"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // media // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Image element (void element - no children)
img_ :: forall msg. Array (Attribute msg) -> Element msg
img_ attrs = element "img" attrs []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // void // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Horizontal rule (void element)
hr_ :: forall msg. Array (Attribute msg) -> Element msg
hr_ attrs = element "hr" attrs []

-- | Line break (void element)
br_ :: forall msg. Array (Attribute msg) -> Element msg
br_ attrs = element "br" attrs []

-- | Meta element (void element, typically in head)
meta_ :: forall msg. Array (Attribute msg) -> Element msg
meta_ attrs = element "meta" attrs []

-- | Link element (void element, typically in head)
link_ :: forall msg. Array (Attribute msg) -> Element msg
link_ attrs = element "link" attrs []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // script // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Script element
script_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
script_ = element "script"
