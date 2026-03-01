-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // render // element // svg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SVG Element Helpers
-- |
-- | Convenience functions for creating SVG elements. All SVG elements are
-- | created in the SVG namespace to ensure proper rendering.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Render.Element.SVG (svg_, circle_, rect_)
-- |
-- | myIcon :: forall msg. Element msg
-- | myIcon =
-- |   svg_ [ attr "viewBox" "0 0 100 100" ]
-- |     [ circle_ [ attr "cx" "50", attr "cy" "50", attr "r" "40" ]
-- |     ]
-- | ```
module Hydrogen.Render.Element.SVG
  ( -- * SVG Namespace
    svgNS
  , svgElement
  
  -- * Root Element
  , svg_
  
  -- * Shape Elements
  , circle_
  , rect_
  , path_
  , line_
  , polyline_
  
  -- * Container Elements
  , g_
  , defs_
  , clipPath_
  , mask_
  
  -- * Reference Elements
  , use_
  
  -- * Gradient Elements
  , linearGradient_
  , radialGradient_
  , stop_
  
  -- * Text Elements
  , text_
  , tspan_
  ) where

import Hydrogen.Render.Element.Types (Attribute, Element, Namespace(SVG))
import Hydrogen.Render.Element.Constructors (elementNS)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // svg // namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG namespace constant
svgNS :: Namespace
svgNS = SVG

-- | Create an SVG element with the SVG namespace
-- |
-- | This is the base constructor for all SVG elements.
svgElement :: forall msg. String -> Array (Attribute msg) -> Array (Element msg) -> Element msg
svgElement = elementNS SVG

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // root // element
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG root element
-- |
-- | The root container for all SVG content. Typically includes viewBox attribute.
svg_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
svg_ = svgElement "svg"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shape // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle element (void - no children)
-- |
-- | Attributes: cx, cy, r
circle_ :: forall msg. Array (Attribute msg) -> Element msg
circle_ attrs = svgElement "circle" attrs []

-- | Rectangle element (void - no children)
-- |
-- | Attributes: x, y, width, height, rx, ry
rect_ :: forall msg. Array (Attribute msg) -> Element msg
rect_ attrs = svgElement "rect" attrs []

-- | Path element (void - no children)
-- |
-- | Attributes: d (path data)
path_ :: forall msg. Array (Attribute msg) -> Element msg
path_ attrs = svgElement "path" attrs []

-- | Line element (void - no children)
-- |
-- | Attributes: x1, y1, x2, y2
line_ :: forall msg. Array (Attribute msg) -> Element msg
line_ attrs = svgElement "line" attrs []

-- | Polyline element (void - no children)
-- |
-- | Attributes: points
polyline_ :: forall msg. Array (Attribute msg) -> Element msg
polyline_ attrs = svgElement "polyline" attrs []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // container // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Group element
-- |
-- | Container for grouping related elements. Transforms applied to a group
-- | affect all children.
g_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
g_ = svgElement "g"

-- | Definitions element
-- |
-- | Container for reusable elements like gradients, patterns, and symbols.
-- | Elements in defs are not rendered directly.
defs_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
defs_ = svgElement "defs"

-- | Clip path element
-- |
-- | Defines a clipping region. Elements outside the region are not rendered.
clipPath_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
clipPath_ = svgElement "clipPath"

-- | Mask element
-- |
-- | Defines an alpha mask. Luminance or alpha of the mask controls opacity.
mask_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
mask_ = svgElement "mask"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // reference // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Use element (void - no children)
-- |
-- | References and renders a defined element from defs.
-- | Attributes: href (or xlink:href for older browsers)
use_ :: forall msg. Array (Attribute msg) -> Element msg
use_ attrs = svgElement "use" attrs []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // gradient // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear gradient element
-- |
-- | Defines a linear gradient for fills or strokes.
-- | Attributes: x1, y1, x2, y2, gradientUnits
linearGradient_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
linearGradient_ = svgElement "linearGradient"

-- | Radial gradient element
-- |
-- | Defines a radial gradient for fills or strokes.
-- | Attributes: cx, cy, r, fx, fy, gradientUnits
radialGradient_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
radialGradient_ = svgElement "radialGradient"

-- | Gradient stop element (void - no children)
-- |
-- | Defines a color stop within a gradient.
-- | Attributes: offset, stop-color, stop-opacity
stop_ :: forall msg. Array (Attribute msg) -> Element msg
stop_ attrs = svgElement "stop" attrs []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // text // elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | SVG text element
-- |
-- | Renders text within SVG. Note: this is SVG text, not HTML text.
-- | Attributes: x, y, text-anchor, dominant-baseline
text_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
text_ = svgElement "text"

-- | Text span element
-- |
-- | Defines a subtext within an SVG text element.
-- | Attributes: x, y, dx, dy
tspan_ :: forall msg. Array (Attribute msg) -> Array (Element msg) -> Element msg
tspan_ = svgElement "tspan"
