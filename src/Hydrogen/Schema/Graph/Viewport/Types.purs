-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // graph // viewport // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport Types — Core primitives for viewport zoom, position, and bounds.
-- |
-- | ## Design Philosophy
-- |
-- | These are the atomic types that compose into higher-level viewport state.
-- | Each type is bounded and validated at construction.
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Graph.Viewport.Types
  ( -- * Viewport Zoom
    ViewportZoom(ViewportZoom)
  , viewportZoom
  , defaultZoom
  , zoomIn
  , zoomOut
  , zoomTo
  , zoomToFit
  , zoomLevel
  , zoomPercentage
  , minZoom
  , maxZoom
  , isMinZoom
  , isMaxZoom
  
  -- * Viewport Position (Pan)
  , ViewportPosition
  , viewportPosition
  , origin
  , panX
  , panY
  , panBy
  , panTo
  , centerOn
  
  -- * Viewport Bounds
  , ViewportBounds
  , viewportBounds
  , boundsFromCenter
  , boundsLeft
  , boundsTop
  , boundsRight
  , boundsBottom
  , boundsWidth
  , boundsHeight
  , boundsCenter
  , containsPoint
  , boundsIntersect
  , expandBounds
  
  -- * Zoom Presets
  , zoomFit
  , zoom25
  , zoom50
  , zoom100
  , zoom200
  , zoom400
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (-)
  , (+)
  , (/)
  , (*)
  , (<=)
  , (>=)
  , (&&)
  , max
  , min
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // viewport zoom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom level for graph viewport.
-- |
-- | - 1.0 = 100% (default, 1:1 mapping)
-- | - 0.5 = 50% (zoomed out, see more)
-- | - 2.0 = 200% (zoomed in, see less)
-- |
-- | Bounded to [0.01, 100.0] to prevent degenerate states.
newtype ViewportZoom = ViewportZoom Number

derive instance eqViewportZoom :: Eq ViewportZoom
derive instance ordViewportZoom :: Ord ViewportZoom

instance showViewportZoom :: Show ViewportZoom where
  show (ViewportZoom z) = show (z * 100.0) <> "%"

-- | Create a zoom level, clamped to valid range
viewportZoom :: Number -> ViewportZoom
viewportZoom z = ViewportZoom (max 0.01 (min 100.0 z))

-- | Default zoom (100%)
defaultZoom :: ViewportZoom
defaultZoom = ViewportZoom 1.0

-- | Minimum allowed zoom
minZoom :: ViewportZoom
minZoom = ViewportZoom 0.01

-- | Maximum allowed zoom
maxZoom :: ViewportZoom
maxZoom = ViewportZoom 100.0

-- | Standard zoom step multiplier
zoomStep :: Number
zoomStep = 1.2

-- | Zoom in by one step
zoomIn :: ViewportZoom -> ViewportZoom
zoomIn (ViewportZoom z) = viewportZoom (z * zoomStep)

-- | Zoom out by one step
zoomOut :: ViewportZoom -> ViewportZoom
zoomOut (ViewportZoom z) = viewportZoom (z / zoomStep)

-- | Zoom to exact level
zoomTo :: Number -> ViewportZoom
zoomTo = viewportZoom

-- | Calculate zoom to fit content in viewport
zoomToFit :: Number -> Number -> Number -> Number -> ViewportZoom
zoomToFit contentWidth contentHeight viewportWidth viewportHeight =
  let
    zoomX = viewportWidth / contentWidth
    zoomY = viewportHeight / contentHeight
  in
    viewportZoom (min zoomX zoomY)

-- | Get numeric zoom level
zoomLevel :: ViewportZoom -> Number
zoomLevel (ViewportZoom z) = z

-- | Get zoom as percentage
zoomPercentage :: ViewportZoom -> Number
zoomPercentage (ViewportZoom z) = z * 100.0

-- | Check if at minimum zoom
isMinZoom :: ViewportZoom -> Boolean
isMinZoom (ViewportZoom z) = z <= 0.01

-- | Check if at maximum zoom
isMaxZoom :: ViewportZoom -> Boolean
isMaxZoom (ViewportZoom z) = z >= 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pan position in graph space coordinates
type ViewportPosition =
  { x :: Number  -- ^ X offset (positive = right)
  , y :: Number  -- ^ Y offset (positive = down)
  }

-- | Create viewport position
viewportPosition :: Number -> Number -> ViewportPosition
viewportPosition x y = { x, y }

-- | Origin position (no pan)
origin :: ViewportPosition
origin = { x: 0.0, y: 0.0 }

-- | Get X pan
panX :: ViewportPosition -> Number
panX p = p.x

-- | Get Y pan
panY :: ViewportPosition -> Number
panY p = p.y

-- | Pan by delta
panBy :: Number -> Number -> ViewportPosition -> ViewportPosition
panBy dx dy p = { x: p.x + dx, y: p.y + dy }

-- | Pan to absolute position
panTo :: Number -> Number -> ViewportPosition
panTo = viewportPosition

-- | Center viewport on a point
centerOn :: Number -> Number -> Number -> Number -> ViewportPosition
centerOn targetX targetY viewportWidth viewportHeight =
  { x: targetX - viewportWidth / 2.0
  , y: targetY - viewportHeight / 2.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangular bounds in graph space
type ViewportBounds =
  { left :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  }

-- | Create bounds from edges
viewportBounds :: Number -> Number -> Number -> Number -> ViewportBounds
viewportBounds left top right bottom =
  { left: min left right
  , top: min top bottom
  , right: max left right
  , bottom: max top bottom
  }

-- | Create bounds from center and size
boundsFromCenter :: Number -> Number -> Number -> Number -> ViewportBounds
boundsFromCenter centerX centerY width height =
  { left: centerX - width / 2.0
  , top: centerY - height / 2.0
  , right: centerX + width / 2.0
  , bottom: centerY + height / 2.0
  }

-- | Get left edge
boundsLeft :: ViewportBounds -> Number
boundsLeft b = b.left

-- | Get top edge
boundsTop :: ViewportBounds -> Number
boundsTop b = b.top

-- | Get right edge
boundsRight :: ViewportBounds -> Number
boundsRight b = b.right

-- | Get bottom edge
boundsBottom :: ViewportBounds -> Number
boundsBottom b = b.bottom

-- | Get width
boundsWidth :: ViewportBounds -> Number
boundsWidth b = b.right - b.left

-- | Get height
boundsHeight :: ViewportBounds -> Number
boundsHeight b = b.bottom - b.top

-- | Get center point
boundsCenter :: ViewportBounds -> { x :: Number, y :: Number }
boundsCenter b =
  { x: (b.left + b.right) / 2.0
  , y: (b.top + b.bottom) / 2.0
  }

-- | Check if point is within bounds
containsPoint :: Number -> Number -> ViewportBounds -> Boolean
containsPoint x y b =
  x >= b.left && x <= b.right && y >= b.top && y <= b.bottom

-- | Check if two bounds intersect
boundsIntersect :: ViewportBounds -> ViewportBounds -> Boolean
boundsIntersect a b =
  a.left <= b.right && a.right >= b.left &&
  a.top <= b.bottom && a.bottom >= b.top

-- | Expand bounds by margin
expandBounds :: Number -> ViewportBounds -> ViewportBounds
expandBounds margin b =
  { left: b.left - margin
  , top: b.top - margin
  , right: b.right + margin
  , bottom: b.bottom + margin
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // zoom presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom to fit content (placeholder, actual value computed)
zoomFit :: ViewportZoom
zoomFit = ViewportZoom 1.0

-- | 25% zoom
zoom25 :: ViewportZoom
zoom25 = ViewportZoom 0.25

-- | 50% zoom
zoom50 :: ViewportZoom
zoom50 = ViewportZoom 0.5

-- | 100% zoom (default)
zoom100 :: ViewportZoom
zoom100 = ViewportZoom 1.0

-- | 200% zoom
zoom200 :: ViewportZoom
zoom200 = ViewportZoom 2.0

-- | 400% zoom
zoom400 :: ViewportZoom
zoom400 = ViewportZoom 4.0
