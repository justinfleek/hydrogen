-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // dimension // bounding-rect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BoundingRect — DOM element measurement type.
-- |
-- | **WHY BOUNDINGRECT?**
-- | BoundingRect represents the result of `getBoundingClientRect()` in pure
-- | PureScript, eliminating the need for JavaScript FFI when working with
-- | DOM element measurements.
-- |
-- | This type captures the complete geometric bounds of an element:
-- | - Position (left, top, right, bottom, x, y)
-- | - Size (width, height)
-- |
-- | **Coordinate System:**
-- | All values are in CSS pixels relative to the viewport.
-- | - Origin (0, 0) is the top-left corner of the viewport
-- | - Y increases downward (standard screen coordinates)
-- | - Values can be negative (element scrolled above/left of viewport)
-- |
-- | **Use Cases:**
-- | - Element positioning and collision detection
-- | - Scroll-based visibility calculations
-- | - Layout measurements for animation
-- | - Intersection observer calculations
-- | - Virtual scroll implementations
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Schema.Dimension.Device (Pixel)
-- |
-- | ## Dependents
-- | - Hydrogen.Schema.Dimension.Intersection (IntersectionEntry)
-- | - Hydrogen.Schema.Dimension.Virtual (VirtualScrollState)
-- | - Component.Tooltip (positioning)
-- | - Component.Dropdown (positioning)

module Hydrogen.Schema.Dimension.BoundingRect
  ( -- * Types
    BoundingRect(BoundingRect)
  
  -- * Constructors
  , boundingRect
  , boundingRectFromRecord
  , boundingRectZero
  
  -- * Accessors
  , left
  , top
  , right
  , bottom
  , x
  , y
  , width
  , height
  , toRecord
  
  -- * Derived Properties
  , center
  , centerX
  , centerY
  , area
  , perimeter
  , aspectRatio
  
  -- * Operations
  , translate
  , scale
  , expand
  , contract
  , intersection
  , union
  
  -- * Predicates
  , isEmpty
  , containsPoint
  , containsRect
  , intersects
  , isInViewport
  
  -- * Conversions
  , toRect
  , fromRect
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel), unwrapPixel)
import Hydrogen.Schema.Dimension.Point2D (Point2D(Point2D))
import Hydrogen.Schema.Dimension.Rect (Rect)
import Hydrogen.Schema.Dimension.Rect as R

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // bounding-rect
-- ═════════════════════════════════════════════════════════════════════════════

-- | BoundingRect represents DOM element bounds in viewport coordinates.
-- |
-- | All measurements are in CSS pixels (Pixel type).
-- | This mirrors the DOMRect interface from getBoundingClientRect().
data BoundingRect = BoundingRect
  { left :: Pixel
  , top :: Pixel
  , right :: Pixel
  , bottom :: Pixel
  , width :: Pixel
  , height :: Pixel
  , x :: Pixel
  , y :: Pixel
  }

derive instance eqBoundingRect :: Eq BoundingRect
derive instance ordBoundingRect :: Ord BoundingRect

instance showBoundingRect :: Show BoundingRect where
  show (BoundingRect r) = 
    "BoundingRect(" <> 
    "x:" <> show r.x <> ", y:" <> show r.y <> 
    ", w:" <> show r.width <> ", h:" <> show r.height <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a BoundingRect from position and size.
-- |
-- | Computes all derived values (right, bottom) from left, top, width, height.
-- |
-- | ```purescript
-- | boundingRect (px 100.0) (px 50.0) (px 200.0) (px 100.0)
-- | -- Creates rect at (100, 50) with size 200×100
-- | ```
boundingRect :: Pixel -> Pixel -> Pixel -> Pixel -> BoundingRect
boundingRect l t w h =
  let 
    lVal = unwrapPixel l
    tVal = unwrapPixel t
    wVal = absNum (unwrapPixel w)
    hVal = absNum (unwrapPixel h)
  in BoundingRect
    { left: Pixel lVal
    , top: Pixel tVal
    , right: Pixel (lVal + wVal)
    , bottom: Pixel (tVal + hVal)
    , width: Pixel wVal
    , height: Pixel hVal
    , x: Pixel lVal
    , y: Pixel tVal
    }

-- | Create from a record matching DOMRect properties.
boundingRectFromRecord 
  :: { left :: Pixel
     , top :: Pixel
     , right :: Pixel
     , bottom :: Pixel
     , width :: Pixel
     , height :: Pixel
     , x :: Pixel
     , y :: Pixel
     }
  -> BoundingRect
boundingRectFromRecord = BoundingRect

-- | Zero-sized BoundingRect at origin.
boundingRectZero :: BoundingRect
boundingRectZero = BoundingRect
  { left: Pixel 0.0
  , top: Pixel 0.0
  , right: Pixel 0.0
  , bottom: Pixel 0.0
  , width: Pixel 0.0
  , height: Pixel 0.0
  , x: Pixel 0.0
  , y: Pixel 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get left edge (x coordinate of left side).
left :: BoundingRect -> Pixel
left (BoundingRect r) = r.left

-- | Get top edge (y coordinate of top side).
top :: BoundingRect -> Pixel
top (BoundingRect r) = r.top

-- | Get right edge (x coordinate of right side).
right :: BoundingRect -> Pixel
right (BoundingRect r) = r.right

-- | Get bottom edge (y coordinate of bottom side).
bottom :: BoundingRect -> Pixel
bottom (BoundingRect r) = r.bottom

-- | Get x coordinate (same as left).
x :: BoundingRect -> Pixel
x (BoundingRect r) = r.x

-- | Get y coordinate (same as top).
y :: BoundingRect -> Pixel
y (BoundingRect r) = r.y

-- | Get width.
width :: BoundingRect -> Pixel
width (BoundingRect r) = r.width

-- | Get height.
height :: BoundingRect -> Pixel
height (BoundingRect r) = r.height

-- | Convert to record.
toRecord 
  :: BoundingRect 
  -> { left :: Pixel
     , top :: Pixel
     , right :: Pixel
     , bottom :: Pixel
     , width :: Pixel
     , height :: Pixel
     , x :: Pixel
     , y :: Pixel
     }
toRecord (BoundingRect r) = r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // derived properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get center point.
center :: BoundingRect -> Point2D
center br = Point2D (centerX br) (centerY br)

-- | Get center X coordinate.
centerX :: BoundingRect -> Number
centerX br = unwrapPixel (left br) + unwrapPixel (width br) / 2.0

-- | Get center Y coordinate.
centerY :: BoundingRect -> Number
centerY br = unwrapPixel (top br) + unwrapPixel (height br) / 2.0

-- | Calculate area in square pixels.
area :: BoundingRect -> Number
area br = unwrapPixel (width br) * unwrapPixel (height br)

-- | Calculate perimeter.
perimeter :: BoundingRect -> Number
perimeter br = 2.0 * (unwrapPixel (width br) + unwrapPixel (height br))

-- | Calculate aspect ratio (width / height).
-- |
-- | Returns 0.0 for zero-height rects.
aspectRatio :: BoundingRect -> Number
aspectRatio br =
  let h = unwrapPixel (height br)
  in if h == 0.0 then 0.0 else unwrapPixel (width br) / h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate rect by dx, dy pixels.
translate :: Pixel -> Pixel -> BoundingRect -> BoundingRect
translate dx dy br =
  boundingRect 
    (Pixel (unwrapPixel (left br) + unwrapPixel dx))
    (Pixel (unwrapPixel (top br) + unwrapPixel dy))
    (width br)
    (height br)

-- | Scale rect from origin by factor.
scale :: Number -> BoundingRect -> BoundingRect
scale factor br =
  boundingRect
    (Pixel (unwrapPixel (left br) * factor))
    (Pixel (unwrapPixel (top br) * factor))
    (Pixel (unwrapPixel (width br) * factor))
    (Pixel (unwrapPixel (height br) * factor))

-- | Expand rect by amount on all sides.
expand :: Pixel -> BoundingRect -> BoundingRect
expand amount br =
  let a = unwrapPixel amount
  in boundingRect
    (Pixel (unwrapPixel (left br) - a))
    (Pixel (unwrapPixel (top br) - a))
    (Pixel (unwrapPixel (width br) + 2.0 * a))
    (Pixel (unwrapPixel (height br) + 2.0 * a))

-- | Contract rect by amount on all sides.
contract :: Pixel -> BoundingRect -> BoundingRect
contract amount br =
  let 
    a = unwrapPixel amount
    newW = maxNum 0.0 (unwrapPixel (width br) - 2.0 * a)
    newH = maxNum 0.0 (unwrapPixel (height br) - 2.0 * a)
  in boundingRect
    (Pixel (unwrapPixel (left br) + a))
    (Pixel (unwrapPixel (top br) + a))
    (Pixel newW)
    (Pixel newH)

-- | Calculate intersection of two BoundingRects.
-- |
-- | Returns Nothing if rects don't overlap.
intersection :: BoundingRect -> BoundingRect -> Maybe BoundingRect
intersection br1 br2 =
  let
    l = maxNum (unwrapPixel (left br1)) (unwrapPixel (left br2))
    t = maxNum (unwrapPixel (top br1)) (unwrapPixel (top br2))
    r = minNum (unwrapPixel (right br1)) (unwrapPixel (right br2))
    b = minNum (unwrapPixel (bottom br1)) (unwrapPixel (bottom br2))
  in if l < r && t < b
    then Just (boundingRect (Pixel l) (Pixel t) (Pixel (r - l)) (Pixel (b - t)))
    else Nothing

-- | Calculate union of two BoundingRects (smallest rect containing both).
union :: BoundingRect -> BoundingRect -> BoundingRect
union br1 br2 =
  let
    l = minNum (unwrapPixel (left br1)) (unwrapPixel (left br2))
    t = minNum (unwrapPixel (top br1)) (unwrapPixel (top br2))
    r = maxNum (unwrapPixel (right br1)) (unwrapPixel (right br2))
    b = maxNum (unwrapPixel (bottom br1)) (unwrapPixel (bottom br2))
  in boundingRect (Pixel l) (Pixel t) (Pixel (r - l)) (Pixel (b - t))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if rect has zero area.
isEmpty :: BoundingRect -> Boolean
isEmpty br = 
  unwrapPixel (width br) == 0.0 && unwrapPixel (height br) == 0.0

-- | Check if rect contains a point (x, y in viewport pixels).
containsPoint :: Number -> Number -> BoundingRect -> Boolean
containsPoint px py br =
  px >= unwrapPixel (left br) && 
  px <= unwrapPixel (right br) &&
  py >= unwrapPixel (top br) && 
  py <= unwrapPixel (bottom br)

-- | Check if this rect fully contains another rect.
containsRect :: BoundingRect -> BoundingRect -> Boolean
containsRect inner outer =
  unwrapPixel (left inner) >= unwrapPixel (left outer) &&
  unwrapPixel (right inner) <= unwrapPixel (right outer) &&
  unwrapPixel (top inner) >= unwrapPixel (top outer) &&
  unwrapPixel (bottom inner) <= unwrapPixel (bottom outer)

-- | Check if two rects intersect.
intersects :: BoundingRect -> BoundingRect -> Boolean
intersects br1 br2 =
  unwrapPixel (left br1) < unwrapPixel (right br2) &&
  unwrapPixel (right br1) > unwrapPixel (left br2) &&
  unwrapPixel (top br1) < unwrapPixel (bottom br2) &&
  unwrapPixel (bottom br1) > unwrapPixel (top br2)

-- | Check if rect is fully within the viewport.
-- |
-- | Requires viewport dimensions.
isInViewport :: Pixel -> Pixel -> BoundingRect -> Boolean
isInViewport viewportWidth viewportHeight br =
  unwrapPixel (left br) >= 0.0 &&
  unwrapPixel (top br) >= 0.0 &&
  unwrapPixel (right br) <= unwrapPixel viewportWidth &&
  unwrapPixel (bottom br) <= unwrapPixel viewportHeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to generic Rect type.
toRect :: BoundingRect -> Rect
toRect br = R.rect 
  (unwrapPixel (left br))
  (unwrapPixel (top br))
  (unwrapPixel (width br))
  (unwrapPixel (height br))

-- | Create BoundingRect from generic Rect type.
fromRect :: Rect -> BoundingRect
fromRect r = boundingRect
  (Pixel (R.x r))
  (Pixel (R.y r))
  (Pixel (R.width r))
  (Pixel (R.height r))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value
absNum :: Number -> Number
absNum n
  | n < 0.0 = 0.0 - n
  | otherwise = n

-- | Maximum of two numbers
maxNum :: Number -> Number -> Number
maxNum a b
  | a >= b = a
  | otherwise = b

-- | Minimum of two numbers
minNum :: Number -> Number -> Number
minNum a b
  | a <= b = a
  | otherwise = b
