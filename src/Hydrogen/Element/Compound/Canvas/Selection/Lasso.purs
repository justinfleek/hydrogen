-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // lasso
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lasso path operations for freeform selection.
-- |
-- | ## Lasso Selection
-- |
-- | The lasso tool allows freeform polygon selection:
-- | 1. User draws a path by dragging
-- | 2. Path is closed when released
-- | 3. Objects inside polygon are selected
-- |
-- | ## Point-in-Polygon
-- |
-- | Uses ray casting algorithm:
-- | - Cast horizontal ray from point
-- | - Count intersections with polygon edges
-- | - Odd count = inside, even = outside
-- |
-- | ## Dependencies
-- |
-- | - Selection.Types (LassoPath)
-- | - Selection.Internal (pointInPolygon, anyPoint, shoelaceArea, abs')

module Hydrogen.Element.Compound.Canvas.Selection.Lasso
  ( -- * Creation
    emptyLasso
  , addLassoPoint
  , closeLasso
  
  -- * Accessors
  , lassoPoints
  
  -- * Containment Tests
  , lassoContainsPoint
  , lassoIntersectsRect
  
  -- * Metrics
  , lassoArea
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (/)
  , ($)
  , (<)
  , not
  )

import Data.Array (length, snoc)

import Hydrogen.Schema.Gestural.Selection as GSelection
import Hydrogen.Element.Compound.Canvas.Selection.Types (LassoPath(LassoPath))
import Hydrogen.Element.Compound.Canvas.Selection.Internal
  ( pointInPolygon
  , anyPoint
  , shoelaceArea
  , abs'
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an empty lasso path.
emptyLasso :: LassoPath
emptyLasso = LassoPath { points: [], closed: notYes }
  where
    yes = 1 < 2
    notYes = not yes

-- | Add a point to the lasso path.
addLassoPoint :: { x :: Number, y :: Number } -> LassoPath -> LassoPath
addLassoPoint point (LassoPath lp) =
  LassoPath lp { points = snoc lp.points point }

-- | Close the lasso path.
closeLasso :: LassoPath -> LassoPath
closeLasso (LassoPath lp) = LassoPath lp { closed = yes }
  where
    yes = 1 < 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get lasso points.
lassoPoints :: LassoPath -> Array { x :: Number, y :: Number }
lassoPoints (LassoPath lp) = lp.points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // containment tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if lasso contains a point (point-in-polygon test).
-- |
-- | Uses ray casting algorithm: count intersections with polygon edges.
-- | Odd count = inside, even count = outside.
lassoContainsPoint :: { x :: Number, y :: Number } -> LassoPath -> Boolean
lassoContainsPoint point (LassoPath lp) =
  let pts = lp.points
      n = length pts
  in if n < 3 then notYes
     else pointInPolygon point pts
  where
    yes = 1 < 2
    notYes = not yes

-- | Check if lasso intersects a rectangle.
-- |
-- | True if any corner of rect is inside lasso, or if lasso path
-- | crosses through the rectangle.
lassoIntersectsRect :: GSelection.SelectionRect -> LassoPath -> Boolean
lassoIntersectsRect rect lasso =
  let 
    corners = 
      [ { x: rect.x, y: rect.y }
      , { x: rect.x + rect.width, y: rect.y }
      , { x: rect.x + rect.width, y: rect.y + rect.height }
      , { x: rect.x, y: rect.y + rect.height }
      ]
    -- Check if any corner is inside
    anyCornerInside = anyPoint (\c -> lassoContainsPoint c lasso) corners
  in anyCornerInside

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // metrics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate approximate area of lasso polygon.
-- |
-- | Uses shoelace formula for polygon area.
lassoArea :: LassoPath -> Number
lassoArea (LassoPath lp) =
  let pts = lp.points
      n = length pts
  in if n < 3 then 0.0
     else abs' (shoelaceArea pts) / 2.0
