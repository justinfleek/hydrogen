-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // hit test
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Hit testing operations for canvas selection.
-- |
-- | ## Hit Testing Philosophy
-- |
-- | Hit testing is hierarchical:
-- | 1. Check handles first (if selection exists)
-- | 2. Check objects from front to back (highest zIndex first)
-- | 3. Return first hit, or Nothing
-- |
-- | ## Coordinate System
-- |
-- | All hit testing operates in canvas space. Screen coordinates must be
-- | converted using viewport transform before testing.
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject, CanvasObjectId)
-- | - Selection.Types (LassoPath)
-- | - Selection.Internal (isTestable, sortByZIndexDesc, findFirstHit)
-- | - Selection.Lasso (lassoIntersectsRect)

module Hydrogen.Element.Compound.Canvas.Selection.HitTest
  ( -- * Point Hit Test
    hitTestPoint
    
  -- * Rectangle Hit Test
  , hitTestRect
  
  -- * Lasso Hit Test
  , hitTestLasso
  
  -- * Object Tests
  , objectContainsPoint
  , objectIntersectsRect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (&&)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , ($)
  )

import Data.Array (filter)
import Data.Functor (map)
import Data.Maybe (Maybe)

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Schema.Gestural.Selection as GSelection
import Hydrogen.Element.Compound.Canvas.Selection.Types (LassoPath)
import Hydrogen.Element.Compound.Canvas.Selection.Internal
  ( isTestable
  , sortByZIndexDesc
  , findFirstHit
  )
import Hydrogen.Element.Compound.Canvas.Selection.Lasso (lassoIntersectsRect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // point hit test
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hit test a point against objects.
-- |
-- | Tests objects from front to back (highest zIndex first).
-- | Returns the first object whose bounds contain the point.
-- |
-- | Does not test locked or invisible objects unless specified.
hitTestPoint :: { x :: Number, y :: Number }
             -> Array Types.CanvasObject
             -> { testLocked :: Boolean, testInvisible :: Boolean }
             -> Maybe Types.CanvasObjectId
hitTestPoint point objects opts =
  findFirstHit point $ sortByZIndexDesc $ filter (isTestable opts) objects

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rectangle hit test
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hit test a rectangle against objects.
-- |
-- | Returns all objects that intersect with the rectangle.
hitTestRect :: GSelection.SelectionRect
            -> Array Types.CanvasObject
            -> { testLocked :: Boolean, testInvisible :: Boolean }
            -> Array Types.CanvasObjectId
hitTestRect rect objects opts =
  let
    testable = filter (isTestable opts) objects
    hits = filter (objectIntersectsRect rect) testable
  in map Types.objectId hits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lasso hit test
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hit test a lasso path against objects.
-- |
-- | Returns all objects that intersect with the lasso polygon.
hitTestLasso :: LassoPath
             -> Array Types.CanvasObject
             -> { testLocked :: Boolean, testInvisible :: Boolean }
             -> Array Types.CanvasObjectId
hitTestLasso lasso objects opts =
  let
    testable = filter (isTestable opts) objects
    hits = filter (objectIntersectsLasso lasso) testable
  in map Types.objectId hits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // object tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if object contains a point.
objectContainsPoint :: { x :: Number, y :: Number } -> Types.CanvasObject -> Boolean
objectContainsPoint point obj =
  let bounds = Types.objectBounds obj
  in point.x >= bounds.x && point.x <= bounds.x + bounds.width
     && point.y >= bounds.y && point.y <= bounds.y + bounds.height

-- | Check if object intersects a rectangle.
objectIntersectsRect :: GSelection.SelectionRect -> Types.CanvasObject -> Boolean
objectIntersectsRect rect obj =
  let bounds = Types.objectBounds obj
  in rect.x < bounds.x + bounds.width && rect.x + rect.width > bounds.x
     && rect.y < bounds.y + bounds.height && rect.y + rect.height > bounds.y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if object intersects lasso.
objectIntersectsLasso :: LassoPath -> Types.CanvasObject -> Boolean
objectIntersectsLasso lasso obj =
  let bounds = Types.objectBounds obj
      rect = GSelection.selectionRect bounds.x bounds.y bounds.width bounds.height
  in lassoIntersectsRect rect lasso
