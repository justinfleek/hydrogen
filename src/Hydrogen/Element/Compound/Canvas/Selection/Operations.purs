-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // selection // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | High-level selection operations.
-- |
-- | ## Selection Methods
-- |
-- | Professional design tools provide multiple selection methods:
-- |
-- | 1. **Click selection**: Select topmost object at point
-- | 2. **Marquee selection**: Select objects in rectangle
-- | 3. **Lasso selection**: Select objects in freeform polygon
-- | 4. **Multi-select**: Select all objects at point (stacked)
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject, CanvasObjectId)
-- | - Selection.Types (LassoPath)
-- | - Selection.HitTest (hitTestPoint, hitTestRect, hitTestLasso, objectContainsPoint)

module Hydrogen.Element.Compound.Canvas.Selection.Operations
  ( -- * Rectangle Selection
    selectObjectsInRect
    
  -- * Lasso Selection
  , selectObjectsInLasso
  
  -- * Point Selection
  , selectTopObjectAtPoint
  , selectAllObjectsAtPoint
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (<)
  , not
  )

import Data.Array (filter)
import Data.Functor (map)
import Data.Maybe (Maybe)

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Schema.Gestural.Selection as GSelection
import Hydrogen.Element.Compound.Canvas.Selection.Types (LassoPath)
import Hydrogen.Element.Compound.Canvas.Selection.HitTest
  ( hitTestPoint
  , hitTestRect
  , hitTestLasso
  , objectContainsPoint
  )
import Hydrogen.Element.Compound.Canvas.Selection.Internal (isTestable)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // rectangle selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select all objects within a rectangle.
selectObjectsInRect :: GSelection.SelectionRect
                    -> Array Types.CanvasObject
                    -> Array Types.CanvasObjectId
selectObjectsInRect rect objects =
  hitTestRect rect objects { testLocked: notYes, testInvisible: notYes }
  where
    yes = 1 < 2
    notYes = not yes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // lasso selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select all objects within a lasso path.
selectObjectsInLasso :: LassoPath
                     -> Array Types.CanvasObject
                     -> Array Types.CanvasObjectId
selectObjectsInLasso lasso objects =
  hitTestLasso lasso objects { testLocked: notYes, testInvisible: notYes }
  where
    yes = 1 < 2
    notYes = not yes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select the topmost object at a point.
selectTopObjectAtPoint :: { x :: Number, y :: Number }
                       -> Array Types.CanvasObject
                       -> Maybe Types.CanvasObjectId
selectTopObjectAtPoint point objects =
  hitTestPoint point objects { testLocked: notYes, testInvisible: notYes }
  where
    yes = 1 < 2
    notYes = not yes

-- | Select all objects at a point (for stacked objects).
selectAllObjectsAtPoint :: { x :: Number, y :: Number }
                        -> Array Types.CanvasObject
                        -> Array Types.CanvasObjectId
selectAllObjectsAtPoint point objects =
  let 
    yes = 1 < 2
    notYes = not yes
    testable = filter (isTestable { testLocked: notYes, testInvisible: notYes }) objects
    hits = filter (objectContainsPoint point) testable
  in map Types.objectId hits
