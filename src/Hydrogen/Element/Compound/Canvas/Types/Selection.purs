-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // element // compound // canvas // types // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Selection Operations — Selection bounds calculation.
-- |
-- | ## Scope
-- |
-- | This module provides selection operations that depend on CanvasObject:
-- |
-- | - **selectionBounds**: Calculate bounding box of selected objects
-- |
-- | ## Design Note
-- |
-- | This is split from Core because it depends on the Object module.
-- | Core provides the basic selection state; this adds object-dependent operations.

module Hydrogen.Element.Compound.Canvas.Types.Selection
  ( selectionBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  , (+)
  , (-) 
  , negate
  , max
  , min
  )

import Data.Array (length, filter, elem)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Foldable (foldl)

import Hydrogen.Element.Compound.Canvas.Types.Core (SelectionState)
import Hydrogen.Element.Compound.Canvas.Types.Object (CanvasObject, objectId, objectBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate bounding box of selection.
-- |
-- | Returns Nothing if selection is empty or objects can't be found.
selectionBounds :: SelectionState -> Array CanvasObject -> Maybe { x :: Number, y :: Number, width :: Number, height :: Number }
selectionBounds state objects =
  let 
    selectedObjects = filter (\obj -> elem (objectId obj) state.selectedIds) objects
  in
    if length selectedObjects == 0
      then Nothing
      else Just (calculateBounds selectedObjects)
  where
    calculateBounds :: Array CanvasObject -> { x :: Number, y :: Number, width :: Number, height :: Number }
    calculateBounds objs =
      let
        initial = { minX: infinity, minY: infinity, maxX: negInfinity, maxY: negInfinity }
        result = foldl accumulateBounds initial objs
      in
        { x: result.minX
        , y: result.minY
        , width: result.maxX - result.minX
        , height: result.maxY - result.minY
        }
    
    accumulateBounds :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number } 
                     -> CanvasObject 
                     -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
    accumulateBounds acc obj =
      let bounds = objectBounds obj
      in
        { minX: min acc.minX bounds.x
        , minY: min acc.minY bounds.y
        , maxX: max acc.maxX (bounds.x + bounds.width)
        , maxY: max acc.maxY (bounds.y + bounds.height)
        }
    
    infinity :: Number
    infinity = 1.0e308
    
    negInfinity :: Number
    negInfinity = -1.0e308
