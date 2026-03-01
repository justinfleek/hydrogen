-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // element // compound // canvas // state // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Selection — Selection management operations.
-- |
-- | ## Contents
-- |
-- | - Selection getters/setters
-- | - Single/multi selection operations
-- | - Rectangle selection
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (SelectionState, CanvasObjectId)
-- | - State.Core (CanvasState type)
-- | - State.Helpers (objectIntersectsRect, getAllObjectIds)

module Hydrogen.Element.Compound.Canvas.State.Selection
  ( -- * Selection Operations
    getSelection
  , setSelection
  , selectObject
  , deselectObject
  , selectAll
  , deselectAll
  , toggleSelection
  , selectInRect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Array (filter)

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)
import Hydrogen.Element.Compound.Canvas.State.Helpers (objectIntersectsRect, getAllObjectIds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current selection.
getSelection :: CanvasState -> Types.SelectionState
getSelection state = state.selection

-- | Set selection.
setSelection :: Types.SelectionState -> CanvasState -> CanvasState
setSelection sel state = state { selection = sel }

-- | Select a single object.
selectObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
selectObject objId state = state { selection = Types.singleSelection objId }

-- | Deselect a specific object.
deselectObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
deselectObject objId state = state { selection = Types.removeFromSelection objId state.selection }

-- | Select all objects.
selectAll :: CanvasState -> CanvasState
selectAll state = 
  let allIds = getAllObjectIds state.objects
  in state { selection = Types.multiSelection allIds }

-- | Deselect all objects.
deselectAll :: CanvasState -> CanvasState
deselectAll state = state { selection = Types.emptySelection }

-- | Toggle selection of an object.
toggleSelection :: Types.CanvasObjectId -> CanvasState -> CanvasState
toggleSelection objId state =
  if Types.isSelected objId state.selection
    then deselectObject objId state
    else state { selection = Types.addToSelection objId state.selection }

-- | Select all objects within a rectangle (in canvas coordinates).
selectInRect :: { x :: Number, y :: Number, width :: Number, height :: Number } -> CanvasState -> CanvasState
selectInRect rect state =
  let 
    objectsInRect = filter (objectIntersectsRect rect) state.objects
    ids = getAllObjectIds objectsInRect
  in state { selection = Types.multiSelection ids }
