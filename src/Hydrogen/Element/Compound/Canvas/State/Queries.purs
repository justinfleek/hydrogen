-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // compound // canvas // state // queries
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Queries — Derived state and query functions.
-- |
-- | ## Contents
-- |
-- | - Visibility queries (visibleObjects, isObjectVisible)
-- | - Coordinate conversion (screenToCanvas, canvasToScreen)
-- | - Selection queries (hasSelection, selectionCount)
-- | - Zoom queries
-- | - Debug info
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (viewport operations)
-- | - Canvas.Types (object operations)
-- | - State.Core (CanvasState type)
-- | - State.Helpers (helper functions)

module Hydrogen.Element.Compound.Canvas.State.Queries
  ( -- * Derived State
    visibleObjects
  , isObjectVisible
  , screenToCanvas
  , canvasToScreen
  
  -- * State Queries
  , hasSelection
  , selectionCount
  , objectCount
  , undoStackDepth
  , redoStackDepth
  , objectAtIndex
  , currentZoomPercent
  , isAtMinZoom
  , isAtMaxZoom
  , isZoomInRange
  , stateDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , (>=)
  , (<=)
  , (>)
  , (&&)
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  )

import Data.Array (length, filter, index)
import Data.Maybe (Maybe(Just, Nothing))

-- Viewport state from Schema
import Hydrogen.Schema.Graph.Viewport as VP

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)
import Hydrogen.Element.Compound.Canvas.State.Helpers (findObject, objectInViewportBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // derived state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get objects visible in current viewport.
visibleObjects :: CanvasState -> Array Types.CanvasObject
visibleObjects state =
  let bounds = VP.viewportBoundsAt state.viewport
  in filter (objectInViewportBounds bounds) state.objects

-- | Check if a specific object is visible.
isObjectVisible :: Types.CanvasObjectId -> CanvasState -> Boolean
isObjectVisible objId state =
  case findObject objId state.objects of
    Nothing -> false
    Just obj -> 
      let bounds = VP.viewportBoundsAt state.viewport
      in objectInViewportBounds bounds obj

-- | Convert screen coordinates to canvas coordinates.
screenToCanvas :: Number -> Number -> CanvasState -> { x :: Number, y :: Number }
screenToCanvas screenX screenY state =
  let 
    zoom = VP.zoomLevel (VP.viewportZoomLevel state.viewport)
    pan = VP.viewportPan state.viewport
  in
    { x: (screenX / zoom) + pan.x
    , y: (screenY / zoom) + pan.y
    }

-- | Convert canvas coordinates to screen coordinates.
canvasToScreen :: Number -> Number -> CanvasState -> { x :: Number, y :: Number }
canvasToScreen canvasX canvasY state =
  let 
    zoom = VP.zoomLevel (VP.viewportZoomLevel state.viewport)
    pan = VP.viewportPan state.viewport
  in
    { x: (canvasX - pan.x) * zoom
    , y: (canvasY - pan.y) * zoom
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // state queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if anything is selected.
hasSelection :: CanvasState -> Boolean
hasSelection state = Types.selectionCount state.selection > 0

-- | Get selection count (re-exported for convenience).
selectionCount :: CanvasState -> Int
selectionCount state = Types.selectionCount state.selection

-- | Get current zoom as percentage.
currentZoomPercent :: CanvasState -> Number
currentZoomPercent state = VP.zoomPercentage (VP.viewportZoomLevel state.viewport)

-- | Is at minimum zoom?
isAtMinZoom :: CanvasState -> Boolean
isAtMinZoom state = VP.isMinZoom (VP.viewportZoomLevel state.viewport)

-- | Is at maximum zoom?
isAtMaxZoom :: CanvasState -> Boolean
isAtMaxZoom state = VP.isMaxZoom (VP.viewportZoomLevel state.viewport)

-- | Get total number of objects on canvas.
objectCount :: CanvasState -> Int
objectCount state = length state.objects

-- | Get undo stack depth (for UI display).
undoStackDepth :: CanvasState -> Int
undoStackDepth state = length state.undoStack

-- | Get redo stack depth (for UI display).
redoStackDepth :: CanvasState -> Int
redoStackDepth state = length state.redoStack

-- | Get object at specific index in the objects array.
-- |
-- | Index 0 is the first object. Returns Nothing if out of bounds.
objectAtIndex :: Int -> CanvasState -> Maybe Types.CanvasObject
objectAtIndex idx state = index state.objects idx

-- | Check if zoom percentage is within a specific range.
-- |
-- | Useful for UI state (e.g., showing different controls at different zoom levels).
isZoomInRange :: Number -> Number -> CanvasState -> Boolean
isZoomInRange minPercent maxPercent state =
  let zoomPercent = currentZoomPercent state
  in zoomPercent >= minPercent && zoomPercent <= maxPercent

-- | Get debug info about canvas state.
-- |
-- | Returns a human-readable string summarizing the current state.
-- | Useful for development and debugging.
stateDebugInfo :: CanvasState -> String
stateDebugInfo state =
  "Canvas[" <> show (objectCount state) <> " objects, " 
  <> "zoom: " <> show (currentZoomPercent state) <> "%, "
  <> "selection: " <> show (selectionCount state) <> ", "
  <> "undo: " <> show (undoStackDepth state) <> ", "
  <> "redo: " <> show (redoStackDepth state) <> ", "
  <> "mode: " <> show state.interactionMode <> ", "
  <> "tool: " <> (show $ state.currentTool) <> "]"
