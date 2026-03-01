-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // state // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Viewport — Viewport manipulation operations.
-- |
-- | ## Contents
-- |
-- | - Pan operations: panBy, panTo
-- | - Zoom operations: zoomIn, zoomOut, zoomTo, zoomToFit, zoomToSelection
-- | - Viewport getters/setters
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (viewport state)
-- | - State.Core (CanvasState type)
-- | - State.Helpers (calculateObjectsBounds)

module Hydrogen.Element.Compound.Canvas.State.Viewport
  ( -- * Viewport Operations
    getViewport
  , setViewport
  , panBy
  , panTo
  , zoomIn
  , zoomOut
  , zoomTo
  , zoomToFit
  , zoomToSelection
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Viewport state from Schema
import Hydrogen.Schema.Graph.Viewport as VP

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)
import Hydrogen.Element.Compound.Canvas.State.Helpers (calculateObjectsBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current viewport state.
getViewport :: CanvasState -> VP.ViewportState
getViewport state = state.viewport

-- | Set viewport state.
setViewport :: VP.ViewportState -> CanvasState -> CanvasState
setViewport vp state = state { viewport = vp }

-- | Pan by delta (in screen pixels).
panBy :: Number -> Number -> CanvasState -> CanvasState
panBy dx dy state = state { viewport = VP.applyPan dx dy state.viewport }

-- | Pan to absolute position (in canvas coordinates).
panTo :: Number -> Number -> CanvasState -> CanvasState
panTo x y state = state { viewport = VP.setPan (VP.panTo x y) state.viewport }

-- | Zoom in by one step.
zoomIn :: CanvasState -> CanvasState
zoomIn state = state { viewport = VP.applyZoom (VP.zoomIn (VP.viewportZoomLevel state.viewport)) state.viewport }

-- | Zoom out by one step.
zoomOut :: CanvasState -> CanvasState
zoomOut state = state { viewport = VP.applyZoom (VP.zoomOut (VP.viewportZoomLevel state.viewport)) state.viewport }

-- | Zoom to specific level.
zoomTo :: VP.ViewportZoom -> CanvasState -> CanvasState
zoomTo zoom state = state { viewport = VP.applyZoom zoom state.viewport }

-- | Zoom to fit all objects in view.
zoomToFit :: CanvasState -> CanvasState
zoomToFit state =
  case calculateObjectsBounds state.objects of
    Nothing -> state  -- No objects, keep current
    Just bounds -> state { viewport = VP.fitContent bounds state.viewport }

-- | Zoom to fit selection in view.
zoomToSelection :: CanvasState -> CanvasState
zoomToSelection state =
  case Types.selectionBounds state.selection state.objects of
    Nothing -> state  -- No selection
    Just bounds -> 
      let vpBounds = 
            { left: bounds.x
            , top: bounds.y
            , right: bounds.x + bounds.width
            , bottom: bounds.y + bounds.height
            }
      in state { viewport = VP.fitContent vpBounds state.viewport }
