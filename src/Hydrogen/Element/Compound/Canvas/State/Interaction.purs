-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // element // compound // canvas // state // interaction
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Interaction — Interaction mode and hover state.
-- |
-- | ## Contents
-- |
-- | - Interaction mode queries
-- | - Hover state operations
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObjectId)
-- | - State.Core (CanvasState, InteractionMode)

module Hydrogen.Element.Compound.Canvas.State.Interaction
  ( -- * Interaction State
    getInteractionMode
  , setInteractionMode
  , isIdle
  , isPanning
  , isZooming
  , isSelecting
  , isDragging
  , isDrawing
  
  -- * Hover State
  , getHoveredObject
  , setHoveredObject
  , clearHoveredObject
  , hasHoveredObject
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core 
  ( CanvasState
  , InteractionMode
      ( ModeIdle
      , ModePanning
      , ModeZooming
      , ModeSelecting
      , ModeDragging
      , ModeDrawing
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // interaction queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get interaction mode.
getInteractionMode :: CanvasState -> InteractionMode
getInteractionMode state = state.interactionMode

-- | Set interaction mode.
setInteractionMode :: InteractionMode -> CanvasState -> CanvasState
setInteractionMode mode state = state { interactionMode = mode }

-- | Is canvas idle?
isIdle :: CanvasState -> Boolean
isIdle state = state.interactionMode == ModeIdle

-- | Is panning in progress?
isPanning :: CanvasState -> Boolean
isPanning state = state.interactionMode == ModePanning

-- | Is zooming in progress?
isZooming :: CanvasState -> Boolean
isZooming state = state.interactionMode == ModeZooming

-- | Is selecting in progress?
isSelecting :: CanvasState -> Boolean
isSelecting state = state.interactionMode == ModeSelecting

-- | Is dragging in progress?
isDragging :: CanvasState -> Boolean
isDragging state = state.interactionMode == ModeDragging

-- | Is drawing in progress?
isDrawing :: CanvasState -> Boolean
isDrawing state = state.interactionMode == ModeDrawing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hover state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get currently hovered object.
getHoveredObject :: CanvasState -> Maybe Types.CanvasObjectId
getHoveredObject state = state.hoveredObject

-- | Set hovered object.
setHoveredObject :: Types.CanvasObjectId -> CanvasState -> CanvasState
setHoveredObject objId state = state { hoveredObject = Just objId }

-- | Clear hovered object.
clearHoveredObject :: CanvasState -> CanvasState
clearHoveredObject state = state { hoveredObject = Nothing }

-- | Check if any object is being hovered.
hasHoveredObject :: CanvasState -> Boolean
hasHoveredObject state = isJust state.hoveredObject
