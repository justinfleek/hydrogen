-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // state // gestures
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Gestures — Gesture state management.
-- |
-- | ## Contents
-- |
-- | - Gesture state operations
-- | - Pointer state operations
-- | - Drag state operations
-- | - Touch state operations
-- |
-- | ## Dependencies
-- |
-- | - Schema.Gestural.* (gesture types)
-- | - State.Core (CanvasState type)

module Hydrogen.Element.Compound.Canvas.State.Gestures
  ( -- * Gesture Operations
    getGestureState
  , updateGestureState
  , getPointerState
  , updatePointerState
  , getDragState
  , updateDragState
  , getTouchState
  , updateTouchState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Gesture states from Schema
import Hydrogen.Schema.Gestural.Gesture as Gesture
import Hydrogen.Schema.Gestural.Pointer as Pointer
import Hydrogen.Schema.Gestural.DragDrop as DragDrop
import Hydrogen.Schema.Gestural.Touch as Touch

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // gesture operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get gesture state.
getGestureState :: CanvasState -> Gesture.GestureState
getGestureState state = state.gestureState

-- | Update gesture state.
updateGestureState :: Gesture.GestureState -> CanvasState -> CanvasState
updateGestureState gs state = state { gestureState = gs }

-- | Get pointer state.
getPointerState :: CanvasState -> Pointer.PointerState
getPointerState state = state.pointerState

-- | Update pointer state.
updatePointerState :: Pointer.PointerState -> CanvasState -> CanvasState
updatePointerState ps state = state { pointerState = ps }

-- | Get drag state.
getDragState :: CanvasState -> DragDrop.DragState
getDragState state = state.dragState

-- | Update drag state.
updateDragState :: DragDrop.DragState -> CanvasState -> CanvasState
updateDragState ds state = state { dragState = ds }

-- | Get touch state.
getTouchState :: CanvasState -> Touch.TouchState
getTouchState state = state.touchState

-- | Update touch state.
updateTouchState :: Touch.TouchState -> CanvasState -> CanvasState
updateTouchState ts state = state { touchState = ts }
