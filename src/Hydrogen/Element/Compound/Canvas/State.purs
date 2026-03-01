-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // compound // canvas // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State — Complete state management for infinite canvas.
-- |
-- | ## Design Philosophy
-- |
-- | Canvas state is a **pure data structure** that combines:
-- |
-- | - **Viewport state**: Pan, zoom, visible bounds (from Schema.Graph.Viewport)
-- | - **Gesture state**: Active gestures, touch tracking (from Schema.Gestural)
-- | - **Selection state**: Selected objects, anchor point
-- | - **Tool state**: Current tool, tool-specific state
-- | - **Interaction state**: Hover, drag, focus
-- | - **History state**: Undo/redo stack
-- |
-- | ## Event-Driven Model
-- |
-- | Canvas does NOT poll or animate continuously. State changes via:
-- |
-- | 1. User input (pointer, touch, keyboard)
-- | 2. External data changes
-- | 3. Timer/animation completion
-- |
-- | Each event produces a new CanvasState. The runtime diffs and patches.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - State.Core: Types and constructors
-- | - State.Viewport: Pan/zoom operations
-- | - State.Tools: Tool management
-- | - State.Selection: Selection operations
-- | - State.Objects: Object/layer management
-- | - State.Gestures: Gesture state tracking
-- | - State.Interaction: Interaction mode and hover
-- | - State.Keyboard: Keyboard state
-- | - State.History: Undo/redo operations
-- | - State.Queries: Derived state and queries
-- | - State.Helpers: Internal utilities
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (viewport state)
-- | - Schema.Gestural.* (all gesture types)
-- | - Composition.Trigger (event system)
-- | - Canvas.Types (canvas-specific types)

module Hydrogen.Element.Compound.Canvas.State
  ( module Core
  , module Viewport
  , module Tools
  , module Selection
  , module Objects
  , module Gestures
  , module Interaction
  , module Keyboard
  , module History
  , module Queries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Core types and constructors
import Hydrogen.Element.Compound.Canvas.State.Core
  ( CanvasState
  , HistoryEntry
  , InteractionMode
      ( ModeIdle
      , ModePanning
      , ModeZooming
      , ModeSelecting
      , ModeDragging
      , ModeDrawing
      , ModeEditing
      , ModeContextMenu
      , ModeCustom
      )
  , initialCanvasState
  , resetCanvasState
  ) as Core

-- Viewport operations
import Hydrogen.Element.Compound.Canvas.State.Viewport
  ( getViewport
  , setViewport
  , panBy
  , panTo
  , zoomIn
  , zoomOut
  , zoomTo
  , zoomToFit
  , zoomToSelection
  ) as Viewport

-- Tool operations
import Hydrogen.Element.Compound.Canvas.State.Tools
  ( getTool
  , setTool
  , previousTool
  , toggleSpacebarPan
  ) as Tools

-- Selection operations
import Hydrogen.Element.Compound.Canvas.State.Selection
  ( getSelection
  , setSelection
  , selectObject
  , deselectObject
  , selectAll
  , deselectAll
  , toggleSelection
  , selectInRect
  ) as Selection

-- Object and config operations
import Hydrogen.Element.Compound.Canvas.State.Objects
  ( getConfig
  , getGridConfig
  , getGuides
  , addObject
  , removeObject
  , updateObject
  , getObjects
  , setObjectZIndex
  , bringToFront
  , sendToBack
  , moveLayerUp
  , moveLayerDown
  ) as Objects

-- Gesture operations
import Hydrogen.Element.Compound.Canvas.State.Gestures
  ( getGestureState
  , updateGestureState
  , getPointerState
  , updatePointerState
  , getDragState
  , updateDragState
  , getTouchState
  , updateTouchState
  ) as Gestures

-- Interaction operations
import Hydrogen.Element.Compound.Canvas.State.Interaction
  ( getInteractionMode
  , setInteractionMode
  , isIdle
  , isPanning
  , isZooming
  , isSelecting
  , isDragging
  , isDrawing
  , getHoveredObject
  , setHoveredObject
  , clearHoveredObject
  , hasHoveredObject
  ) as Interaction

-- Keyboard operations
import Hydrogen.Element.Compound.Canvas.State.Keyboard
  ( getKeyboardState
  , updateKeyboardState
  , isCtrlHeld
  , isAltHeld
  , isShiftHeld
  , isMetaHeld
  , hasAnyModifier
  , lastPressedKey
  ) as Keyboard

-- History operations
import Hydrogen.Element.Compound.Canvas.State.History
  ( canUndo
  , canRedo
  , pushHistory
  , undo
  , redo
  , clearHistory
  ) as History

-- Query operations
import Hydrogen.Element.Compound.Canvas.State.Queries
  ( visibleObjects
  , isObjectVisible
  , screenToCanvas
  , canvasToScreen
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
  ) as Queries
