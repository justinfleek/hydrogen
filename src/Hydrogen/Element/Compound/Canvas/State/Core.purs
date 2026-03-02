-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // compound // canvas // state // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Core — Type definitions and constructors.
-- |
-- | ## Contents
-- |
-- | - InteractionMode: Current interaction mode
-- | - HistoryEntry: Undo/redo history entry
-- | - CanvasState: Complete canvas state record
-- | - Constructors: initialCanvasState, resetCanvasState
-- |
-- | ## Dependencies
-- |
-- | - Schema.Graph.Viewport (viewport state)
-- | - Schema.Gestural.* (gesture types)
-- | - Canvas.Types (canvas-specific types)

module Hydrogen.Element.Compound.Canvas.State.Core
  ( -- * Interaction Mode
    InteractionMode(ModeIdle, ModePanning, ModeZooming, ModeSelecting, ModeDragging, ModeDrawing, ModeEditing, ModeContextMenu, ModeCustom)
    
  -- * History Entry
  , HistoryEntry
  
  -- * Canvas State
  , CanvasState
  
  -- * Constructors
  , initialCanvasState
  , resetCanvasState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))

-- Viewport state from Schema
import Hydrogen.Schema.Graph.Viewport as VP
  
-- Gesture states from Schema
import Hydrogen.Schema.Gestural.Gesture as Gesture
import Hydrogen.Schema.Gestural.Pointer as Pointer
import Hydrogen.Schema.Gestural.DragDrop as DragDrop
import Hydrogen.Schema.Gestural.Touch as Touch
import Hydrogen.Schema.Gestural.Keyboard as Keyboard

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // interaction mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current interaction mode determines how input is interpreted.
data InteractionMode
  = ModeIdle              -- ^ No active interaction
  | ModePanning           -- ^ Viewport pan in progress
  | ModeZooming           -- ^ Zoom gesture in progress
  | ModeSelecting         -- ^ Selection marquee active
  | ModeDragging          -- ^ Object drag in progress
  | ModeDrawing           -- ^ Shape/path drawing active
  | ModeEditing           -- ^ Text/point editing active
  | ModeContextMenu       -- ^ Context menu open
  | ModeCustom String     -- ^ Custom mode for extensions

derive instance eqInteractionMode :: Eq InteractionMode

instance showInteractionMode :: Show InteractionMode where
  show ModeIdle = "idle"
  show ModePanning = "panning"
  show ModeZooming = "zooming"
  show ModeSelecting = "selecting"
  show ModeDragging = "dragging"
  show ModeDrawing = "drawing"
  show ModeEditing = "editing"
  show ModeContextMenu = "context-menu"
  show (ModeCustom name) = "custom:" <> name

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // history entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | History entry for undo/redo.
-- |
-- | Stores enough state to restore canvas to a previous point.
type HistoryEntry =
  { objects :: Array Types.CanvasObject
  , selection :: Types.SelectionState
  , label :: String                    -- Human-readable description
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // canvas state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete canvas state.
-- |
-- | This is the single source of truth for the canvas component.
-- | All operations produce a new CanvasState (immutable).
type CanvasState =
  { -- Identity
    id :: Types.CanvasId
  , config :: Types.CanvasConfig
  , bounds :: Types.CanvasBounds
  
  -- Viewport (from Schema.Graph.Viewport)
  , viewport :: VP.ViewportState
  
  -- Tools
  , currentTool :: Types.CanvasTool
  , previousTool :: Maybe Types.CanvasTool   -- For spacebar-pan toggle
  , spacebarHeld :: Boolean
  
  -- Selection
  , selection :: Types.SelectionState
  
  -- Objects (the actual content)
  , objects :: Array Types.CanvasObject
  
  -- Guides
  , guides :: Array Types.Guide
  
  -- Interaction
  , interactionMode :: InteractionMode
  , hoveredObject :: Maybe Types.CanvasObjectId
  
  -- Gesture states (from Schema.Gestural)
  , gestureState :: Gesture.GestureState
  , pointerState :: Pointer.PointerState
  , dragState :: DragDrop.DragState
  , touchState :: Touch.TouchState
  , keyboardState :: Keyboard.KeyboardState
  
  -- History
  , undoStack :: Array HistoryEntry
  , redoStack :: Array HistoryEntry
  , maxHistorySize :: Int
  
  -- Performance
  , lastRenderTime :: Number           -- For FPS tracking
  , frameCount :: Int
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create initial canvas state.
initialCanvasState :: Types.CanvasId -> Number -> Number -> CanvasState
initialCanvasState canvasId width height =
  { id: canvasId
  , config: Types.defaultCanvasConfig
  , bounds: Types.infiniteBounds
  , viewport: VP.initialViewport width height
  , currentTool: Types.ToolSelect
  , previousTool: Nothing
  , spacebarHeld: false
  , selection: Types.emptySelection
  , objects: []
  , guides: []
  , interactionMode: ModeIdle
  , hoveredObject: Nothing
  , gestureState: Gesture.initialGestureState
  , pointerState: Pointer.defaultPointerState
  , dragState: DragDrop.initialDragState
  , touchState: Touch.noTouches
  , keyboardState: Keyboard.initialKeyboardState
  , undoStack: []
  , redoStack: []
  , maxHistorySize: 100
  , lastRenderTime: 0.0
  , frameCount: 0
  }

-- | Reset canvas to initial state, preserving config.
resetCanvasState :: CanvasState -> CanvasState
resetCanvasState state =
  let initial = initialCanvasState state.id (screenWidth state) (screenHeight state)
  in initial { config = state.config }
  where
    screenWidth s = s.viewport.screenWidth
    screenHeight s = s.viewport.screenHeight
