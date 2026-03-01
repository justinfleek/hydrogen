-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // compound // canvas // state // history
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State History — Undo/redo history operations.
-- |
-- | ## Contents
-- |
-- | - History queries (canUndo, canRedo)
-- | - History mutations (pushHistory, undo, redo, clearHistory)
-- |
-- | ## Stack Implementation
-- |
-- | Uses cons (prepend) for O(1) stack operations.
-- | Most recent entry is at the head of the array.
-- |
-- | ## Dependencies
-- |
-- | - State.Core (CanvasState, HistoryEntry)

module Hydrogen.Element.Compound.Canvas.State.History
  ( -- * History Operations
    canUndo
  , canRedo
  , pushHistory
  , undo
  , redo
  , clearHistory
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  )

import Data.Array (null, take, drop, head)
import Data.Array ((:)) as Array
import Data.Maybe (Maybe(Just, Nothing))

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // history operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Can undo?
canUndo :: CanvasState -> Boolean
canUndo state = not (null state.undoStack)

-- | Can redo?
canRedo :: CanvasState -> Boolean
canRedo state = not (null state.redoStack)

-- | Push current state to history.
-- |
-- | Uses cons (prepend) for O(1) stack operations.
-- | Most recent entry is at the head of the array.
pushHistory :: String -> CanvasState -> CanvasState
pushHistory label state =
  let 
    entry = 
      { objects: state.objects
      , selection: state.selection
      , label
      }
    -- Prepend new entry, then take from the beginning to enforce max size
    newUndo = take state.maxHistorySize (Array.(:) entry state.undoStack)
  in state 
    { undoStack = newUndo
    , redoStack = []  -- Clear redo on new action
    }

-- | Undo last action.
-- |
-- | Pops from undo stack (head) and pushes current state to redo stack.
undo :: CanvasState -> CanvasState
undo state = case head state.undoStack of
  Nothing -> state
  Just entry ->
    let 
      currentEntry = 
        { objects: state.objects
        , selection: state.selection
        , label: "Redo point"
        }
    in state
      { objects = entry.objects
      , selection = entry.selection
      , undoStack = dropFirst state.undoStack
      , redoStack = Array.(:) currentEntry state.redoStack
      }

-- | Redo last undone action.
-- |
-- | Pops from redo stack (head) and pushes current state to undo stack.
redo :: CanvasState -> CanvasState
redo state = case head state.redoStack of
  Nothing -> state
  Just entry ->
    let 
      currentEntry = 
        { objects: state.objects
        , selection: state.selection
        , label: "Undo point"
        }
    in state
      { objects = entry.objects
      , selection = entry.selection
      , undoStack = Array.(:) currentEntry state.undoStack
      , redoStack = dropFirst state.redoStack
      }

-- | Clear all history.
clearHistory :: CanvasState -> CanvasState
clearHistory state = state { undoStack = [], redoStack = [] }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop first element (O(n) but semantically correct for stack operations).
-- |
-- | Used by undo/redo stacks where head is most recent.
dropFirst :: forall a. Array a -> Array a
dropFirst arr = drop 1 arr
