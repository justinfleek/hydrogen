-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // element // compound // canvas // state // tools
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Tools — Tool management operations.
-- |
-- | ## Contents
-- |
-- | - Tool operations: getTool, setTool, previousTool
-- | - Spacebar pan toggle
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasTool)
-- | - State.Core (CanvasState type)

module Hydrogen.Element.Compound.Canvas.State.Tools
  ( -- * Tool Operations
    getTool
  , setTool
  , previousTool
  , toggleSpacebarPan
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  , (&&)
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

-- Canvas-specific types
import Hydrogen.Element.Compound.Canvas.Types as Types

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tool operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current tool.
getTool :: CanvasState -> Types.CanvasTool
getTool state = state.currentTool

-- | Set current tool.
setTool :: Types.CanvasTool -> CanvasState -> CanvasState
setTool tool state = state 
  { currentTool = tool
  , previousTool = Just state.currentTool
  }

-- | Revert to previous tool.
previousTool :: CanvasState -> CanvasState
previousTool state = case state.previousTool of
  Nothing -> state
  Just prev -> state { currentTool = prev, previousTool = Nothing }

-- | Toggle spacebar pan mode.
toggleSpacebarPan :: Boolean -> CanvasState -> CanvasState
toggleSpacebarPan held state =
  if held && not state.spacebarHeld
    then state 
      { spacebarHeld = true
      , previousTool = Just state.currentTool
      , currentTool = Types.ToolPan
      }
    else if not held && state.spacebarHeld
      then state
        { spacebarHeld = false
        , currentTool = fromMaybe Types.ToolSelect state.previousTool
        , previousTool = Nothing
        }
      else state
