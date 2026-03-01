-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // element // compound // canvas // state // keyboard
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas State Keyboard — Keyboard state management.
-- |
-- | ## Contents
-- |
-- | - Keyboard state operations
-- | - Modifier key queries (Ctrl, Alt, Shift, Meta)
-- | - Last pressed key tracking
-- |
-- | ## Dependencies
-- |
-- | - Schema.Gestural.Keyboard (KeyboardState, KeyCode)
-- | - State.Core (CanvasState type)

module Hydrogen.Element.Compound.Canvas.State.Keyboard
  ( -- * Keyboard State
    getKeyboardState
  , updateKeyboardState
  , isCtrlHeld
  , isAltHeld
  , isShiftHeld
  , isMetaHeld
  , hasAnyModifier
  , lastPressedKey
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Nothing, Just))

-- Keyboard state from Schema
import Hydrogen.Schema.Gestural.Keyboard as Keyboard

-- Local imports
import Hydrogen.Element.Compound.Canvas.State.Core (CanvasState)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // keyboard state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get keyboard state.
getKeyboardState :: CanvasState -> Keyboard.KeyboardState
getKeyboardState state = state.keyboardState

-- | Update keyboard state.
updateKeyboardState :: Keyboard.KeyboardState -> CanvasState -> CanvasState
updateKeyboardState ks state = state { keyboardState = ks }

-- | Check if Ctrl is held.
isCtrlHeld :: CanvasState -> Boolean
isCtrlHeld state = (Keyboard.stateModifiers state.keyboardState).ctrl

-- | Check if Alt is held.
isAltHeld :: CanvasState -> Boolean
isAltHeld state = (Keyboard.stateModifiers state.keyboardState).alt

-- | Check if Shift is held.
isShiftHeld :: CanvasState -> Boolean
isShiftHeld state = (Keyboard.stateModifiers state.keyboardState).shift

-- | Check if Meta (Cmd on Mac, Win on Windows) is held.
isMetaHeld :: CanvasState -> Boolean
isMetaHeld state = (Keyboard.stateModifiers state.keyboardState).meta

-- | Check if any modifier is held.
hasAnyModifier :: CanvasState -> Boolean
hasAnyModifier state = Keyboard.hasActiveModifiers state.keyboardState

-- | Get the last pressed key code (if any).
lastPressedKey :: CanvasState -> Maybe Keyboard.KeyCode
lastPressedKey state = 
  case Keyboard.stateLastEvent state.keyboardState of
    Nothing -> Nothing
    Just event -> Just (Keyboard.eventCode event)
