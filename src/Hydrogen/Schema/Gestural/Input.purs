-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // gestural // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Input - Pure bounded input types for keyboard and mouse.
-- |
-- | **Zero JavaScript. Zero browser APIs. Zero side effects.**
-- |
-- | This module provides platform-independent input types that:
-- | - Match the Rust runtime exactly (`runtime/src/core/input.rs`)
-- | - Serialize to binary for cross-language communication
-- | - Use bounded ADTs (no strings, no unbounded values)
-- |
-- | ## Module Structure
-- |
-- | - `Input.ScanCode` — USB HID scan codes (bounded ADT, 72 variants)
-- | - `Input.Modifiers` — Keyboard modifier bitfield (u8)
-- | - `Input.MouseButtons` — Mouse button bitfield (u8)
-- | - `Input.State` — MouseState, KeyboardState, FrameInput
-- | - `Input.Shortcut` — Keyboard shortcuts (ScanCode + Modifiers)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Gestural.Input.ScanCode as SC
-- | import Hydrogen.Schema.Gestural.Input.Modifiers as Mod
-- | import Hydrogen.Schema.Gestural.Input.MouseButtons as MB
-- | import Hydrogen.Schema.Gestural.Input.Shortcut as Shortcut
-- | import Hydrogen.Schema.Gestural.Input.State (KeyboardState, isPressed)
-- |
-- | -- Define a keyboard shortcut
-- | saveShortcut = Shortcut.ctrl SC.S
-- |
-- | -- Check if key is pressed
-- | isSPressed = isPressed SC.S keyboardState
-- |
-- | -- Display shortcut in UI
-- | label = Shortcut.toDisplayString saveShortcut  -- "Ctrl+S"
-- | ```
-- |
-- | Note: Use qualified imports for Modifiers and MouseButtons to avoid
-- | name conflicts (both have `none`, `union`, `contains`, etc.).

module Hydrogen.Schema.Gestural.Input
  ( -- * ScanCode (re-exported)
    module ScanCode
  -- * State Types (re-exported)
  , module State
  ) where

-- ScanCode is safe to re-export fully (unique names)
import Hydrogen.Schema.Gestural.Input.ScanCode
  ( ScanCode
      ( A, B, C, D, E, F, G, H, I, J, K, L, M
      , N, O, P, Q, R, S, T, U, V, W, X, Y, Z
      , Num1, Num2, Num3, Num4, Num5, Num6, Num7, Num8, Num9, Num0
      , Enter, Escape, Backspace, Tab, Space
      , Minus, Equal, LeftBracket, RightBracket, Backslash
      , Semicolon, Quote, Grave, Comma, Period, Slash
      , CapsLock
      , F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12
      , PrintScreen, ScrollLock, Pause, Insert, Home, PageUp
      , Delete, End, PageDown
      , ArrowRight, ArrowLeft, ArrowDown, ArrowUp
      , NumLock, NumpadDivide, NumpadMultiply, NumpadMinus, NumpadPlus
      , NumpadEnter, Numpad1, Numpad2, Numpad3, Numpad4, Numpad5
      , Numpad6, Numpad7, Numpad8, Numpad9, Numpad0, NumpadDecimal
      , LeftCtrl, LeftShift, LeftAlt, LeftMeta
      , RightCtrl, RightShift, RightAlt, RightMeta
      )
  , toU8
  , fromU8
  , toDisplayString
  ) as ScanCode

-- State types are safe to re-export (unique names)
import Hydrogen.Schema.Gestural.Input.State
  ( MouseState
  , mouseStateNew
  , mouseStateAt
  , KeyboardState
  , keyboardStateNew
  , isPressed
  , pressKey
  , releaseKey
  , clearKeys
  , pressedCount
  , FrameInput
  , frameInputNew
  ) as State

-- Note: Modifiers, MouseButtons, and Shortcut should be imported qualified
-- by the consumer to avoid name conflicts. They are NOT re-exported here.
--
-- Example usage:
--   import Hydrogen.Schema.Gestural.Input.Modifiers as Mod
--   import Hydrogen.Schema.Gestural.Input.MouseButtons as MB
--   import Hydrogen.Schema.Gestural.Input.Shortcut as Shortcut
