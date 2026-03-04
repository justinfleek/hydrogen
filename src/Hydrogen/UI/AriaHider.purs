-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // ui // ariahider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ARIA Hider — Accessibility hiding for modal dialogs
-- |
-- | When a modal dialog opens, all sibling content must be hidden from
-- | screen readers by setting `aria-hidden="true"`. This module provides
-- | pure command descriptions that the Rust runtime interprets.
-- |
-- | ## Design Philosophy
-- |
-- | This module emits **pure data** (Cmd values) instead of performing
-- | effects directly. The Rust/WASM runtime interprets these commands
-- | and executes the actual DOM manipulation.
-- |
-- | At billion-agent scale, commands are encoded as SIGIL frames:
-- |   - `AriaHide` → opcode 0xD0 (ARIA_HIDE)
-- |   - `AriaRestore` → opcode 0xD1 (ARIA_RESTORE)
-- |
-- | straylight-llm consumes these frames via ZMQ4 at 10,000 tokens/second.
-- |
-- | ## Usage (Elm Architecture)
-- |
-- | ```purescript
-- | import Hydrogen.UI.AriaHider as Aria
-- | import Hydrogen.Runtime.Cmd (Cmd, ariaHide, ariaRestore, AriaStateToken)
-- |
-- | data Msg
-- |   = OpenModal
-- |   | CloseModal
-- |   | AriaStateReceived AriaStateToken
-- |
-- | update :: Msg -> State -> Transition State Msg
-- | update msg state = case msg of
-- |   OpenModal ->
-- |     transition
-- |       state { modalOpen = true }
-- |       (ariaHide "#modal-content" AriaStateReceived)
-- |
-- |   AriaStateReceived token ->
-- |     noCmd state { ariaToken = Just token }
-- |
-- |   CloseModal ->
-- |     case state.ariaToken of
-- |       Just token ->
-- |         transition
-- |           state { modalOpen = false, ariaToken = Nothing }
-- |           (ariaRestore token)
-- |       Nothing ->
-- |         noCmd state { modalOpen = false }
-- | ```
-- |
-- | ## SIGIL Wire Encoding
-- |
-- | For direct SIGIL frame emission (advanced usage):
-- |
-- | ```purescript
-- | import Hydrogen.Scraper.Wire.Encode (encodeAriaHide, encodeAriaRestore)
-- |
-- | -- Encode hide command to SIGIL frame
-- | let frame = encodeAriaHide "#modal-content"
-- | -- Frame contains: [0xD0, varint(len), UTF-8 bytes...]
-- | ```
-- |
-- | ## Migration from Foreign Import
-- |
-- | If you have existing code using the Effect-based API:
-- |
-- | ```purescript
-- | -- OLD (foreign import, now removed):
-- | -- hideOthers :: HTMLElement -> Effect AriaHiderState
-- |
-- | -- NEW (pure command):
-- | -- Use ariaHide from Hydrogen.Runtime.Cmd
-- | ```
-- |
-- | The Effect-based functions are intentionally removed. All side effects
-- | flow through the Cmd type for testability and determinism.

module Hydrogen.UI.AriaHider
  ( -- * Re-exports from Hydrogen.Runtime.Cmd
    -- | Use these in your update functions
    module ReExports
  
  -- * SIGIL Frame Encoding
  -- | For direct wire encoding (advanced)
  , encodeAriaHideFrame
  , encodeAriaRestoreFrame
  ) where

import Hydrogen.Runtime.Cmd 
  ( AriaStateToken(AriaStateToken)
  , ariaHide
  , ariaRestore
  ) as ReExports

import Hydrogen.Runtime.Cmd (AriaStateToken(AriaStateToken))
import Hydrogen.Scraper.Wire.Types (Frame)
import Hydrogen.Scraper.Wire.Encode (encodeAriaHide, encodeAriaRestore)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // sigil frame encoding
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Encode an ARIA hide command as a SIGIL frame.
-- |
-- | SIGIL opcode: 0xD0 (ARIA_HIDE)
-- | Payload: varint-prefixed UTF-8 element selector
-- |
-- | This is for advanced usage where you need to emit raw SIGIL frames
-- | directly (e.g., for testing, debugging, or custom transport).
-- |
-- | For normal application code, use `ariaHide` from `Hydrogen.Runtime.Cmd`.
encodeAriaHideFrame :: String -> Frame
encodeAriaHideFrame = encodeAriaHide

-- | Encode an ARIA restore command as a SIGIL frame.
-- |
-- | SIGIL opcode: 0xD1 (ARIA_RESTORE)
-- | Payload: u32 state token
-- |
-- | This is for advanced usage where you need to emit raw SIGIL frames.
-- |
-- | For normal application code, use `ariaRestore` from `Hydrogen.Runtime.Cmd`.
encodeAriaRestoreFrame :: AriaStateToken -> Frame
encodeAriaRestoreFrame (AriaStateToken token) = encodeAriaRestore token
