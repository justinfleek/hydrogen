-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // gestural // input // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | State - input state types for mouse, keyboard, and frame.
-- |
-- | **Zero JavaScript. Zero browser APIs. Zero side effects.**
-- |
-- | These types match the Rust runtime exactly and serialize to binary.
-- |
-- | ## Dependencies
-- | - Gestural.Input.ScanCode
-- | - Gestural.Input.Modifiers
-- | - Gestural.Input.MouseButtons
-- |
-- | ## Alignment
-- | - Matches: `runtime/src/core/input.rs::MouseState`
-- | - Matches: `runtime/src/core/input.rs::KeyboardState`
-- | - Matches: `runtime/src/core/input.rs::FrameInput`

module Hydrogen.Schema.Gestural.Input.State
  ( -- * Mouse State
    MouseState
  , mouseStateNew
  , mouseStateAt
  -- * Keyboard State
  , KeyboardState
  , keyboardStateNew
  , isPressed
  , pressKey
  , releaseKey
  , clearKeys
  , pressedCount
  -- * Frame Input
  , FrameInput
  , frameInputNew
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (/=)
  , (+)
  , (<>)
  , map
  )

import Data.Array (filter, findIndex, updateAt, length)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Schema.Gestural.Input.ScanCode (ScanCode, toU8)
import Hydrogen.Schema.Gestural.Input.Modifiers (Modifiers)
import Hydrogen.Schema.Gestural.Input.Modifiers as Modifiers
import Hydrogen.Schema.Gestural.Input.MouseButtons (MouseButtons)
import Hydrogen.Schema.Gestural.Input.MouseButtons as MouseButtons

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mouse state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Current mouse state.
-- |
-- | All coordinates in logical pixels. The host handles DPI scaling.
type MouseState =
  { x :: Number          -- ^ X position (left = 0)
  , y :: Number          -- ^ Y position (top = 0)
  , buttons :: MouseButtons  -- ^ Currently pressed buttons
  , scrollX :: Number    -- ^ Scroll delta X since last frame (positive = right)
  , scrollY :: Number    -- ^ Scroll delta Y since last frame (positive = down)
  , inside :: Boolean    -- ^ Whether mouse is inside application area
  }

-- | Create a new mouse state with all fields zeroed.
mouseStateNew :: MouseState
mouseStateNew =
  { x: 0.0
  , y: 0.0
  , buttons: MouseButtons.none
  , scrollX: 0.0
  , scrollY: 0.0
  , inside: false
  }

-- | Create mouse state at a specific position.
mouseStateAt :: Number -> Number -> MouseState
mouseStateAt x y =
  { x
  , y
  , buttons: MouseButtons.none
  , scrollX: 0.0
  , scrollY: 0.0
  , inside: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // keyboard state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard state.
-- |
-- | Tracks up to 6 simultaneously pressed keys (USB HID limit).
-- | Each slot is 0 for empty or a scan code byte value.
type KeyboardState =
  { pressed :: Array Int   -- ^ Up to 6 pressed keys (0 = empty slot)
  , modifiers :: Modifiers -- ^ Current modifier state
  }

-- | Create a new keyboard state with no keys pressed.
keyboardStateNew :: KeyboardState
keyboardStateNew =
  { pressed: [0, 0, 0, 0, 0, 0]
  , modifiers: Modifiers.none
  }

-- | Check if a specific key is currently pressed.
isPressed :: ScanCode -> KeyboardState -> Boolean
isPressed code state =
  let codeU8 = toU8 code
  in case findIndex (\k -> k == codeU8) state.pressed of
    Just _ -> true
    Nothing -> false

-- | Add a key to the pressed state.
-- |
-- | Returns the updated state. If the key is already pressed or no slots
-- | are available, returns the state unchanged.
pressKey :: ScanCode -> KeyboardState -> KeyboardState
pressKey code state =
  let
    codeU8 = toU8 code
    -- Check if already pressed
    alreadyPressed = case findIndex (\k -> k == codeU8) state.pressed of
      Just _ -> true
      Nothing -> false
  in
    if alreadyPressed
      then state
      else
        -- Find empty slot (0)
        case findIndex (\k -> k == 0) state.pressed of
          Just idx ->
            state { pressed = fromMaybe state.pressed (updateAt idx codeU8 state.pressed) }
          Nothing ->
            state  -- No empty slots (USB HID limit)

-- | Remove a key from the pressed state.
-- |
-- | Returns the updated state. If the key is not pressed, returns unchanged.
releaseKey :: ScanCode -> KeyboardState -> KeyboardState
releaseKey code state =
  let codeU8 = toU8 code
  in case findIndex (\k -> k == codeU8) state.pressed of
    Just idx ->
      state { pressed = fromMaybe state.pressed (updateAt idx 0 state.pressed) }
    Nothing ->
      state

-- | Clear all pressed keys.
clearKeys :: KeyboardState -> KeyboardState
clearKeys state = state { pressed = [0, 0, 0, 0, 0, 0] }

-- | Get count of currently pressed keys.
pressedCount :: KeyboardState -> Int
pressedCount state = length (filter (\k -> k /= 0) state.pressed)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // frame input
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete input state for a single frame.
-- |
-- | The host constructs this from accumulated events and passes it
-- | to the pure core's step function.
type FrameInput =
  { mouse :: MouseState            -- ^ Current mouse state
  , keyboard :: KeyboardState      -- ^ Current keyboard state
  , timeMs :: Number               -- ^ Absolute time since start (ms)
  , deltaMs :: Number              -- ^ Delta since last frame (ms)
  , frame :: Int                   -- ^ Frame number (monotonic)
  , viewportWidth :: Number        -- ^ Viewport width (logical pixels)
  , viewportHeight :: Number       -- ^ Viewport height (logical pixels)
  , devicePixelRatio :: Number     -- ^ DPI scale factor
  }

-- | Create a new frame input with default values.
frameInputNew :: FrameInput
frameInputNew =
  { mouse: mouseStateNew
  , keyboard: keyboardStateNew
  , timeMs: 0.0
  , deltaMs: 16.666666  -- ~60fps default
  , frame: 0
  , viewportWidth: 0.0
  , viewportHeight: 0.0
  , devicePixelRatio: 1.0
  }
