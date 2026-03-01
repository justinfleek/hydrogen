-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // framestate // mouse
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mouse — Pointer Input State
-- |
-- | ## Purpose
-- |
-- | Tracks mouse/pointer state for the current frame:
-- |
-- | - **Position**: Current and previous X/Y coordinates
-- | - **Velocity**: Movement rate for momentum/inertia effects
-- | - **Buttons**: Currently pressed mouse buttons
-- | - **Hover/Active**: Element targeting for hit testing
-- | - **Drag State**: For drag-and-drop interactions
-- |
-- | ## Future: Input Submodule
-- |
-- | MouseState will eventually move to `FrameState.Input` alongside:
-- |
-- | - **TouchState**: Multi-touch, pressure, contact area
-- | - **StylusState**: Tilt, azimuth, pressure, barrel button
-- | - **GestureState**: Pinch, rotate, pan recognition
-- |
-- | For now, mouse is the most common input and lives here.

module Hydrogen.GPU.FrameState.Mouse
  ( -- * Mouse State
    MouseState
  , mkMouseState
  
  -- * Accessors
  , mousePosition
  , mouseButtons
  , mouseHoverTarget
  , mouseDelta
  , mouseVelocity
  
  -- * Re-export MouseButton from Gestural.Pointer
  , module PointerButton
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  )

import Prim (Array, Boolean, Int, Number)
import Data.Maybe (Maybe(Nothing))

-- Mouse button type (authoritative definition in Gestural.Pointer)
-- Re-exported via `module PointerButton` in the exports list
import Hydrogen.Schema.Gestural.Pointer
  ( MouseButton(MouseLeft, MouseMiddle, MouseRight, MouseBack, MouseForward)
  ) as PointerButton

-- Also import unqualified for local use
import Hydrogen.Schema.Gestural.Pointer (MouseButton)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mouse state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mouse interaction state
-- |
-- | Tracks position, velocity, buttons, and targeting for the current frame.
-- | Position is in viewport pixels (0,0 = top-left corner).
type MouseState =
  { x :: Number                -- X position in viewport pixels
  , y :: Number                -- Y position in viewport pixels
  , prevX :: Number            -- Previous X position
  , prevY :: Number            -- Previous Y position
  , velocityX :: Number        -- X velocity (pixels per frame)
  , velocityY :: Number        -- Y velocity (pixels per frame)
  , buttons :: Array MouseButton  -- Currently pressed buttons
  , hoverTarget :: Maybe Int   -- PickId of element under cursor
  , activeTarget :: Maybe Int  -- PickId of element being pressed
  , dragStartX :: Number       -- Drag start X (if dragging)
  , dragStartY :: Number       -- Drag start Y (if dragging)
  , isDragging :: Boolean      -- Is a drag in progress
  }

-- | Create initial mouse state
-- |
-- | Starts at origin (0,0) with no buttons pressed and no targets.
-- | Real position will be set on first mouse event.
mkMouseState :: MouseState
mkMouseState =
  { x: 0.0
  , y: 0.0
  , prevX: 0.0
  , prevY: 0.0
  , velocityX: 0.0
  , velocityY: 0.0
  , buttons: []
  , hoverTarget: Nothing
  , activeTarget: Nothing
  , dragStartX: 0.0
  , dragStartY: 0.0
  , isDragging: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get mouse position as a record
-- |
-- | Returns current X/Y in viewport pixels.
mousePosition :: MouseState -> { x :: Number, y :: Number }
mousePosition state = { x: state.x, y: state.y }

-- | Get pressed buttons
-- |
-- | Returns array of currently pressed buttons.
-- | Empty array means no buttons pressed.
mouseButtons :: MouseState -> Array MouseButton
mouseButtons state = state.buttons

-- | Get hover target PickId
-- |
-- | Returns the PickId of the element currently under the cursor,
-- | or Nothing if no element is under the cursor.
mouseHoverTarget :: MouseState -> Maybe Int
mouseHoverTarget state = state.hoverTarget

-- | Get mouse movement since last frame
-- |
-- | Returns delta X/Y (current - previous position).
-- | Positive dx = moved right, positive dy = moved down.
mouseDelta :: MouseState -> { dx :: Number, dy :: Number }
mouseDelta state = { dx: state.x - state.prevX, dy: state.y - state.prevY }

-- | Get mouse velocity
-- |
-- | Returns velocity in pixels per frame.
-- | Use with delta time for momentum effects.
mouseVelocity :: MouseState -> { vx :: Number, vy :: Number }
mouseVelocity state = { vx: state.velocityX, vy: state.velocityY }
