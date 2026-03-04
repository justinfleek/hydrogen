-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // gestural // input // mousebuttons
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | MouseButtons - mouse button state as bounded bitfield.
-- |
-- | **Zero JavaScript. Zero browser APIs. Zero side effects.**
-- |
-- | This is a bounded u8 bitfield matching the Rust runtime exactly.
-- |
-- | ## Bit Layout (matches Rust)
-- | - Bit 0 (0x01): Left (primary)
-- | - Bit 1 (0x02): Right (secondary)
-- | - Bit 2 (0x04): Middle (auxiliary)
-- | - Bit 3 (0x08): Back (browser back)
-- | - Bit 4 (0x10): Forward (browser forward)
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Show)
-- | - Data.Int.Bits (for bitwise operations)
-- |
-- | ## Alignment
-- | - Matches: `runtime/src/core/input.rs::MouseButtons`

module Hydrogen.Schema.Gestural.Input.MouseButtons
  ( -- * MouseButtons Type
    MouseButtons(MouseButtons)
  -- * Constants
  , none
  , left
  , right
  , middle
  , back
  , forward
  -- * Constructors
  , fromBits
  , toBits
  -- * Operations
  , union
  , contains
  -- * Queries
  , hasLeft
  , hasRight
  , hasMiddle
  , hasBack
  , hasForward
  , hasAny
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (/=)
  , (<>)
  , compare
  )

import Data.Int.Bits ((.&.), (.|.))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mousebuttons type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mouse button state as u8 bitfield.
-- |
-- | Bounded: only valid bit combinations (0x00 - 0x1F).
newtype MouseButtons = MouseButtons Int

derive instance eqMouseButtons :: Eq MouseButtons

instance ordMouseButtons :: Ord MouseButtons where
  compare (MouseButtons a) (MouseButtons b) = compare a b

instance showMouseButtons :: Show MouseButtons where
  show (MouseButtons bits) = "MouseButtons(" <> show bits <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No buttons pressed.
none :: MouseButtons
none = MouseButtons 0

-- | Left mouse button (primary).
left :: MouseButtons
left = MouseButtons 1

-- | Right mouse button (secondary).
right :: MouseButtons
right = MouseButtons 2

-- | Middle mouse button (auxiliary).
middle :: MouseButtons
middle = MouseButtons 4

-- | Back button (browser back).
back :: MouseButtons
back = MouseButtons 8

-- | Forward button (browser forward).
forward :: MouseButtons
forward = MouseButtons 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create from raw bits (masks to valid range 0x00-0x1F).
fromBits :: Int -> MouseButtons
fromBits bits = MouseButtons (bits .&. 0x1F)

-- | Get raw bits.
toBits :: MouseButtons -> Int
toBits (MouseButtons bits) = bits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine button states (bitwise OR).
union :: MouseButtons -> MouseButtons -> MouseButtons
union (MouseButtons a) (MouseButtons b) = MouseButtons (a .|. b)

-- | Check if a specific button is pressed.
contains :: MouseButtons -> MouseButtons -> Boolean
contains (MouseButtons state) (MouseButtons check) = (state .&. check) == check

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if left button is pressed.
hasLeft :: MouseButtons -> Boolean
hasLeft m = contains m left

-- | Check if right button is pressed.
hasRight :: MouseButtons -> Boolean
hasRight m = contains m right

-- | Check if middle button is pressed.
hasMiddle :: MouseButtons -> Boolean
hasMiddle m = contains m middle

-- | Check if back button is pressed.
hasBack :: MouseButtons -> Boolean
hasBack m = contains m back

-- | Check if forward button is pressed.
hasForward :: MouseButtons -> Boolean
hasForward m = contains m forward

-- | Check if any button is pressed.
hasAny :: MouseButtons -> Boolean
hasAny (MouseButtons bits) = bits /= 0
