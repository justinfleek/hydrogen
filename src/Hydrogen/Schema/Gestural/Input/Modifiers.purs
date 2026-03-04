-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // gestural // input // modifiers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Modifiers - keyboard modifier state as bounded bitfield.
-- |
-- | **Zero JavaScript. Zero browser APIs. Zero side effects.**
-- |
-- | This is a bounded u8 bitfield matching the Rust runtime exactly.
-- |
-- | ## Bit Layout (matches Rust)
-- | - Bit 0 (0x01): Shift
-- | - Bit 1 (0x02): Ctrl
-- | - Bit 2 (0x04): Alt
-- | - Bit 3 (0x08): Meta
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Show)
-- | - Data.Int.Bits (for bitwise operations)
-- |
-- | ## Alignment
-- | - Matches: `runtime/src/core/input.rs::Modifiers`

module Hydrogen.Schema.Gestural.Input.Modifiers
  ( -- * Modifiers Type
    Modifiers(Modifiers)
  -- * Constants
  , none
  , shift
  , ctrl
  , alt
  , meta
  -- * Constructors
  , fromBits
  , toBits
  -- * Operations
  , union
  , contains
  -- * Queries
  , hasShift
  , hasCtrl
  , hasAlt
  , hasMeta
  , hasCommand
  -- * Display
  , toDisplayString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (||)
  , (/=)
  , (<>)
  , compare
  )

import Data.Array (filter)
import Data.Int.Bits ((.&.), (.|.))
import Data.String (joinWith)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // modifiers type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard modifier state as u8 bitfield.
-- |
-- | Bounded: only valid bit combinations (0x00 - 0x0F).
newtype Modifiers = Modifiers Int

derive instance eqModifiers :: Eq Modifiers

instance ordModifiers :: Ord Modifiers where
  compare (Modifiers a) (Modifiers b) = compare a b

instance showModifiers :: Show Modifiers where
  show m = "Modifiers(" <> toDisplayString m <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No modifiers pressed.
none :: Modifiers
none = Modifiers 0

-- | Shift modifier (bit 0).
shift :: Modifiers
shift = Modifiers 1

-- | Control modifier (bit 1).
-- | Ctrl on Windows/Linux, Control on Mac.
ctrl :: Modifiers
ctrl = Modifiers 2

-- | Alt modifier (bit 2).
-- | Alt on Windows/Linux, Option on Mac.
alt :: Modifiers
alt = Modifiers 4

-- | Meta modifier (bit 3).
-- | Windows key on Windows, Command on Mac.
meta :: Modifiers
meta = Modifiers 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create from raw bits (masks to valid range 0x00-0x0F).
fromBits :: Int -> Modifiers
fromBits bits = Modifiers (bits .&. 0x0F)

-- | Get raw bits.
toBits :: Modifiers -> Int
toBits (Modifiers bits) = bits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine modifier states (bitwise OR).
union :: Modifiers -> Modifiers -> Modifiers
union (Modifiers a) (Modifiers b) = Modifiers (a .|. b)

-- | Check if a specific modifier is set.
contains :: Modifiers -> Modifiers -> Boolean
contains (Modifiers state) (Modifiers check) = (state .&. check) == check

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if Shift is pressed.
hasShift :: Modifiers -> Boolean
hasShift m = contains m shift

-- | Check if Ctrl is pressed.
hasCtrl :: Modifiers -> Boolean
hasCtrl m = contains m ctrl

-- | Check if Alt is pressed.
hasAlt :: Modifiers -> Boolean
hasAlt m = contains m alt

-- | Check if Meta is pressed.
hasMeta :: Modifiers -> Boolean
hasMeta m = contains m meta

-- | Check for Ctrl OR Meta (cross-platform "command" shortcut).
-- |
-- | On Mac, users expect Cmd+key. On Windows/Linux, Ctrl+key.
-- | This function returns true for either.
hasCommand :: Modifiers -> Boolean
hasCommand m = hasCtrl m || hasMeta m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to human-readable string.
-- |
-- | Returns "+"-separated list of active modifiers.
toDisplayString :: Modifiers -> String
toDisplayString m =
  let
    parts = filter (\s -> s /= "")
      [ if hasCtrl m then "Ctrl" else ""
      , if hasAlt m then "Alt" else ""
      , if hasShift m then "Shift" else ""
      , if hasMeta m then "Meta" else ""
      ]
  in
    if parts == []
      then "none"
      else joinWith "+" parts
