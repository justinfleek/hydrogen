-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // gestural // input // shortcut
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shortcut - keyboard shortcut as pure bounded data.
-- |
-- | **Zero JavaScript. Zero browser APIs. Zero side effects.**
-- |
-- | A shortcut is a key code plus modifiers. Fully bounded, serializable,
-- | and deterministic.
-- |
-- | ## Dependencies
-- | - Gestural.Input.ScanCode
-- | - Gestural.Input.Modifiers
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Gestural.Input.Shortcut as Shortcut
-- | import Hydrogen.Schema.Gestural.Input.ScanCode as SC
-- |
-- | -- Ctrl+S
-- | saveShortcut = Shortcut.ctrl SC.S
-- |
-- | -- Ctrl+Shift+P
-- | paletteShortcut = Shortcut.ctrlShift SC.P
-- | ```

module Hydrogen.Schema.Gestural.Input.Shortcut
  ( -- * Shortcut Type
    Shortcut
  -- * Constructors
  , shortcut
  , simple
  , ctrl
  , ctrlShift
  , alt
  , altShift
  , meta
  , metaShift
  -- * Common Shortcuts
  , copy
  , cut
  , paste
  , undo
  , redo
  , save
  , find
  , selectAll
  , close
  , newDoc
  , open
  -- * Accessors
  , getCode
  , getModifiers
  -- * Matching
  , matches
  , matchesLoose
  -- * Display
  , toDisplayString
  -- * Serialization
  , toBytes
  , fromBytes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (<>)
  , not
  )

import Data.Array (filter)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (joinWith)

import Hydrogen.Schema.Gestural.Input.ScanCode
  ( ScanCode
      ( A, C, F, N, O, P, S, V, W, X, Y, Z
      )
  , toU8
  , fromU8
  , toDisplayString
  ) as SC

import Hydrogen.Schema.Gestural.Input.Modifiers
  ( Modifiers
  , none
  , hasShift
  , hasCtrl
  , hasAlt
  , hasMeta
  , hasCommand
  , toBits
  , fromBits
  , union
  ) as Mod

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // shortcut type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard shortcut as pure bounded data.
-- |
-- | A combination of a key code and modifier flags.
-- | Serializes to exactly 2 bytes: [scancode, modifiers].
type Shortcut =
  { code :: SC.ScanCode      -- ^ The key to press
  , modifiers :: Mod.Modifiers  -- ^ Required modifiers
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a shortcut with explicit modifiers.
shortcut :: SC.ScanCode -> Mod.Modifiers -> Shortcut
shortcut code modifiers = { code, modifiers }

-- | Create a shortcut with just a key (no modifiers).
simple :: SC.ScanCode -> Shortcut
simple code = { code, modifiers: Mod.none }

-- | Create Ctrl+Key shortcut.
ctrl :: SC.ScanCode -> Shortcut
ctrl code = { code, modifiers: Mod.fromBits 0x02 }

-- | Create Ctrl+Shift+Key shortcut.
ctrlShift :: SC.ScanCode -> Shortcut
ctrlShift code = { code, modifiers: Mod.fromBits 0x03 }

-- | Create Alt+Key shortcut.
alt :: SC.ScanCode -> Shortcut
alt code = { code, modifiers: Mod.fromBits 0x04 }

-- | Create Alt+Shift+Key shortcut.
altShift :: SC.ScanCode -> Shortcut
altShift code = { code, modifiers: Mod.fromBits 0x05 }

-- | Create Meta+Key shortcut (Cmd on Mac).
meta :: SC.ScanCode -> Shortcut
meta code = { code, modifiers: Mod.fromBits 0x08 }

-- | Create Meta+Shift+Key shortcut.
metaShift :: SC.ScanCode -> Shortcut
metaShift code = { code, modifiers: Mod.fromBits 0x09 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // common shortcuts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ctrl+C / Cmd+C (Copy)
copy :: Shortcut
copy = ctrl SC.C

-- | Ctrl+X / Cmd+X (Cut)
cut :: Shortcut
cut = ctrl SC.X

-- | Ctrl+V / Cmd+V (Paste)
paste :: Shortcut
paste = ctrl SC.V

-- | Ctrl+Z / Cmd+Z (Undo)
undo :: Shortcut
undo = ctrl SC.Z

-- | Ctrl+Shift+Z / Cmd+Shift+Z (Redo)
redo :: Shortcut
redo = ctrlShift SC.Z

-- | Ctrl+S / Cmd+S (Save)
save :: Shortcut
save = ctrl SC.S

-- | Ctrl+F / Cmd+F (Find)
find :: Shortcut
find = ctrl SC.F

-- | Ctrl+A / Cmd+A (Select All)
selectAll :: Shortcut
selectAll = ctrl SC.A

-- | Ctrl+W / Cmd+W (Close)
close :: Shortcut
close = ctrl SC.W

-- | Ctrl+N / Cmd+N (New)
newDoc :: Shortcut
newDoc = ctrl SC.N

-- | Ctrl+O / Cmd+O (Open)
open :: Shortcut
open = ctrl SC.O

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the scan code.
getCode :: Shortcut -> SC.ScanCode
getCode s = s.code

-- | Get the modifiers.
getModifiers :: Shortcut -> Mod.Modifiers
getModifiers s = s.modifiers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // matching
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if input matches shortcut exactly.
-- |
-- | All modifiers must match exactly.
matches :: Shortcut -> SC.ScanCode -> Mod.Modifiers -> Boolean
matches s inputCode inputMods =
  s.code == inputCode && s.modifiers == inputMods

-- | Check if input matches shortcut loosely.
-- |
-- | Ctrl and Meta are treated as interchangeable (cross-platform).
matchesLoose :: Shortcut -> SC.ScanCode -> Mod.Modifiers -> Boolean
matchesLoose s inputCode inputMods =
  s.code == inputCode
  && Mod.hasAlt s.modifiers == Mod.hasAlt inputMods
  && Mod.hasShift s.modifiers == Mod.hasShift inputMods
  && (if Mod.hasCommand s.modifiers
      then Mod.hasCommand inputMods
      else not (Mod.hasCommand inputMods))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to human-readable display string.
-- |
-- | Example: "Ctrl+Shift+P", "Alt+F4", "Escape"
toDisplayString :: Shortcut -> String
toDisplayString s =
  let
    mods = s.modifiers
    modParts = filter (\str -> str /= "")
      [ if Mod.hasCtrl mods then "Ctrl" else ""
      , if Mod.hasAlt mods then "Alt" else ""
      , if Mod.hasShift mods then "Shift" else ""
      , if Mod.hasMeta mods then "Meta" else ""
      ]
    parts = modParts <> [SC.toDisplayString s.code]
  in
    joinWith "+" parts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize to 2 bytes: [scancode, modifiers].
toBytes :: Shortcut -> { byte0 :: Int, byte1 :: Int }
toBytes s =
  { byte0: SC.toU8 s.code
  , byte1: Mod.toBits s.modifiers
  }

-- | Parse from 2 bytes.
fromBytes :: Int -> Int -> Maybe Shortcut
fromBytes byte0 byte1 =
  case SC.fromU8 byte0 of
    Just code -> Just { code, modifiers: Mod.fromBits byte1 }
    Nothing -> Nothing
