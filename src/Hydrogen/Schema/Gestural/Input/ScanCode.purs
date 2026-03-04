-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // gestural // input // scancode
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ScanCode - USB HID scan codes for platform-independent key identification.
-- |
-- | **Zero JavaScript. Zero browser APIs. Zero side effects.**
-- |
-- | This is a bounded ADT matching the Rust runtime exactly.
-- | Every variant maps to a USB HID scan code (single byte).
-- |
-- | Reference: USB HID Usage Tables, Section 10 (Keyboard/Keypad Page)
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Maybe (for fromU8)
-- |
-- | ## Alignment
-- | - Matches: `runtime/src/core/input.rs::ScanCode`

module Hydrogen.Schema.Gestural.Input.ScanCode
  ( -- * ScanCode Type
    ScanCode
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
  -- * Serialization
  , toU8
  , fromU8
  -- * Display
  , toDisplayString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<>)
  , compare
  , Ordering
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // scancode type
-- ═════════════════════════════════════════════════════════════════════════════

-- | USB HID scan code for platform-independent key identification.
-- |
-- | This is a bounded ADT — only valid key codes can exist.
-- | Each variant maps to a specific USB HID byte value.
data ScanCode
  -- Letters (0x04 - 0x1D)
  = A | B | C | D | E | F | G | H | I | J | K | L | M
  | N | O | P | Q | R | S | T | U | V | W | X | Y | Z
  -- Numbers (0x1E - 0x27)
  | Num1 | Num2 | Num3 | Num4 | Num5 | Num6 | Num7 | Num8 | Num9 | Num0
  -- Control keys (0x28 - 0x2C)
  | Enter | Escape | Backspace | Tab | Space
  -- Punctuation (0x2D - 0x38)
  | Minus | Equal | LeftBracket | RightBracket | Backslash
  | Semicolon | Quote | Grave | Comma | Period | Slash
  -- Lock keys (0x39)
  | CapsLock
  -- Function keys (0x3A - 0x45)
  | F1 | F2 | F3 | F4 | F5 | F6 | F7 | F8 | F9 | F10 | F11 | F12
  -- Navigation (0x46 - 0x4E)
  | PrintScreen | ScrollLock | Pause | Insert | Home | PageUp
  | Delete | End | PageDown
  -- Arrow keys (0x4F - 0x52)
  | ArrowRight | ArrowLeft | ArrowDown | ArrowUp
  -- Numpad (0x53 - 0x63)
  | NumLock | NumpadDivide | NumpadMultiply | NumpadMinus | NumpadPlus
  | NumpadEnter | Numpad1 | Numpad2 | Numpad3 | Numpad4 | Numpad5
  | Numpad6 | Numpad7 | Numpad8 | Numpad9 | Numpad0 | NumpadDecimal
  -- Modifiers (0xE0 - 0xE7)
  | LeftCtrl | LeftShift | LeftAlt | LeftMeta
  | RightCtrl | RightShift | RightAlt | RightMeta

derive instance eqScanCode :: Eq ScanCode

instance ordScanCode :: Ord ScanCode where
  compare a b = compare (toU8 a) (toU8 b)

instance showScanCode :: Show ScanCode where
  show = toDisplayString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to USB HID scan code (single byte).
-- |
-- | Total function — every ScanCode maps to exactly one byte.
toU8 :: ScanCode -> Int
toU8 A = 0x04
toU8 B = 0x05
toU8 C = 0x06
toU8 D = 0x07
toU8 E = 0x08
toU8 F = 0x09
toU8 G = 0x0A
toU8 H = 0x0B
toU8 I = 0x0C
toU8 J = 0x0D
toU8 K = 0x0E
toU8 L = 0x0F
toU8 M = 0x10
toU8 N = 0x11
toU8 O = 0x12
toU8 P = 0x13
toU8 Q = 0x14
toU8 R = 0x15
toU8 S = 0x16
toU8 T = 0x17
toU8 U = 0x18
toU8 V = 0x19
toU8 W = 0x1A
toU8 X = 0x1B
toU8 Y = 0x1C
toU8 Z = 0x1D
toU8 Num1 = 0x1E
toU8 Num2 = 0x1F
toU8 Num3 = 0x20
toU8 Num4 = 0x21
toU8 Num5 = 0x22
toU8 Num6 = 0x23
toU8 Num7 = 0x24
toU8 Num8 = 0x25
toU8 Num9 = 0x26
toU8 Num0 = 0x27
toU8 Enter = 0x28
toU8 Escape = 0x29
toU8 Backspace = 0x2A
toU8 Tab = 0x2B
toU8 Space = 0x2C
toU8 Minus = 0x2D
toU8 Equal = 0x2E
toU8 LeftBracket = 0x2F
toU8 RightBracket = 0x30
toU8 Backslash = 0x31
toU8 Semicolon = 0x33
toU8 Quote = 0x34
toU8 Grave = 0x35
toU8 Comma = 0x36
toU8 Period = 0x37
toU8 Slash = 0x38
toU8 CapsLock = 0x39
toU8 F1 = 0x3A
toU8 F2 = 0x3B
toU8 F3 = 0x3C
toU8 F4 = 0x3D
toU8 F5 = 0x3E
toU8 F6 = 0x3F
toU8 F7 = 0x40
toU8 F8 = 0x41
toU8 F9 = 0x42
toU8 F10 = 0x43
toU8 F11 = 0x44
toU8 F12 = 0x45
toU8 PrintScreen = 0x46
toU8 ScrollLock = 0x47
toU8 Pause = 0x48
toU8 Insert = 0x49
toU8 Home = 0x4A
toU8 PageUp = 0x4B
toU8 Delete = 0x4C
toU8 End = 0x4D
toU8 PageDown = 0x4E
toU8 ArrowRight = 0x4F
toU8 ArrowLeft = 0x50
toU8 ArrowDown = 0x51
toU8 ArrowUp = 0x52
toU8 NumLock = 0x53
toU8 NumpadDivide = 0x54
toU8 NumpadMultiply = 0x55
toU8 NumpadMinus = 0x56
toU8 NumpadPlus = 0x57
toU8 NumpadEnter = 0x58
toU8 Numpad1 = 0x59
toU8 Numpad2 = 0x5A
toU8 Numpad3 = 0x5B
toU8 Numpad4 = 0x5C
toU8 Numpad5 = 0x5D
toU8 Numpad6 = 0x5E
toU8 Numpad7 = 0x5F
toU8 Numpad8 = 0x60
toU8 Numpad9 = 0x61
toU8 Numpad0 = 0x62
toU8 NumpadDecimal = 0x63
toU8 LeftCtrl = 0xE0
toU8 LeftShift = 0xE1
toU8 LeftAlt = 0xE2
toU8 LeftMeta = 0xE3
toU8 RightCtrl = 0xE4
toU8 RightShift = 0xE5
toU8 RightAlt = 0xE6
toU8 RightMeta = 0xE7

-- | Parse from USB HID scan code.
-- |
-- | Returns Nothing for invalid/unsupported codes.
fromU8 :: Int -> Maybe ScanCode
fromU8 0x04 = Just A
fromU8 0x05 = Just B
fromU8 0x06 = Just C
fromU8 0x07 = Just D
fromU8 0x08 = Just E
fromU8 0x09 = Just F
fromU8 0x0A = Just G
fromU8 0x0B = Just H
fromU8 0x0C = Just I
fromU8 0x0D = Just J
fromU8 0x0E = Just K
fromU8 0x0F = Just L
fromU8 0x10 = Just M
fromU8 0x11 = Just N
fromU8 0x12 = Just O
fromU8 0x13 = Just P
fromU8 0x14 = Just Q
fromU8 0x15 = Just R
fromU8 0x16 = Just S
fromU8 0x17 = Just T
fromU8 0x18 = Just U
fromU8 0x19 = Just V
fromU8 0x1A = Just W
fromU8 0x1B = Just X
fromU8 0x1C = Just Y
fromU8 0x1D = Just Z
fromU8 0x1E = Just Num1
fromU8 0x1F = Just Num2
fromU8 0x20 = Just Num3
fromU8 0x21 = Just Num4
fromU8 0x22 = Just Num5
fromU8 0x23 = Just Num6
fromU8 0x24 = Just Num7
fromU8 0x25 = Just Num8
fromU8 0x26 = Just Num9
fromU8 0x27 = Just Num0
fromU8 0x28 = Just Enter
fromU8 0x29 = Just Escape
fromU8 0x2A = Just Backspace
fromU8 0x2B = Just Tab
fromU8 0x2C = Just Space
fromU8 0x2D = Just Minus
fromU8 0x2E = Just Equal
fromU8 0x2F = Just LeftBracket
fromU8 0x30 = Just RightBracket
fromU8 0x31 = Just Backslash
fromU8 0x33 = Just Semicolon
fromU8 0x34 = Just Quote
fromU8 0x35 = Just Grave
fromU8 0x36 = Just Comma
fromU8 0x37 = Just Period
fromU8 0x38 = Just Slash
fromU8 0x39 = Just CapsLock
fromU8 0x3A = Just F1
fromU8 0x3B = Just F2
fromU8 0x3C = Just F3
fromU8 0x3D = Just F4
fromU8 0x3E = Just F5
fromU8 0x3F = Just F6
fromU8 0x40 = Just F7
fromU8 0x41 = Just F8
fromU8 0x42 = Just F9
fromU8 0x43 = Just F10
fromU8 0x44 = Just F11
fromU8 0x45 = Just F12
fromU8 0x46 = Just PrintScreen
fromU8 0x47 = Just ScrollLock
fromU8 0x48 = Just Pause
fromU8 0x49 = Just Insert
fromU8 0x4A = Just Home
fromU8 0x4B = Just PageUp
fromU8 0x4C = Just Delete
fromU8 0x4D = Just End
fromU8 0x4E = Just PageDown
fromU8 0x4F = Just ArrowRight
fromU8 0x50 = Just ArrowLeft
fromU8 0x51 = Just ArrowDown
fromU8 0x52 = Just ArrowUp
fromU8 0x53 = Just NumLock
fromU8 0x54 = Just NumpadDivide
fromU8 0x55 = Just NumpadMultiply
fromU8 0x56 = Just NumpadMinus
fromU8 0x57 = Just NumpadPlus
fromU8 0x58 = Just NumpadEnter
fromU8 0x59 = Just Numpad1
fromU8 0x5A = Just Numpad2
fromU8 0x5B = Just Numpad3
fromU8 0x5C = Just Numpad4
fromU8 0x5D = Just Numpad5
fromU8 0x5E = Just Numpad6
fromU8 0x5F = Just Numpad7
fromU8 0x60 = Just Numpad8
fromU8 0x61 = Just Numpad9
fromU8 0x62 = Just Numpad0
fromU8 0x63 = Just NumpadDecimal
fromU8 0xE0 = Just LeftCtrl
fromU8 0xE1 = Just LeftShift
fromU8 0xE2 = Just LeftAlt
fromU8 0xE3 = Just LeftMeta
fromU8 0xE4 = Just RightCtrl
fromU8 0xE5 = Just RightShift
fromU8 0xE6 = Just RightAlt
fromU8 0xE7 = Just RightMeta
fromU8 _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to human-readable display string.
-- |
-- | Used for showing shortcuts in UI (e.g., "Ctrl+S").
toDisplayString :: ScanCode -> String
toDisplayString A = "A"
toDisplayString B = "B"
toDisplayString C = "C"
toDisplayString D = "D"
toDisplayString E = "E"
toDisplayString F = "F"
toDisplayString G = "G"
toDisplayString H = "H"
toDisplayString I = "I"
toDisplayString J = "J"
toDisplayString K = "K"
toDisplayString L = "L"
toDisplayString M = "M"
toDisplayString N = "N"
toDisplayString O = "O"
toDisplayString P = "P"
toDisplayString Q = "Q"
toDisplayString R = "R"
toDisplayString S = "S"
toDisplayString T = "T"
toDisplayString U = "U"
toDisplayString V = "V"
toDisplayString W = "W"
toDisplayString X = "X"
toDisplayString Y = "Y"
toDisplayString Z = "Z"
toDisplayString Num1 = "1"
toDisplayString Num2 = "2"
toDisplayString Num3 = "3"
toDisplayString Num4 = "4"
toDisplayString Num5 = "5"
toDisplayString Num6 = "6"
toDisplayString Num7 = "7"
toDisplayString Num8 = "8"
toDisplayString Num9 = "9"
toDisplayString Num0 = "0"
toDisplayString Enter = "Enter"
toDisplayString Escape = "Esc"
toDisplayString Backspace = "Backspace"
toDisplayString Tab = "Tab"
toDisplayString Space = "Space"
toDisplayString Minus = "-"
toDisplayString Equal = "="
toDisplayString LeftBracket = "["
toDisplayString RightBracket = "]"
toDisplayString Backslash = "\\"
toDisplayString Semicolon = ";"
toDisplayString Quote = "'"
toDisplayString Grave = "`"
toDisplayString Comma = ","
toDisplayString Period = "."
toDisplayString Slash = "/"
toDisplayString CapsLock = "CapsLock"
toDisplayString F1 = "F1"
toDisplayString F2 = "F2"
toDisplayString F3 = "F3"
toDisplayString F4 = "F4"
toDisplayString F5 = "F5"
toDisplayString F6 = "F6"
toDisplayString F7 = "F7"
toDisplayString F8 = "F8"
toDisplayString F9 = "F9"
toDisplayString F10 = "F10"
toDisplayString F11 = "F11"
toDisplayString F12 = "F12"
toDisplayString PrintScreen = "PrintScreen"
toDisplayString ScrollLock = "ScrollLock"
toDisplayString Pause = "Pause"
toDisplayString Insert = "Insert"
toDisplayString Home = "Home"
toDisplayString PageUp = "PageUp"
toDisplayString Delete = "Delete"
toDisplayString End = "End"
toDisplayString PageDown = "PageDown"
toDisplayString ArrowRight = "→"
toDisplayString ArrowLeft = "←"
toDisplayString ArrowDown = "↓"
toDisplayString ArrowUp = "↑"
toDisplayString NumLock = "NumLock"
toDisplayString NumpadDivide = "Num/"
toDisplayString NumpadMultiply = "Num*"
toDisplayString NumpadMinus = "Num-"
toDisplayString NumpadPlus = "Num+"
toDisplayString NumpadEnter = "NumEnter"
toDisplayString Numpad1 = "Num1"
toDisplayString Numpad2 = "Num2"
toDisplayString Numpad3 = "Num3"
toDisplayString Numpad4 = "Num4"
toDisplayString Numpad5 = "Num5"
toDisplayString Numpad6 = "Num6"
toDisplayString Numpad7 = "Num7"
toDisplayString Numpad8 = "Num8"
toDisplayString Numpad9 = "Num9"
toDisplayString Numpad0 = "Num0"
toDisplayString NumpadDecimal = "Num."
toDisplayString LeftCtrl = "Ctrl"
toDisplayString LeftShift = "Shift"
toDisplayString LeftAlt = "Alt"
toDisplayString LeftMeta = "Meta"
toDisplayString RightCtrl = "Ctrl"
toDisplayString RightShift = "Shift"
toDisplayString RightAlt = "Alt"
toDisplayString RightMeta = "Meta"
