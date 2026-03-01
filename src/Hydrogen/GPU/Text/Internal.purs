-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // text
--                                                                  // internal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Internal helper functions for text processing
-- |
-- | Contains utility functions shared across the text rendering modules:
-- | - String to codepoint conversion
-- | - Array manipulation helpers
-- | - Numeric conversions
-- |
-- | These are implementation details not exposed in the public API.

module Hydrogen.GPU.Text.Internal
  ( -- * String Processing
    stringToCodepoints
  , codePointToInt
  
  -- * Numeric Conversions
  , intToNumber
  
  -- * Array Utilities
  , mapArray
  , foldlArray
  , arrayLength
  
  -- * Glyph Utilities
  , sumAdvances
  , isSpace
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (==)
  , (<=)
  , (||)
  , (<>)
  )

import Data.Array (take, drop, length) as Array
import Data.String.CodePoints (toCodePointArray, CodePoint) as SCP
import Data.Enum (fromEnum) as Enum

import Hydrogen.GPU.Text.Types (ShapedGlyph)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // string processing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert string to array of Unicode codepoints.
-- |
-- | Uses Data.String.CodePoints.toCodePointArray which correctly handles
-- | all Unicode codepoints including supplementary planes (U+10000 to U+10FFFF).
-- | This properly handles emoji, rare CJK characters, mathematical symbols,
-- | and all other characters that require surrogate pairs in UTF-16.
-- |
-- | ## Why this matters
-- |
-- | JavaScript strings are UTF-16 encoded. Characters outside the BMP
-- | (Basic Multilingual Plane) are represented as surrogate pairs.
-- | Using CodeUnits.toCharArray would incorrectly split these into two
-- | separate "characters", breaking emoji and other supplementary characters.
-- |
-- | CodePoints.toCodePointArray correctly identifies surrogate pairs and
-- | returns the actual Unicode codepoint values.
stringToCodepoints :: String -> Array Int
stringToCodepoints str = mapArray codePointToInt (SCP.toCodePointArray str)

-- | Convert CodePoint to Int codepoint value
-- | Uses Data.Enum.fromEnum which extracts the numeric value from CodePoint
codePointToInt :: SCP.CodePoint -> Int
codePointToInt = Enum.fromEnum

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // numeric conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber i = intToNumberGo i 0.0

intToNumberGo :: Int -> Number -> Number
intToNumberGo i acc
  | i <= 0 = acc
  | true = intToNumberGo (i - 1) (acc + 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // array utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map over array
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldlArray (\acc x -> acc <> [f x]) []

-- | Fold left
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr = case Array.take 1 arr of
  [] -> init
  [x] -> foldlArray f (f init x) (Array.drop 1 arr)
  _ -> init

-- | Get array length
arrayLength :: forall a. Array a -> Int
arrayLength = Array.length

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // glyph utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum advance widths
sumAdvances :: Array ShapedGlyph -> Number
sumAdvances = foldlArray (\acc g -> acc + g.advanceWidth) 0.0

-- | Check if codepoint is a space character
-- |
-- | Recognizes:
-- | - U+0020: Space
-- | - U+0009: Tab
-- | - U+000A: Line Feed
-- | - U+000D: Carriage Return
isSpace :: Int -> Boolean
isSpace cp = cp == 32 || cp == 9 || cp == 10 || cp == 13
