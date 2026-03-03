-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // scraper // parse
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CSS string parsers that convert raw computed styles to Schema atoms.
-- |
-- | ## Purpose
-- |
-- | Browsers return computed styles as strings. This module provides pure
-- | parsers that convert those strings to bounded Schema atoms:
-- |
-- | - `"rgb(255, 128, 64)"` → `OKLCH { l, c, h }`
-- | - `"16px"` → `Pixel 16.0`
-- | - `"700"` → `FontWeight 700`
-- |
-- | ## Design
-- |
-- | All parsers return `Maybe` — invalid CSS produces `Nothing` rather than
-- | crashing. This is essential for scraping arbitrary websites where CSS
-- | may be malformed or use values we don't support.

module Hydrogen.Scraper.Parse
  ( -- * Dimension parsers
    parsePixels
    
  -- * Typography parsers
  , parseFontWeight
  , parseLineHeight
  
  -- * Elevation parsers
  , parseZIndex
  
  -- * Color parsers
  , parseRgbColor
  ) where

import Prelude
  ( bind
  , map
  , pure
  , ($)
  , (==)
  , (<)
  , (-)
  )

import Data.Array (index)
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (Pattern(Pattern), split, trim, length, take, drop) as String
import Data.String.CodeUnits (dropRight) as StringCU
import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB as RGB
import Data.Number (fromString) as Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // dimension parsers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse a CSS pixel value like "16px" or "24.5px"
-- |
-- | Returns Nothing for:
-- | - Empty strings
-- | - Non-pixel units (em, rem, %)
-- | - Invalid numbers
parsePixels :: String -> Maybe Number
parsePixels str =
  let len = String.length str
  in if len < 3
    then Nothing
    else
      let suffix = String.drop (len - 2) str
          numStr = StringCU.dropRight 2 str
      in if suffix == "px"
        then Number.fromString numStr
        else Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // typography parsers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse a CSS font-weight value
-- |
-- | CSS computed font-weight is always a number (100-900 typically).
-- | Keywords like "bold" are resolved to numeric values by the browser.
parseFontWeight :: String -> Maybe Int
parseFontWeight = Int.fromString

-- | Parse a CSS line-height value
-- |
-- | Computed line-height is either:
-- | - "normal" → returns Nothing (let caller use default)
-- | - A pixel value like "24px" → convert to ratio if font-size known
-- | - A unitless number like "1.5" → direct ratio
parseLineHeight :: String -> Maybe Number
parseLineHeight str =
  if str == "normal"
    then Nothing
    else case parsePixels str of
      Just px -> Just px  -- Caller must convert to ratio with font-size
      Nothing -> Number.fromString str  -- Try unitless number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // elevation parsers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse a CSS z-index value
-- |
-- | CSS computed z-index is either:
-- | - "auto" → returns Nothing
-- | - An integer like "100" or "-5"
parseZIndex :: String -> Maybe Int
parseZIndex str =
  if str == "auto"
    then Nothing
    else Int.fromString str

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // color parsers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse a CSS rgb() or rgba() color value
-- |
-- | Handles formats:
-- | - "rgb(255, 128, 64)"
-- | - "rgba(255, 128, 64, 0.5)"
-- | - "transparent" → returns Nothing
-- |
-- | Returns the RGB component (alpha is discarded for now).
parseRgbColor :: String -> Maybe RGB
parseRgbColor str =
  if str == "transparent" 
    then Nothing
    else if hasPrefix "rgba(" str
      then parseRgbaInner (extractInner 5 str)
      else if hasPrefix "rgb(" str
        then parseRgbInner (extractInner 4 str)
        else Nothing

-- | Check if string starts with prefix
hasPrefix :: String -> String -> Boolean
hasPrefix prefix str = String.take (String.length prefix) str == prefix

-- | Extract inner content: "rgb(1,2,3)" → "1,2,3"
extractInner :: Int -> String -> String
extractInner prefixLen str = 
  StringCU.dropRight 1 (String.drop prefixLen str)

-- | Parse "r, g, b" into RGB
parseRgbInner :: String -> Maybe RGB
parseRgbInner inner =
  let parts = String.split (String.Pattern ",") inner
      trimmed = map String.trim parts
  in case index trimmed 0, index trimmed 1, index trimmed 2 of
    Just rStr, Just gStr, Just bStr ->
      case Int.fromString rStr, Int.fromString gStr, Int.fromString bStr of
        Just r, Just g, Just b -> Just (RGB.rgb r g b)
        _, _, _ -> Nothing
    _, _, _ -> Nothing

-- | Parse "r, g, b, a" into RGB (ignoring alpha)
parseRgbaInner :: String -> Maybe RGB
parseRgbaInner = parseRgbInner  -- Same logic, alpha is 4th param and ignored
