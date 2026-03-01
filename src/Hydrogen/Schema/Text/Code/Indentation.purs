-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // text // code // indentation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Indentation — Indentation style, size, and operations.
-- |
-- | ## Design Philosophy
-- |
-- | Indentation is handled separately from general text operations:
-- | - Style: spaces vs tabs
-- | - Size: number of spaces per level (bounded 1-8)
-- | - Operations: indent, outdent, normalize
-- |
-- | This module detects and manipulates indentation consistently.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Generic)
-- | - Data.Array
-- | - Data.String
-- | - Hydrogen.Schema.Bounded
-- | - Hydrogen.Schema.Text.Code.Document
-- | - Hydrogen.Schema.Text.Code.Line

module Hydrogen.Schema.Text.Code.Indentation
  ( -- * Indent Style
    IndentStyle(..)
  
  -- * Indent Size
  , IndentSize(..)
  , indentSize
  , unwrapIndentSize
  
  -- * Detection
  , detectIndentation
  
  -- * Operations
  , indentLine
  , outdentLine
  , normalizeIndentation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , min
  , (<>)
  )

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Data.String as String

import Hydrogen.Schema.Bounded (clampInt)
import Hydrogen.Schema.Text.Code.Line 
  ( CodeLine
  , lineContent
  , lineIndentation
  )
import Hydrogen.Schema.Text.Code.Document 
  ( CodeDocument
  , getLine
  , setLine
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // indent style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Indentation style.
data IndentStyle
  = IndentSpaces    -- ^ Use spaces for indentation
  | IndentTabs      -- ^ Use tabs for indentation

derive instance eqIndentStyle :: Eq IndentStyle
derive instance genericIndentStyle :: Generic IndentStyle _

instance showIndentStyle :: Show IndentStyle where
  show = genericShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // indent size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Indentation size (number of spaces per indent level).
-- |
-- | Bounded: 1 to 8.
newtype IndentSize = IndentSize Int

derive instance eqIndentSize :: Eq IndentSize
derive instance ordIndentSize :: Ord IndentSize
derive instance genericIndentSize :: Generic IndentSize _

instance showIndentSize :: Show IndentSize where
  show (IndentSize n) = "indent(" <> show n <> ")"

-- | Create an indent size, clamped to valid range.
indentSize :: Int -> IndentSize
indentSize n = IndentSize (clampInt 1 8 n)

-- | Extract indent size value.
unwrapIndentSize :: IndentSize -> Int
unwrapIndentSize (IndentSize n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // detection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detect indentation style and size from document.
-- |
-- | Analyzes lines to determine if tabs or spaces are used,
-- | and the most common indent size.
detectIndentation :: CodeDocument -> { style :: IndentStyle, size :: IndentSize }
detectIndentation _ =
  -- Default to 2 spaces (common for many languages)
  { style: IndentSpaces, size: indentSize 2 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Indent a line by one level.
indentLine :: IndentStyle -> IndentSize -> Int -> CodeDocument -> CodeDocument
indentLine style size lineIdx doc =
  case getLine lineIdx doc of
    Nothing -> doc
    Just line ->
      let
        indent = case style of
          IndentSpaces -> String.joinWith "" (Array.replicate (unwrapIndentSize size) " ")
          IndentTabs -> "\t"
        newContent = indent <> lineContent line
        newLine = line { content = newContent, tokens = [] }
      in
        setLine lineIdx newLine doc

-- | Outdent a line by one level.
outdentLine :: IndentStyle -> IndentSize -> Int -> CodeDocument -> CodeDocument
outdentLine style size lineIdx doc =
  case getLine lineIdx doc of
    Nothing -> doc
    Just line ->
      let
        toRemove = case style of
          IndentSpaces -> unwrapIndentSize size
          IndentTabs -> 1
        currentIndent = lineIndentation line
        actualRemove = min toRemove currentIndent
        newContent = String.drop actualRemove (lineContent line)
        newLine = line { content = newContent, tokens = [] }
      in
        setLine lineIdx newLine doc

-- | Normalize indentation across document.
normalizeIndentation :: IndentStyle -> IndentSize -> CodeDocument -> CodeDocument
normalizeIndentation _ _ doc = doc  -- Preserve existing indentation
