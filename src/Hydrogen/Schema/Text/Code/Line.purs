-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // text // code // line
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Line — A single line in a code document.
-- |
-- | ## Design Philosophy
-- |
-- | Code documents are line-oriented. Each line stores:
-- | - Raw text content
-- | - Syntax tokens (lazily computed or cached)
-- | - Line number for reference
-- |
-- | Lines are immutable values. Editing creates new lines.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Data.String
-- | - Hydrogen.Schema.Text.Code.Token

module Hydrogen.Schema.Text.Code.Line
  ( -- * Line Type
    CodeLine
  , codeLine
  , lineContent
  , lineTokens
  , lineNumber
  , lineIndentation
  , isLineEmpty
  , isLineWhitespace
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (==)
  , (||)
  )

import Data.String as String

import Hydrogen.Schema.Text.Code.Token (Token)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // code line
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single line in a code document.
-- |
-- | Lines store both raw content and tokenized form. Tokens may be
-- | lazily computed or cached.
type CodeLine =
  { content :: String
  , tokens :: Array Token     -- ^ Syntax tokens (may be empty if not tokenized)
  , lineNum :: Int            -- ^ 0-indexed line number
  }

-- | Create a code line.
codeLine :: String -> Int -> CodeLine
codeLine content' num =
  { content: content'
  , tokens: []
  , lineNum: num
  }

-- | Get line content.
lineContent :: CodeLine -> String
lineContent l = l.content

-- | Get line tokens.
lineTokens :: CodeLine -> Array Token
lineTokens l = l.tokens

-- | Get line number.
lineNumber :: CodeLine -> Int
lineNumber l = l.lineNum

-- | Get indentation level (leading whitespace count).
lineIndentation :: CodeLine -> Int
lineIndentation l = countLeadingWhitespace 0 l.content
  where
    countLeadingWhitespace :: Int -> String -> Int
    countLeadingWhitespace acc s =
      let first = String.take 1 s
          rest = String.drop 1 s
      in if first == " " || first == "\t"
           then countLeadingWhitespace (acc + 1) rest
           else acc

-- | Check if line is empty.
isLineEmpty :: CodeLine -> Boolean
isLineEmpty l = String.null l.content

-- | Check if line is only whitespace.
isLineWhitespace :: CodeLine -> Boolean
isLineWhitespace l = String.null (String.trim l.content)
