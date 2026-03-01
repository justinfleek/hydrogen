-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // text // code
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Code — Code editor document model with syntax highlighting support.
-- |
-- | ## Design Philosophy
-- |
-- | Code documents are structured differently from rich text:
-- | - Line-oriented (not block-oriented)
-- | - Syntax-aware (tokens, not formatting)
-- | - Multi-cursor native (code editors expect this)
-- | - Indentation-sensitive
-- |
-- | This module re-exports all Code submodules for convenient access.
-- | The pure data model lives in submodules; syntax highlighting is performed
-- | by the target-specific renderer.
-- |
-- | ## Submodules
-- |
-- | - Token: Syntax token types and values
-- | - Line: Single line in a document
-- | - Cursor: Cursor position and selection
-- | - Document: Complete document and operations
-- | - Indentation: Indent style and operations
-- | - LineEnding: Line ending normalization
-- | - Folding: Code folding regions
-- | - Diagnostic: Error/warning messages
-- |
-- | ## Dependencies
-- |
-- | This is a leader module — it re-exports submodules only.

module Hydrogen.Schema.Text.Code
  ( -- * Token Types (from Code.Token)
    module Hydrogen.Schema.Text.Code.Token
  
  -- * Line Types (from Code.Line)
  , module Hydrogen.Schema.Text.Code.Line
  
  -- * Cursor Types (from Code.Cursor)
  , module Hydrogen.Schema.Text.Code.Cursor
  
  -- * Document Types (from Code.Document)
  , module Hydrogen.Schema.Text.Code.Document
  
  -- * Indentation (from Code.Indentation)
  , module Hydrogen.Schema.Text.Code.Indentation
  
  -- * Line Endings (from Code.LineEnding)
  , module Hydrogen.Schema.Text.Code.LineEnding
  
  -- * Folding (from Code.Folding)
  , module Hydrogen.Schema.Text.Code.Folding
  
  -- * Diagnostics (from Code.Diagnostic)
  , module Hydrogen.Schema.Text.Code.Diagnostic
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Text.Code.Token
  ( TokenType
      ( TokKeyword
      , TokKeywordControl
      , TokKeywordOperator
      , TokIdentifier
      , TokFunction
      , TokFunctionCall
      , TokType
      , TokTypeParameter
      , TokNamespace
      , TokClass
      , TokInterface
      , TokEnum
      , TokEnumMember
      , TokProperty
      , TokParameter
      , TokVariable
      , TokConstant
      , TokString
      , TokStringEscape
      , TokStringInterp
      , TokNumber
      , TokBoolean
      , TokNull
      , TokRegexp
      , TokOperator
      , TokPunctuation
      , TokBracket
      , TokComment
      , TokCommentBlock
      , TokCommentDoc
      , TokTag
      , TokTagAttribute
      , TokMacro
      , TokLabel
      , TokInvalid
      , TokPlain
      )
  , isKeyword
  , isString
  , isNumber
  , isComment
  , isOperator
  , isPunctuation
  , Token
  , token
  , tokenType
  , tokenStart
  , tokenEnd
  , tokenText
  , tokenLength
  )

import Hydrogen.Schema.Text.Code.Line
  ( CodeLine
  , codeLine
  , lineContent
  , lineTokens
  , lineNumber
  , lineIndentation
  , isLineEmpty
  , isLineWhitespace
  )

import Hydrogen.Schema.Text.Code.Cursor
  ( Cursor
  , cursor
  , cursorPosition
  , cursorSelection
  , cursorIsCollapsed
  , cursorLine
  , cursorColumn
  )

import Hydrogen.Schema.Text.Code.Document
  ( CodeDocument
  , codeDocument
  , emptyCodeDocument
  , documentContent
  , documentLanguage
  , documentCursors
  , setContent
  , setLanguage
  , setCursors
  , documentLines
  , documentLineCount
  , getLine
  , setLine
  , insertLine
  , deleteLine
  , splitLine
  , joinLines
  , insertTextAt
  , deleteTextAt
  , replaceTextAt
  , getTextInRange
  )

import Hydrogen.Schema.Text.Code.Indentation
  ( IndentStyle(IndentSpaces, IndentTabs)
  , IndentSize(IndentSize)
  , indentSize
  , unwrapIndentSize
  , detectIndentation
  , indentLine
  , outdentLine
  , normalizeIndentation
  )

import Hydrogen.Schema.Text.Code.LineEnding
  ( LineEnding(LineLF, LineCRLF, LineCR)
  , detectLineEnding
  , normalizeLineEndings
  )

import Hydrogen.Schema.Text.Code.Folding
  ( FoldRegion
  , foldRegion
  , foldStart
  , foldEnd
  , isFolded
  , toggleFold
  )

import Hydrogen.Schema.Text.Code.Diagnostic
  ( DiagnosticSeverity
      ( SeverityError
      , SeverityWarning
      , SeverityInfo
      , SeverityHint
      )
  , Diagnostic
  , diagnostic
  , diagnosticLine
  , diagnosticColumn
  , diagnosticMessage
  , diagnosticSeverity
  )
