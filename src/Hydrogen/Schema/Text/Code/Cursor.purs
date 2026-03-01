-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // text // code // cursor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cursor — Cursor position and selection in code documents.
-- |
-- | ## Design Philosophy
-- |
-- | Code editors support multi-cursor editing. Each cursor has:
-- | - A position (line and column)
-- | - An optional selection (anchor and focus)
-- |
-- | Cursors are immutable values. Movement creates new cursors.
-- |
-- | ## Dependencies
-- |
-- | - Data.Maybe
-- | - Hydrogen.Schema.Text.Selection

module Hydrogen.Schema.Text.Code.Cursor
  ( -- * Cursor Type
    Cursor
  , cursor
  , cursorPosition
  , cursorSelection
  , cursorIsCollapsed
  , cursorLine
  , cursorColumn
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (==)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Text.Selection 
  ( CodePosition
  , CodeSelection
  , unwrapLineNumber
  , unwrapColumn
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // cursor
-- ═════════════════════════════════════════════════════════════════════════════

-- | A cursor in the code document.
-- |
-- | Cursors have position and optional selection. Multiple cursors
-- | are supported for multi-cursor editing.
type Cursor =
  { position :: CodePosition
  , selection :: Maybe CodeSelection    -- ^ Selection if not collapsed
  }

-- | Create a cursor at a position.
cursor :: CodePosition -> Cursor
cursor pos =
  { position: pos
  , selection: Nothing
  }

-- | Get cursor position.
cursorPosition :: Cursor -> CodePosition
cursorPosition c = c.position

-- | Get cursor selection (if any).
cursorSelection :: Cursor -> Maybe CodeSelection
cursorSelection c = c.selection

-- | Check if cursor is collapsed (no selection).
cursorIsCollapsed :: Cursor -> Boolean
cursorIsCollapsed c = case c.selection of
  Nothing -> true
  Just sel -> sel.anchor == sel.focus

-- | Get cursor line number.
cursorLine :: Cursor -> Int
cursorLine c = unwrapLineNumber c.position.line

-- | Get cursor column.
cursorColumn :: Cursor -> Int
cursorColumn c = unwrapColumn c.position.column
