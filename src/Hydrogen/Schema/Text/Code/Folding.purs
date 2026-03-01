-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // text // code // folding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Folding — Code folding regions for collapsible sections.
-- |
-- | ## Design Philosophy
-- |
-- | Code editors support folding to hide sections of code:
-- | - Functions, classes, blocks can be collapsed
-- | - Fold regions are computed from syntax (indentation, braces, etc.)
-- | - Fold state is separate from document content
-- |
-- | This module provides the fold region type and toggle operations.
-- |
-- | ## Dependencies
-- |
-- | - None (self-contained)

module Hydrogen.Schema.Text.Code.Folding
  ( -- * Fold Region Type
    FoldRegion
  , foldRegion
  , foldStart
  , foldEnd
  , isFolded
  , toggleFold
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // fold region
-- ═════════════════════════════════════════════════════════════════════════════

-- | A foldable region in the code.
-- |
-- | Fold regions can be collapsed to hide their contents.
type FoldRegion =
  { startLine :: Int
  , endLine :: Int
  , folded :: Boolean
  }

-- | Create a fold region.
foldRegion :: Int -> Int -> Boolean -> FoldRegion
foldRegion start end folded' =
  { startLine: start
  , endLine: end
  , folded: folded'
  }

-- | Get fold start line.
foldStart :: FoldRegion -> Int
foldStart r = r.startLine

-- | Get fold end line.
foldEnd :: FoldRegion -> Int
foldEnd r = r.endLine

-- | Check if region is folded.
isFolded :: FoldRegion -> Boolean
isFolded r = r.folded

-- | Toggle fold state.
toggleFold :: FoldRegion -> FoldRegion
toggleFold r = r { folded = not r.folded }
  where
    not :: Boolean -> Boolean
    not true = false
    not false = true
