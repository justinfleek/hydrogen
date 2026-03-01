-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // text // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selection — Text selection model for rich text and code editing.
-- |
-- | ## Design Philosophy
-- |
-- | Selections in text editors are described by an anchor (where selection started)
-- | and a focus (where it currently ends). When anchor equals focus, the selection
-- | is a cursor (caret). When they differ, text is selected.
-- |
-- | ## Positions
-- |
-- | Positions are hierarchical addresses into a document:
-- | - Block index (which paragraph/heading/etc.)
-- | - Offset (character position within block)
-- |
-- | For code documents, positions are simpler:
-- | - Line number
-- | - Column (character offset in line)
-- |
-- | ## Selection Direction
-- |
-- | Selections have direction: forward (anchor before focus) or backward
-- | (focus before anchor). This matters for extending selections and for
-- | determining where the cursor appears visually.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Generic)
-- | - Schema.Bounded (bounded indices)

module Hydrogen.Schema.Text.Selection
  ( -- * Position Types
    BlockIndex(..)
  , blockIndex
  , unwrapBlockIndex
  , maxBlockIndex
  
  , CharOffset(..)
  , charOffset
  , unwrapCharOffset
  , maxCharOffset
  
  , LineNumber(..)
  , lineNumber
  , unwrapLineNumber
  , maxLineNumber
  
  , Column(..)
  , column
  , unwrapColumn
  , maxColumn
  
  -- * Position Records
  , Position
  , position
  , positionStart
  , comparePositions
  
  , CodePosition
  , codePosition
  , codePositionStart
  , compareCodePositions
  
  -- * Selection Types
  , Selection
  , selection
  , cursor
  , cursorAt
  , selectionAnchor
  , selectionFocus
  , selectionIsCollapsed
  , selectionIsForward
  , selectionIsBackward
  , normalizeSelection
  , extendSelection
  , collapseToAnchor
  , collapseToFocus
  
  , CodeSelection
  , codeSelection
  , codeCursor
  , codeCursorAt
  
  -- * Multi-cursor Support
  , MultiSelection
  , singleSelection
  , addSelection
  , removeSelection
  , primarySelection
  , allSelections
  , selectionsCount
  
  -- * Selection Ranges
  , SelectionRange
  , selectionRange
  , rangeStart
  , rangeEnd
  , rangeLength
  , positionsInRange
  , rangesOverlap
  , mergeRanges
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, GT, EQ)
  , show
  , compare
  , min
  , max
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (&&)
  , (||)
  , (+)
  , (-)
  , ($)
  , not
  , (*)
  )

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)

import Hydrogen.Schema.Bounded (clampInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bounded // indices
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum block index (65535 blocks per document).
maxBlockIndex :: Int
maxBlockIndex = 65535

-- | Maximum character offset within a block (16M characters).
maxCharOffset :: Int
maxCharOffset = 16777215

-- | Maximum line number in a code document (1M lines).
maxLineNumber :: Int
maxLineNumber = 1048575

-- | Maximum column in a code line (16K characters).
maxColumn :: Int
maxColumn = 16383

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // block index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Block index within a document.
-- |
-- | Zero-indexed position of a block (paragraph, heading, etc.).
-- | Bounded: 0 to maxBlockIndex.
newtype BlockIndex = BlockIndex Int

derive instance eqBlockIndex :: Eq BlockIndex
derive instance ordBlockIndex :: Ord BlockIndex
derive instance genericBlockIndex :: Generic BlockIndex _

instance showBlockIndex :: Show BlockIndex where
  show (BlockIndex n) = "block[" <> show n <> "]"

-- | Create a block index, clamped to valid range.
blockIndex :: Int -> BlockIndex
blockIndex n = BlockIndex (clampInt 0 maxBlockIndex n)

-- | Extract raw Int from BlockIndex.
unwrapBlockIndex :: BlockIndex -> Int
unwrapBlockIndex (BlockIndex n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // char offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Character offset within a block.
-- |
-- | Zero-indexed position of a character within inline content.
-- | Bounded: 0 to maxCharOffset.
newtype CharOffset = CharOffset Int

derive instance eqCharOffset :: Eq CharOffset
derive instance ordCharOffset :: Ord CharOffset
derive instance genericCharOffset :: Generic CharOffset _

instance showCharOffset :: Show CharOffset where
  show (CharOffset n) = "offset[" <> show n <> "]"

-- | Create a character offset, clamped to valid range.
charOffset :: Int -> CharOffset
charOffset n = CharOffset (clampInt 0 maxCharOffset n)

-- | Extract raw Int from CharOffset.
unwrapCharOffset :: CharOffset -> Int
unwrapCharOffset (CharOffset n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // line number
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line number in a code document.
-- |
-- | Zero-indexed line position.
-- | Bounded: 0 to maxLineNumber.
newtype LineNumber = LineNumber Int

derive instance eqLineNumber :: Eq LineNumber
derive instance ordLineNumber :: Ord LineNumber
derive instance genericLineNumber :: Generic LineNumber _

instance showLineNumber :: Show LineNumber where
  show (LineNumber n) = "line[" <> show n <> "]"

-- | Create a line number, clamped to valid range.
lineNumber :: Int -> LineNumber
lineNumber n = LineNumber (clampInt 0 maxLineNumber n)

-- | Extract raw Int from LineNumber.
unwrapLineNumber :: LineNumber -> Int
unwrapLineNumber (LineNumber n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // column
-- ═════════════════════════════════════════════════════════════════════════════

-- | Column (character offset) within a line.
-- |
-- | Zero-indexed character position in a line.
-- | Bounded: 0 to maxColumn.
newtype Column = Column Int

derive instance eqColumn :: Eq Column
derive instance ordColumn :: Ord Column
derive instance genericColumn :: Generic Column _

instance showColumn :: Show Column where
  show (Column n) = "col[" <> show n <> "]"

-- | Create a column, clamped to valid range.
column :: Int -> Column
column n = Column (clampInt 0 maxColumn n)

-- | Extract raw Int from Column.
unwrapColumn :: Column -> Int
unwrapColumn (Column n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // position // rich text
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position within a rich text document.
-- |
-- | Addresses a specific character within a specific block.
type Position =
  { blockIndex :: BlockIndex
  , offset :: CharOffset
  }

-- | Create a position.
position :: Int -> Int -> Position
position block off =
  { blockIndex: blockIndex block
  , offset: charOffset off
  }

-- | Position at the start of the document (block 0, offset 0).
positionStart :: Position
positionStart = position 0 0

-- | Compare two positions.
-- |
-- | Positions are ordered first by block, then by offset.
comparePositions :: Position -> Position -> Ordering
comparePositions p1 p2 =
  case compare p1.blockIndex p2.blockIndex of
    EQ -> compare p1.offset p2.offset
    other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // position // code
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position within a code document.
-- |
-- | Addresses a specific column within a specific line.
type CodePosition =
  { line :: LineNumber
  , column :: Column
  }

-- | Create a code position.
codePosition :: Int -> Int -> CodePosition
codePosition ln col =
  { line: lineNumber ln
  , column: column col
  }

-- | Position at the start of the code document (line 0, column 0).
codePositionStart :: CodePosition
codePositionStart = codePosition 0 0

-- | Compare two code positions.
compareCodePositions :: CodePosition -> CodePosition -> Ordering
compareCodePositions p1 p2 =
  case compare p1.line p2.line of
    EQ -> compare p1.column p2.column
    other -> other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // selection // rich text
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection in a rich text document.
-- |
-- | ## Anchor and Focus
-- |
-- | - Anchor: where the selection started (user clicked/tapped)
-- | - Focus: where the selection ends (current cursor position)
-- |
-- | When anchor == focus, the selection is collapsed (a cursor/caret).
-- | When anchor != focus, text between them is selected.
type Selection =
  { anchor :: Position
  , focus :: Position
  }

-- | Create a selection.
selection :: Position -> Position -> Selection
selection anchor focus =
  { anchor
  , focus
  }

-- | Create a collapsed selection (cursor) at a position.
cursor :: Position -> Selection
cursor pos = selection pos pos

-- | Create a cursor at block and offset.
cursorAt :: Int -> Int -> Selection
cursorAt block off = cursor (position block off)

-- | Get the anchor position.
selectionAnchor :: Selection -> Position
selectionAnchor sel = sel.anchor

-- | Get the focus position.
selectionFocus :: Selection -> Position
selectionFocus sel = sel.focus

-- | Check if selection is collapsed (cursor with no selected text).
selectionIsCollapsed :: Selection -> Boolean
selectionIsCollapsed sel =
  sel.anchor.blockIndex == sel.focus.blockIndex &&
  sel.anchor.offset == sel.focus.offset

-- | Check if selection is forward (anchor before focus).
selectionIsForward :: Selection -> Boolean
selectionIsForward sel =
  case comparePositions sel.anchor sel.focus of
    LT -> true
    _ -> false

-- | Check if selection is backward (focus before anchor).
selectionIsBackward :: Selection -> Boolean
selectionIsBackward sel =
  case comparePositions sel.anchor sel.focus of
    GT -> true
    _ -> false

-- | Normalize selection so anchor is always before or equal to focus.
-- |
-- | After normalization, the selection is always forward or collapsed.
normalizeSelection :: Selection -> Selection
normalizeSelection sel =
  case comparePositions sel.anchor sel.focus of
    GT -> { anchor: sel.focus, focus: sel.anchor }
    _ -> sel

-- | Extend selection to a new focus position.
extendSelection :: Position -> Selection -> Selection
extendSelection newFocus sel = sel { focus = newFocus }

-- | Collapse selection to the anchor position.
collapseToAnchor :: Selection -> Selection
collapseToAnchor sel = cursor sel.anchor

-- | Collapse selection to the focus position.
collapseToFocus :: Selection -> Selection
collapseToFocus sel = cursor sel.focus

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection // code
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection in a code document.
type CodeSelection =
  { anchor :: CodePosition
  , focus :: CodePosition
  }

-- | Create a code selection.
codeSelection :: CodePosition -> CodePosition -> CodeSelection
codeSelection anchor focus =
  { anchor
  , focus
  }

-- | Create a collapsed code selection (cursor).
codeCursor :: CodePosition -> CodeSelection
codeCursor pos = codeSelection pos pos

-- | Create a code cursor at line and column.
codeCursorAt :: Int -> Int -> CodeSelection
codeCursorAt ln col = codeCursor (codePosition ln col)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // multi-cursor // support
-- ═════════════════════════════════════════════════════════════════════════════

-- | Multiple simultaneous selections.
-- |
-- | Modern editors support multiple cursors. This type tracks all active
-- | selections, with the first being the "primary" selection.
-- |
-- | Invariant: selections array is never empty.
newtype MultiSelection = MultiSelection (Array Selection)

derive instance eqMultiSelection :: Eq MultiSelection
derive instance genericMultiSelection :: Generic MultiSelection _

instance showMultiSelection :: Show MultiSelection where
  show = genericShow

-- | Create a multi-selection with a single selection.
singleSelection :: Selection -> MultiSelection
singleSelection sel = MultiSelection [ sel ]

-- | Add a selection to the multi-selection.
-- |
-- | New selections are added at the end; the first remains primary.
addSelection :: Selection -> MultiSelection -> MultiSelection
addSelection sel (MultiSelection sels) = MultiSelection (Array.snoc sels sel)

-- | Remove a selection by index.
-- |
-- | If removing would leave zero selections, returns unchanged.
removeSelection :: Int -> MultiSelection -> MultiSelection
removeSelection idx (MultiSelection sels) =
  case Array.deleteAt idx sels of
    Nothing -> MultiSelection sels
    Just [] -> MultiSelection sels
    Just remaining -> MultiSelection remaining

-- | Get the primary (first) selection.
primarySelection :: MultiSelection -> Selection
primarySelection (MultiSelection sels) =
  case Array.head sels of
    Just sel -> sel
    Nothing -> cursor positionStart  -- Impossible by invariant

-- | Get all selections.
allSelections :: MultiSelection -> Array Selection
allSelections (MultiSelection sels) = sels

-- | Count of selections.
selectionsCount :: MultiSelection -> Int
selectionsCount (MultiSelection sels) = Array.length sels

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // selection // ranges
-- ═════════════════════════════════════════════════════════════════════════════

-- | A normalized range between two positions.
-- |
-- | Unlike Selection, SelectionRange is always normalized:
-- | start is always before or equal to end.
type SelectionRange =
  { start :: Position
  , end :: Position
  }

-- | Create a selection range from two positions.
-- |
-- | Automatically normalizes so start <= end.
selectionRange :: Position -> Position -> SelectionRange
selectionRange p1 p2 =
  case comparePositions p1 p2 of
    GT -> { start: p2, end: p1 }
    _ -> { start: p1, end: p2 }

-- | Get the start position of a range.
rangeStart :: SelectionRange -> Position
rangeStart r = r.start

-- | Get the end position of a range.
rangeEnd :: SelectionRange -> Position
rangeEnd r = r.end

-- | Calculate the approximate length of a range.
-- |
-- | For same-block ranges, this is exact. For multi-block ranges,
-- | this returns the character span which may not account for block boundaries.
rangeLength :: SelectionRange -> Int
rangeLength r =
  if r.start.blockIndex == r.end.blockIndex
    then unwrapCharOffset r.end.offset - unwrapCharOffset r.start.offset
    else
      let blocks = unwrapBlockIndex r.end.blockIndex - unwrapBlockIndex r.start.blockIndex
          startOffset = unwrapCharOffset r.start.offset
          endOffset = unwrapCharOffset r.end.offset
      in (blocks * 1000) + endOffset - startOffset  -- Approximate

-- | Check if a position is within a range (inclusive).
positionsInRange :: Position -> SelectionRange -> Boolean
positionsInRange pos range =
  case comparePositions pos range.start of
    LT -> false
    _ -> case comparePositions pos range.end of
      GT -> false
      _ -> true

-- | Check if two ranges overlap.
rangesOverlap :: SelectionRange -> SelectionRange -> Boolean
rangesOverlap r1 r2 =
  not (comparePositions r1.end r2.start == LT || comparePositions r2.end r1.start == LT)

-- | Merge two overlapping ranges.
-- |
-- | If ranges don't overlap, returns the union (gap included).
mergeRanges :: SelectionRange -> SelectionRange -> SelectionRange
mergeRanges r1 r2 =
  let
    minStart = case comparePositions r1.start r2.start of
      LT -> r1.start
      _ -> r2.start
    maxEnd = case comparePositions r1.end r2.end of
      GT -> r1.end
      _ -> r2.end
  in
    { start: minStart, end: maxEnd }
