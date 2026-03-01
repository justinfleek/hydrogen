-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // text
--                                                               // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Operations — Manipulation and query functions for shaped text
-- |
-- | Provides utilities for:
-- | - Truncation: Cutting text to fit within bounds
-- | - Filtering: Culling off-screen glyphs
-- | - Comparison: Testing glyph equality and ordering
-- | - Sorting: Arranging glyphs by position
-- |
-- | ## Dependencies
-- | - Hydrogen.GPU.Text.Types
-- | - Hydrogen.GPU.Text.Internal

module Hydrogen.GPU.Text.Operations
  ( -- * Truncation
    truncateText
  
  -- * Filtering
  , filterVisibleGlyphs
  , glyphsInBounds
  
  -- * Comparison
  , glyphsEqual
  , glyphBefore
  
  -- * Sorting
  , sortGlyphsByPosition
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (+)
  , (<)
  , (<=)
  , (==)
  , (>=)
  , (<>)
  , (&&)
  )

import Data.Array (filter, take, drop) as Array

import Hydrogen.GPU.Text.Types
  ( ShapedGlyph
  , ShapedText
  )
import Hydrogen.GPU.Text.Internal
  ( sumAdvances
  , foldlArray
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // truncation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Truncate shaped text to fit within maxWidth
-- |
-- | Removes glyphs that extend beyond maxWidth. If truncation occurs,
-- | the text is cut at the last glyph that fully fits. For ellipsis
-- | truncation, the caller should append "..." to the truncated text.
-- |
-- | Uses comparison operators (>, >=, <) for bounds checking.
truncateText :: Number -> ShapedText -> ShapedText
truncateText maxWidth shaped =
  if shaped.totalWidth <= maxWidth
  then shaped  -- No truncation needed
  else
    let
      -- Keep glyphs whose right edge (x + width) is within bounds
      truncated = truncateGlyphsAt maxWidth shaped.glyphs
      newWidth = sumAdvances truncated
    in
      shaped { glyphs = truncated, totalWidth = newWidth }

-- | Truncate glyphs at a given x boundary
truncateGlyphsAt :: Number -> Array ShapedGlyph -> Array ShapedGlyph
truncateGlyphsAt maxX glyphs = truncateGo maxX glyphs []

truncateGo :: Number -> Array ShapedGlyph -> Array ShapedGlyph -> Array ShapedGlyph
truncateGo maxX glyphs acc =
  case Array.take 1 glyphs of
    [] -> acc
    [g] ->
      let 
        rest = Array.drop 1 glyphs
        rightEdge = g.x + g.width
      in
      if rightEdge <= maxX
      then truncateGo maxX rest (acc <> [g])
      else acc  -- This glyph exceeds bounds, stop here
    _ -> acc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter glyphs to only those currently visible
-- |
-- | Removes glyphs that are completely outside the visible region.
-- | Useful for culling off-screen text in scrolling views.
-- |
-- | Uses Data.Array.filter for efficient predicate-based selection.
filterVisibleGlyphs :: { x :: Number, y :: Number, width :: Number, height :: Number } -> ShapedText -> ShapedText
filterVisibleGlyphs bounds shaped =
  let
    visible = Array.filter (isGlyphVisible bounds) shaped.glyphs
    newWidth = sumAdvances visible
  in
    shaped { glyphs = visible, totalWidth = newWidth }

-- | Check if a glyph is at least partially visible within bounds
isGlyphVisible :: { x :: Number, y :: Number, width :: Number, height :: Number } -> ShapedGlyph -> Boolean
isGlyphVisible bounds glyph =
  let
    glyphRight = glyph.x + glyph.width
    glyphBottom = glyph.y + glyph.height
    boundsRight = bounds.x + bounds.width
    boundsBottom = bounds.y + bounds.height
  in
  -- Check for intersection (not complete exclusion)
  -- Glyph is visible if it overlaps the bounds rectangle
  glyphRight >= bounds.x &&        -- Glyph extends into or past left edge
  glyph.x < boundsRight &&         -- Glyph starts before right edge
  glyphBottom >= bounds.y &&       -- Glyph extends into or past top edge
  glyph.y < boundsBottom           -- Glyph starts before bottom edge

-- | Get glyphs within a bounding box
-- |
-- | Returns glyphs that intersect with the given bounds rectangle.
-- | This is useful for hit testing (finding which glyphs are under a point)
-- | and for partial text rendering (only render visible portion).
glyphsInBounds :: { x :: Number, y :: Number, width :: Number, height :: Number } -> ShapedText -> Array ShapedGlyph
glyphsInBounds bounds shaped = Array.filter (isGlyphVisible bounds) shaped.glyphs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two ShapedGlyph records for equality
-- |
-- | Two glyphs are equal if they have the same codepoint at the same position.
-- | Uses the Eq typeclass for Number comparison.
glyphsEqual :: ShapedGlyph -> ShapedGlyph -> Boolean
glyphsEqual g1 g2 =
  g1.codepoint == g2.codepoint &&
  g1.x == g2.x &&
  g1.y == g2.y

-- | Compare two ShapedGlyph records by position
-- |
-- | Compares glyphs by their x position for left-to-right ordering.
-- | Uses the Ord typeclass (via < operator) for Number comparison.
-- | Returns true if g1 comes before g2 in reading order.
glyphBefore :: ShapedGlyph -> ShapedGlyph -> Boolean
glyphBefore g1 g2 = g1.x < g2.x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // sorting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort glyphs by position (left to right)
-- |
-- | Uses a simple insertion sort for small arrays.
-- | For text that's already shaped left-to-right, this is a no-op.
-- | Useful when glyphs have been repositioned or filtered.
sortGlyphsByPosition :: Array ShapedGlyph -> Array ShapedGlyph
sortGlyphsByPosition glyphs = insertionSort glyphBefore glyphs

-- | Generic insertion sort using a comparison function
-- |
-- | Uses the $ operator for clean function application.
-- | The Ord constraint is satisfied through the comparison function.
insertionSort :: forall a. (a -> a -> Boolean) -> Array a -> Array a
insertionSort before arr = foldlArray (\sorted x -> insertSorted before x sorted) [] arr

-- | Insert element into sorted array
insertSorted :: forall a. (a -> a -> Boolean) -> a -> Array a -> Array a
insertSorted before x sorted = insertGo before x sorted []

insertGo :: forall a. (a -> a -> Boolean) -> a -> Array a -> Array a -> Array a
insertGo before x remaining acc =
  case Array.take 1 remaining of
    [] -> acc <> [x]  -- End of array, append x
    [y] ->
      if before x y
      then acc <> [x] <> remaining  -- x goes before y
      else insertGo before x (Array.drop 1 remaining) $ acc <> [y]
    _ -> acc <> [x]  -- Should not happen
