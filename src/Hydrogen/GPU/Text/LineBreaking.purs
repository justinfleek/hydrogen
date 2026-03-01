-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // text
--                                                             // line breaking
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Line Breaking — Splitting text into lines that fit within bounds
-- |
-- | Implements greedy line breaking at word boundaries. For better
-- | typography, consider Knuth-Plass optimal line breaking.
-- |
-- | ## Algorithm
-- |
-- | 1. Split glyphs into words at space boundaries
-- | 2. Accumulate words into lines until maxWidth exceeded
-- | 3. Start new line when next word would exceed width
-- | 4. Reposition glyphs per line (reset x to 0, offset y by lineHeight)
-- |
-- | ## Dependencies
-- | - Hydrogen.GPU.Text.Types
-- | - Hydrogen.GPU.Text.Internal

module Hydrogen.GPU.Text.LineBreaking
  ( breakLines
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (*)
  , (<=)
  , (==)
  , (<>)
  )

import Data.HeytingAlgebra (disj) as HeytingAlgebra

import Data.Array (take, drop) as Array

import Hydrogen.GPU.Text.Types
  ( ShapedGlyph
  , ShapedText
  , LineBreakResult
  )
import Hydrogen.GPU.Text.Internal
  ( intToNumber
  , foldlArray
  , arrayLength
  , isSpace
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // line breaking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Break shaped text into lines that fit within maxWidth
-- |
-- | Uses greedy line breaking at word boundaries (spaces).
-- | Algorithm:
-- | 1. Split glyphs into words at space boundaries
-- | 2. Accumulate words into lines until maxWidth exceeded
-- | 3. Start new line when next word would exceed width
-- | 4. Reposition glyphs per line (reset x to 0, offset y by lineHeight)
-- |
-- | For better typography, consider Knuth-Plass optimal line breaking.
breakLines :: Number -> ShapedText -> LineBreakResult
breakLines maxWidth shaped =
  if shaped.totalWidth <= maxWidth
  then
    -- Text fits on single line, no breaking needed
    { lines: [shaped], totalHeight: shaped.lineHeight }
  else
    let
      -- Split into words (groups of non-space glyphs)
      words = splitIntoWords shaped.glyphs
      
      -- Build lines greedily
      builtLines = buildLines maxWidth shaped.lineHeight words
      
      -- Count lines for height calculation
      lineCount = arrayLength builtLines
      totalHeight = shaped.lineHeight * intToNumber lineCount
    in
      { lines: builtLines, totalHeight }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // word splitting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Split glyphs into words at space boundaries
splitIntoWords :: Array ShapedGlyph -> Array (Array ShapedGlyph)
splitIntoWords glyphs = splitWordsGo glyphs [] []

splitWordsGo 
  :: Array ShapedGlyph 
  -> Array ShapedGlyph          -- Current word accumulator
  -> Array (Array ShapedGlyph)  -- Completed words
  -> Array (Array ShapedGlyph)
splitWordsGo glyphs currentWord completedWords =
  case Array.take 1 glyphs of
    [] -> 
      -- End of input: finalize current word if non-empty
      if arrayLength currentWord == 0
      then completedWords
      else completedWords <> [currentWord]
    [g] ->
      let rest = Array.drop 1 glyphs in
      if isSpace g.codepoint
      then
        -- Space: finalize current word, skip the space
        if arrayLength currentWord == 0
        then splitWordsGo rest [] completedWords
        else splitWordsGo rest [] (completedWords <> [currentWord])
      else
        -- Non-space: add to current word
        splitWordsGo rest (currentWord <> [g]) completedWords
    _ -> completedWords  -- Should not happen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // line building
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build lines from words using greedy algorithm
buildLines :: Number -> Number -> Array (Array ShapedGlyph) -> Array ShapedText
buildLines maxWidth lineHeight words = buildLinesGo maxWidth lineHeight words 0.0 0.0 [] []

buildLinesGo
  :: Number                     -- maxWidth
  -> Number                     -- lineHeight  
  -> Array (Array ShapedGlyph)  -- remaining words
  -> Number                     -- current x position
  -> Number                     -- current y position
  -> Array ShapedGlyph          -- current line glyphs
  -> Array ShapedText           -- completed lines
  -> Array ShapedText
buildLinesGo maxWidth lineHeight words x y currentLineGlyphs completedLines =
  case Array.take 1 words of
    [] ->
      -- No more words: finalize current line if non-empty
      if arrayLength currentLineGlyphs == 0
      then completedLines
      else 
        let finalLine = makeShapedText currentLineGlyphs lineHeight
        in completedLines <> [finalLine]
    [word] ->
      let 
        rest = Array.drop 1 words
        wordWidth = sumWordAdvances word
        spaceWidth = if arrayLength currentLineGlyphs == 0 then 0.0 else 4.0  -- Inter-word space
        neededWidth = x + spaceWidth + wordWidth
      in
      if HeytingAlgebra.disj (neededWidth <= maxWidth) (arrayLength currentLineGlyphs == 0)
      then
        -- Word fits on current line (or current line is empty, so must add anyway)
        let 
          newX = if arrayLength currentLineGlyphs == 0 then 0.0 else x + spaceWidth
          repositionedWord = repositionGlyphs newX y word
          newGlyphs = currentLineGlyphs <> repositionedWord
          finalX = newX + wordWidth
        in
        buildLinesGo maxWidth lineHeight rest finalX y newGlyphs completedLines
      else
        -- Word doesn't fit: wrap to new line
        let
          finishedLine = makeShapedText currentLineGlyphs lineHeight
          newY = y + lineHeight
          repositionedWord = repositionGlyphs 0.0 newY word
        in
        buildLinesGo maxWidth lineHeight rest wordWidth newY repositionedWord (completedLines <> [finishedLine])
    _ -> completedLines  -- Should not happen

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reposition glyphs to start at given x, y
repositionGlyphs :: Number -> Number -> Array ShapedGlyph -> Array ShapedGlyph
repositionGlyphs startX startY glyphs = repositionGo startX startY glyphs []

repositionGo :: Number -> Number -> Array ShapedGlyph -> Array ShapedGlyph -> Array ShapedGlyph
repositionGo x y glyphs acc =
  case Array.take 1 glyphs of
    [] -> acc
    [g] ->
      let 
        rest = Array.drop 1 glyphs
        newGlyph = g { x = x, y = y }
        newX = x + g.advanceWidth
      in
      repositionGo newX y rest (acc <> [newGlyph])
    _ -> acc

-- | Sum advance widths of glyphs in a word
sumWordAdvances :: Array ShapedGlyph -> Number
sumWordAdvances = foldlArray (\acc g -> acc + g.advanceWidth) 0.0

-- | Create ShapedText from glyphs
makeShapedText :: Array ShapedGlyph -> Number -> ShapedText
makeShapedText glyphs lineHeight =
  { glyphs
  , totalWidth: sumWordAdvances glyphs
  , lineHeight
  , baseline: lineHeight * 0.8  -- Approximate baseline
  }
