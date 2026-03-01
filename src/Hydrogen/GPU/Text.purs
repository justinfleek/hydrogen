-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // gpu // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Rendering Pipeline — String to DrawCommand
-- |
-- | Bridges text strings to GPU rendering via the glyph geometry system.
-- | Uses FontMetrics for sizing, GlyphGeometry for shapes, and produces
-- | DrawGlyph/DrawWord commands for the GPU.
-- |
-- | ## Typography Pipeline
-- |
-- | ```
-- | String + FontConfig
-- |     ↓ shapeText
-- | ShapedText (positioned glyphs)
-- |     ↓ textToCommands
-- | Array (DrawCommand msg)
-- | ```
-- |
-- | ## Key Concepts
-- |
-- | - **Font Atlas**: Registry of loaded fonts with metrics + glyph data
-- | - **Shaping**: Converting codepoints to positioned glyphs (handles kerning, ligatures)
-- | - **Line Breaking**: Splitting text into lines that fit within width
-- | - **Baseline Alignment**: Positioning glyphs on the typographic baseline
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Types`: Core data types (FontConfig, FontAtlas, ShapedText, etc.)
-- | - `Shaping`: Text shaping (shapeText)
-- | - `LineBreaking`: Line breaking algorithm (breakLines)
-- | - `Operations`: Text manipulation (truncateText, filterVisibleGlyphs, etc.)
-- | - `Commands`: GPU command generation (textToCommands, shapedToCommands)
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Typography.FontMetrics
-- | - Hydrogen.Schema.Typography.GlyphGeometry
-- | - Hydrogen.GPU.DrawCommand
-- | - Hydrogen.GPU.GlyphConvert

module Hydrogen.GPU.Text
  ( module Types
  , module Shaping
  , module LineBreaking
  , module Operations
  , module Commands
  ) where

import Hydrogen.GPU.Text.Types 
  ( CachedGlyph
  , FontAtlas
  , FontConfig
  , GlyphCache
  , LineBreakResult
  , RegisteredFont
  , ShapedGlyph
  , ShapedText
  , cacheGlyph
  , emptyAtlas
  , emptyGlyphCache
  , fontConfig
  , lookupFont
  , lookupGlyph
  , registerFont
  ) as Types

import Hydrogen.GPU.Text.Shaping 
  ( shapeText
  ) as Shaping

import Hydrogen.GPU.Text.LineBreaking 
  ( breakLines
  ) as LineBreaking

import Hydrogen.GPU.Text.Operations 
  ( filterVisibleGlyphs
  , glyphBefore
  , glyphsEqual
  , glyphsInBounds
  , sortGlyphsByPosition
  , truncateText
  ) as Operations

import Hydrogen.GPU.Text.Commands 
  ( shapedToCommands
  , textToCommands
  ) as Commands
