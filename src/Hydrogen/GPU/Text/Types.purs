-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // text
--                                                                     // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for the Text Rendering Pipeline
-- |
-- | Defines all data structures used throughout the text rendering system:
-- | - Font configuration and atlas management
-- | - Glyph caching for geometry lookup
-- | - Shaped text with positioned glyphs
-- | - Line breaking results
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Typography.FontMetrics
-- | - Hydrogen.Schema.Typography.GlyphGeometry

module Hydrogen.GPU.Text.Types
  ( -- * Font Configuration
    FontConfig
  , fontConfig
  
  -- * Font Atlas
  , FontAtlas
  , RegisteredFont
  , emptyAtlas
  , registerFont
  , lookupFont
  
  -- * Glyph Cache
  , GlyphCache
  , CachedGlyph
  , emptyGlyphCache
  , cacheGlyph
  , lookupGlyph
  
  -- * Shaped Text
  , ShapedGlyph
  , ShapedText
  
  -- * Line Breaking
  , LineBreakResult
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  )

import Data.Maybe (Maybe)
import Data.Map (Map)
import Data.Map as Map

import Hydrogen.Schema.Typography.FontMetrics as FM
import Hydrogen.Schema.Typography.GlyphGeometry as GG

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // font configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font configuration for text rendering
-- |
-- | Specifies which font to use and at what size.
type FontConfig =
  { fontId :: Int
    -- ^ Index into the font atlas
  , fontSize :: Number
    -- ^ Size in pixels (corresponds to em-square height)
  , letterSpacing :: Number
    -- ^ Additional spacing between glyphs (can be negative)
  , lineHeight :: Number
    -- ^ Line height as multiplier of fontSize
  }

-- | Create default font configuration
fontConfig :: Int -> Number -> FontConfig
fontConfig fontId fontSize =
  { fontId
  , fontSize
  , letterSpacing: 0.0
  , lineHeight: 1.2  -- Standard 120% line height
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // font atlas
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registered font with metrics
type RegisteredFont =
  { fontId :: Int
  , name :: String
  , metrics :: FM.FontMetrics
  , glyphCache :: GlyphCache
  }

-- | Font atlas — registry of loaded fonts
-- |
-- | At runtime, fonts are loaded and registered here. Each font gets:
-- | - A unique fontId for referencing
-- | - Font metrics (ascender, descender, xHeight, etc.)
-- | - Glyph cache for geometry lookup
type FontAtlas =
  { fonts :: Map Int RegisteredFont
  , nextId :: Int
  }

-- | Empty font atlas
emptyAtlas :: FontAtlas
emptyAtlas = { fonts: Map.empty, nextId: 0 }

-- | Register a font in the atlas
-- |
-- | Returns the assigned fontId and updated atlas.
registerFont :: String -> FM.FontMetrics -> FontAtlas -> { fontId :: Int, atlas :: FontAtlas }
registerFont name metrics atlas =
  let
    fontId = atlas.nextId
    font = { fontId, name, metrics, glyphCache: emptyGlyphCache }
    newFonts = Map.insert fontId font atlas.fonts
  in
    { fontId
    , atlas: atlas { fonts = newFonts, nextId = fontId + 1 }
    }

-- | Look up a font by ID
lookupFont :: Int -> FontAtlas -> Maybe RegisteredFont
lookupFont fontId atlas = Map.lookup fontId atlas.fonts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // glyph cache
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cached glyph data
-- |
-- | Stores precomputed geometry and metrics for a single glyph.
type CachedGlyph =
  { codepoint :: Int
    -- ^ Unicode codepoint
  , geometry :: GG.GlyphPath
    -- ^ Vector path data
  , advanceWidth :: Number
    -- ^ Horizontal advance after this glyph (in font units)
  }

-- | Glyph cache — lookup table for glyph geometry
-- |
-- | Keyed by Unicode codepoint for O(log n) lookup.
type GlyphCache =
  { glyphs :: Map Int CachedGlyph
  }

-- | Empty glyph cache
emptyGlyphCache :: GlyphCache
emptyGlyphCache = { glyphs: Map.empty }

-- | Add a glyph to the cache
cacheGlyph :: Int -> GG.GlyphPath -> Number -> GlyphCache -> GlyphCache
cacheGlyph codepoint geometry advanceWidth cache =
  let
    glyph = { codepoint, geometry, advanceWidth }
  in
    cache { glyphs = Map.insert codepoint glyph cache.glyphs }

-- | Look up a glyph by codepoint
lookupGlyph :: Int -> GlyphCache -> Maybe CachedGlyph
lookupGlyph codepoint cache = Map.lookup codepoint cache.glyphs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // shaped text
-- ═════════════════════════════════════════════════════════════════════════════

-- | A shaped glyph with computed position
-- |
-- | After shaping, each glyph has:
-- | - Its codepoint and geometry reference
-- | - Computed x, y position (in pixels)
-- | - Size scaled to the requested fontSize
type ShapedGlyph =
  { codepoint :: Int
  , x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , advanceWidth :: Number
  , geometry :: Maybe GG.GlyphPath
  }

-- | Result of shaping a text string
type ShapedText =
  { glyphs :: Array ShapedGlyph
  , totalWidth :: Number
  , lineHeight :: Number
  , baseline :: Number
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // line breaking
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of line breaking
type LineBreakResult =
  { lines :: Array ShapedText
  , totalHeight :: Number
  }
