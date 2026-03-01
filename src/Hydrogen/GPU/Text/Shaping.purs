-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // text
--                                                                  // shaping
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Shaping — Converting strings to positioned glyphs
-- |
-- | Shaping is the process of converting a string of Unicode codepoints
-- | into positioned glyphs. This module implements simplified shaping
-- | without advanced OpenType features.
-- |
-- | ## Typography Pipeline
-- |
-- | ```
-- | String + FontConfig
-- |     ↓ shapeText
-- | ShapedText (positioned glyphs)
-- | ```
-- |
-- | ## Limitations
-- |
-- | This is simplified shaping without:
-- | - Kerning pairs
-- | - Ligature substitution (fi, fl, etc.)
-- | - Complex script handling (Arabic, Devanagari, etc.)
-- |
-- | For full shaping, integrate HarfBuzz via FFI at the system boundary.
-- |
-- | ## Dependencies
-- | - Hydrogen.GPU.Text.Types
-- | - Hydrogen.GPU.Text.Internal
-- | - Hydrogen.Schema.Typography.FontMetrics

module Hydrogen.GPU.Text.Shaping
  ( shapeText
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , ($)
  , (+)
  , (*)
  , (/)
  , (<>)
  )

import Data.Array (take, drop) as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Typography.FontMetrics as FM
import Hydrogen.GPU.Text.Types 
  ( FontConfig
  , FontAtlas
  , RegisteredFont
  , ShapedGlyph
  , ShapedText
  , lookupFont
  , lookupGlyph
  )
import Hydrogen.GPU.Text.Internal
  ( stringToCodepoints
  , intToNumber
  , sumAdvances
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text shaping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape text into positioned glyphs
-- |
-- | This is simplified shaping without:
-- | - Kerning pairs
-- | - Ligature substitution (fi, fl, etc.)
-- | - Complex script handling (Arabic, Devanagari, etc.)
-- |
-- | For full shaping, integrate HarfBuzz via FFI at the system boundary.
shapeText :: FontConfig -> FontAtlas -> String -> ShapedText
shapeText config atlas text =
  let
    codepoints = stringToCodepoints text
    font = lookupFont config.fontId atlas
    scale = case font of
      Nothing -> config.fontSize / 1000.0  -- Default UPM
      Just f -> config.fontSize / intToNumber (FM.getUnitsPerEm f.metrics)
    
    -- Position each glyph
    shaped = shapeGlyphs config scale font codepoints
    
    -- Compute totals
    totalWidth = sumAdvances shaped
    lineHeight = config.fontSize * config.lineHeight
    baseline = case font of
      Nothing -> config.fontSize * 0.8
      Just f -> config.fontSize * FM.ascenderRatio f.metrics
  in
    { glyphs: shaped
    , totalWidth
    , lineHeight
    , baseline
    }

-- | Shape glyphs with positioning
shapeGlyphs :: FontConfig -> Number -> Maybe RegisteredFont -> Array Int -> Array ShapedGlyph
shapeGlyphs config scale mFont codepoints =
  shapeGlyphsGo config scale mFont codepoints 0.0 []

shapeGlyphsGo 
  :: FontConfig 
  -> Number 
  -> Maybe RegisteredFont 
  -> Array Int 
  -> Number 
  -> Array ShapedGlyph 
  -> Array ShapedGlyph
shapeGlyphsGo config scale mFont codepoints x acc =
  case Array.take 1 codepoints of
    [] -> acc
    [cp] ->
      let
        rest = Array.drop 1 codepoints
        cached = case mFont of
          Nothing -> Nothing
          Just f -> lookupGlyph cp f.glyphCache
        advance = case cached of
          Nothing -> config.fontSize * 0.6  -- Fallback advance
          Just g -> g.advanceWidth * scale
        glyph =
          { codepoint: cp
          , x: x
          , y: 0.0  -- Baseline-relative
          , width: advance
          , height: config.fontSize
          , advanceWidth: advance + config.letterSpacing
          , geometry: map (\g -> g.geometry) cached
          }
      in
        shapeGlyphsGo config scale mFont rest (x + glyph.advanceWidth) (acc <> [glyph])
    _ -> acc
