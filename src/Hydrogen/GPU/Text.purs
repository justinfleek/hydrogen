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
-- | ## Dependencies
-- | - Hydrogen.Schema.Typography.FontMetrics
-- | - Hydrogen.Schema.Typography.GlyphGeometry
-- | - Hydrogen.GPU.DrawCommand
-- | - Hydrogen.GPU.GlyphConvert

module Hydrogen.GPU.Text
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
  
  -- * Text Shaping
  , ShapedGlyph
  , ShapedText
  , shapeText
  
  -- * Line Breaking
  , LineBreakResult
  , breakLines
  
  -- * Command Generation
  , textToCommands
  , shapedToCommands
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , map
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>)
  , (>=)
  , (<>)
  , (||)
  )

import Data.Array (filter, length, take, drop) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Map (Map)
import Data.Map as Map
import Data.String.CodeUnits (toCharArray) as SU
import Data.Enum (fromEnum) as Enum

import Hydrogen.Schema.Typography.FontMetrics as FM
import Hydrogen.Schema.Typography.GlyphGeometry as GG
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Color.RGB as RGB

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // font configuration
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // font atlas
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // glyph cache
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // text shaping
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- | Sum advance widths
sumAdvances :: Array ShapedGlyph -> Number
sumAdvances = foldlArray (\acc g -> acc + g.advanceWidth) 0.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // line breaking
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Result of line breaking
type LineBreakResult =
  { lines :: Array ShapedText
  , totalHeight :: Number
  }

-- | Break shaped text into lines that fit within maxWidth
-- |
-- | Uses greedy line breaking at word boundaries (spaces).
-- | For better typography, implement Knuth-Plass algorithm.
breakLines :: Number -> ShapedText -> LineBreakResult
breakLines maxWidth shaped =
  let
    -- For now, simple single-line (no breaking)
    -- Full implementation would:
    -- 1. Find word boundaries (space codepoints)
    -- 2. Measure word widths
    -- 3. Greedily fill lines until maxWidth exceeded
    -- 4. Reposition glyphs per line
    lines = [shaped]
    totalHeight = shaped.lineHeight
  in
    { lines, totalHeight }

-- | Check if codepoint is a space
isSpace :: Int -> Boolean
isSpace cp = cp == 32 || cp == 9 || cp == 10 || cp == 13

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // command generation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert text string directly to draw commands
-- |
-- | Convenience function that shapes text and generates commands.
textToCommands
  :: forall msg
   . FontConfig
  -> FontAtlas
  -> Number  -- ^ x position
  -> Number  -- ^ y position (baseline)
  -> String
  -> Array (DC.DrawCommand msg)
textToCommands config atlas x y text =
  let
    shaped = shapeText config atlas text
    positioned = offsetShapedText x y shaped
  in
    shapedToCommands config positioned

-- | Convert shaped text to draw commands
-- |
-- | Each glyph becomes a DrawGlyph or DrawGlyphInstance command.
shapedToCommands
  :: forall msg
   . FontConfig
  -> ShapedText
  -> Array (DC.DrawCommand msg)
shapedToCommands config shaped =
  mapArray (glyphToCommand config) shaped.glyphs

-- | Convert single shaped glyph to command
glyphToCommand
  :: forall msg
   . FontConfig
  -> ShapedGlyph
  -> DC.DrawCommand msg
glyphToCommand config glyph =
  DC.DrawGlyph (DC.glyphParams 
    (Device.px glyph.x)
    (Device.px glyph.y)
    glyph.codepoint  -- Use codepoint as glyph index
    config.fontId
    (Device.px config.fontSize)
    defaultTextColor
  )

-- | Offset shaped text by x, y
offsetShapedText :: Number -> Number -> ShapedText -> ShapedText
offsetShapedText dx dy shaped =
  shaped { glyphs = mapArray (offsetGlyph dx dy) shaped.glyphs }

-- | Offset a single glyph
offsetGlyph :: Number -> Number -> ShapedGlyph -> ShapedGlyph
offsetGlyph dx dy glyph =
  glyph { x = glyph.x + dx, y = glyph.y + dy }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert string to array of Unicode codepoints
-- |
-- | This is a placeholder - actual implementation requires String.toCodePointArray
-- | or similar, which is provided by the runtime. For compilation, we use
-- | Data.String.CodeUnits which is in the standard library.
stringToCodepoints :: String -> Array Int
stringToCodepoints str = mapArray charToInt (SU.toCharArray str)

-- | Convert Char to Int codepoint
-- | Uses Data.Enum.fromEnum which is available for Char
charToInt :: Char -> Int
charToInt = Enum.fromEnum

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber i = intToNumberGo i 0.0

intToNumberGo :: Int -> Number -> Number
intToNumberGo i acc
  | i <= 0 = acc
  | true = intToNumberGo (i - 1) (acc + 1.0)

-- | Map over array
mapArray :: forall a b. (a -> b) -> Array a -> Array b
mapArray f = foldlArray (\acc x -> acc <> [f x]) []

-- | Fold left
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f init arr = case Array.take 1 arr of
  [] -> init
  [x] -> foldlArray f (f init x) (Array.drop 1 arr)
  _ -> init

-- | Default text color (black)
defaultTextColor :: RGB.RGBA
defaultTextColor = RGB.rgba 0 0 0 255
