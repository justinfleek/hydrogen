-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // text
--                                                                  // commands
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Command Generation — Converting shaped text to GPU draw commands
-- |
-- | The final stage of the text pipeline: converting positioned glyphs
-- | into DrawCommand values that the GPU can execute.
-- |
-- | ## Typography Pipeline
-- |
-- | ```
-- | ShapedText (positioned glyphs)
-- |     ↓ shapedToCommands
-- | Array (DrawCommand msg)
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.GPU.Text.Types
-- | - Hydrogen.GPU.Text.Shaping
-- | - Hydrogen.GPU.DrawCommand
-- | - Hydrogen.Schema.Dimension.Device
-- | - Hydrogen.Schema.Color.RGB

module Hydrogen.GPU.Text.Commands
  ( textToCommands
  , shapedToCommands
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  )

import Hydrogen.GPU.Text.Types
  ( FontConfig
  , FontAtlas
  , ShapedGlyph
  , ShapedText
  )
import Hydrogen.GPU.Text.Shaping (shapeText)
import Hydrogen.GPU.Text.Internal (mapArray)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // command generation
-- ═════════════════════════════════════════════════════════════════════════════

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

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

-- | Default text color (black)
defaultTextColor :: RGB.RGBA
defaultTextColor = RGB.rgba 0 0 0 255
