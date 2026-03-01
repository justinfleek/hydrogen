-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // binary // encoding // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Serialization
-- |
-- | Binary encoding for Text elements and glyph geometry.

module Hydrogen.Element.Binary.Encoding.Text
  ( serializeTextSpec
  , serializeGlyphArray
  , serializeGlyph
  , serializeGlyphPath
  , serializeContours
  , serializeContour
  , serializePathCommands3D
  , serializePathCommand3D
  , serializeControlPoint3D
  , serializeGlyphBounds
  , serializeProgress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Data.Array as Array

import Hydrogen.Element.Binary.Types
  ( Bytes
  )

import Hydrogen.Element.Binary.Primitives
  ( concatBytes
  , emptyBytes
  , writeU32
  , writeU8
  , writeF32
  )

import Hydrogen.Element.Core
  ( TextSpec
  , GlyphSpec
  )

import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Typography.GlyphGeometry as Glyph
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Element.Binary.Encoding.Helpers
  ( unwrapPixel
  )

import Hydrogen.Element.Binary.Encoding.Material
  ( serializeFill
  , serializeMaybeStroke
  , serializeOpacity
  )

import Hydrogen.Element.Binary.Encoding.Transform
  ( serializeTransform2D
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize TextSpec
-- |
-- | Layout:
-- |   glyphCount (u32) + glyphs (variable) + opacity (f32)
serializeTextSpec :: TextSpec -> Bytes
serializeTextSpec spec =
  let glyphCount = writeU32 (Array.length spec.glyphs)
      glyphBytes = serializeGlyphArray spec.glyphs
  in concatBytes glyphCount $
     concatBytes glyphBytes $
     serializeOpacity spec.opacity

-- | Serialize array of GlyphSpec
serializeGlyphArray :: Array GlyphSpec -> Bytes
serializeGlyphArray glyphs =
  Array.foldl (\acc g -> concatBytes acc (serializeGlyph g)) emptyBytes glyphs

-- | Serialize single GlyphSpec
-- |
-- | Layout:
-- |   glyphPath (variable) + transform2D (36) + fill (variable) + 
-- |   maybeStroke (variable) + opacity (4) + progress (4)
serializeGlyph :: GlyphSpec -> Bytes
serializeGlyph spec =
  concatBytes (serializeGlyphPath spec.glyph) $
  concatBytes (serializeTransform2D spec.transform) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  concatBytes (serializeOpacity spec.opacity) $
  serializeProgress spec.progress

-- | Serialize Progress (4 bytes as f32)
serializeProgress :: Progress.Progress -> Bytes
serializeProgress p = writeF32 (Progress.unwrapProgress p)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // glyph serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize GlyphPath
-- |
-- | Layout:
-- |   contourCount (u32) + contours (variable) + bounds (24) +
-- |   advanceWidth (4) + leftSideBearing (4)
serializeGlyphPath :: Glyph.GlyphPath -> Bytes
serializeGlyphPath gp =
  let contourCount = writeU32 (Array.length gp.contours)
      contourBytes = serializeContours gp.contours
  in concatBytes contourCount $
     concatBytes contourBytes $
     concatBytes (serializeGlyphBounds gp.bounds) $
     concatBytes (writeF32 (unwrapPixel gp.advanceWidth)) $
     writeF32 (unwrapPixel gp.leftSideBearing)

-- | Serialize array of Contours
serializeContours :: Array Glyph.Contour -> Bytes
serializeContours contours =
  Array.foldl (\acc c -> concatBytes acc (serializeContour c)) emptyBytes contours

-- | Serialize single Contour
-- |
-- | Layout:
-- |   winding (u8) + commandCount (u32) + commands (variable)
serializeContour :: Glyph.Contour -> Bytes
serializeContour c =
  let windingByte = case c.winding of
        Glyph.WindingClockwise -> writeU8 0
        Glyph.WindingCounterClockwise -> writeU8 1
      commandCount = writeU32 (Array.length c.commands)
      commandBytes = serializePathCommands3D c.commands
  in concatBytes windingByte $
     concatBytes commandCount $
     commandBytes

-- | Serialize array of 3D path commands
serializePathCommands3D :: Array Glyph.PathCommand3D -> Bytes
serializePathCommands3D cmds =
  Array.foldl (\acc cmd -> concatBytes acc (serializePathCommand3D cmd)) emptyBytes cmds

-- | Serialize single 3D path command
-- |
-- | Tags:
-- |   0 = MoveTo3D (12 bytes: x, y, z)
-- |   1 = LineTo3D (12 bytes)
-- |   2 = QuadraticTo3D (24 bytes: control + end)
-- |   3 = CubicTo3D (36 bytes: c1 + c2 + end)
-- |   4 = ClosePath3D (0 bytes)
serializePathCommand3D :: Glyph.PathCommand3D -> Bytes
serializePathCommand3D = case _ of
  Glyph.MoveTo3D p ->
    concatBytes (writeU8 0) (serializeControlPoint3D p)
  Glyph.LineTo3D p ->
    concatBytes (writeU8 1) (serializeControlPoint3D p)
  Glyph.QuadraticTo3D c1 end ->
    concatBytes (writeU8 2) $
    concatBytes (serializeControlPoint3D c1) $
    serializeControlPoint3D end
  Glyph.CubicTo3D c1 c2 end ->
    concatBytes (writeU8 3) $
    concatBytes (serializeControlPoint3D c1) $
    concatBytes (serializeControlPoint3D c2) $
    serializeControlPoint3D end
  Glyph.ClosePath3D ->
    writeU8 4

-- | Serialize ControlPoint3D (12 bytes: x, y, z as f32)
serializeControlPoint3D :: Glyph.ControlPoint3D -> Bytes
serializeControlPoint3D pt =
  concatBytes (writeF32 (unwrapPixel pt.x)) $
  concatBytes (writeF32 (unwrapPixel pt.y)) $
  writeF32 (unwrapPixel pt.z)

-- | Serialize GlyphBounds (24 bytes: 6 x f32)
serializeGlyphBounds :: Glyph.GlyphBounds -> Bytes
serializeGlyphBounds b =
  concatBytes (writeF32 (unwrapPixel b.minX)) $
  concatBytes (writeF32 (unwrapPixel b.maxX)) $
  concatBytes (writeF32 (unwrapPixel b.minY)) $
  concatBytes (writeF32 (unwrapPixel b.maxY)) $
  concatBytes (writeF32 (unwrapPixel b.minZ)) $
  writeF32 (unwrapPixel b.maxZ)
