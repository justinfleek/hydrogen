-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // binary // decoding // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text Decoding
-- |
-- | Deserialize Text elements (glyphs, contours, 3D paths) from binary format.

module Hydrogen.Element.Binary.Decoding.Text
  ( -- * Text
    deserializeText
  , deserializeGlyphs
  , deserializeGlyph
  
  -- * Glyph Path
  , deserializeGlyphPath
  , deserializeContours
  , deserializeContour
  
  -- * 3D Path Commands
  , deserializePathCommands3D
  , deserializePathCommand3D
  , deserializeControlPoint3D
  , deserializeGlyphBounds
  
  -- * Transform
  , deserializeTransform2D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , pure
  , ($)
  , (+)
  , (-)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Binary.Types (DeserializeResult)
import Hydrogen.Element.Binary.Primitives (readU32, readU8, readF32)

import Hydrogen.Element.Binary.Decoding.Common
  ( deserializeFillAt
  , deserializeMaybeStroke
  , deserializeOpacity
  )

import Hydrogen.Element.Core
  ( Element(Text)
  , TextSpec
  , GlyphSpec
  )

import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Angle (degrees)
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Typography.GlyphGeometry as Glyph

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // text deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Text at offset
deserializeText :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeText arr offset = do
  -- Glyph count (4 bytes)
  glyphCount <- readU32 arr offset
  
  -- Glyphs (variable)
  glyphsResult <- deserializeGlyphs arr (offset + 4) glyphCount
  let glyphsEnd = offset + 4 + glyphsResult.bytesRead
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr glyphsEnd
  
  let spec :: TextSpec
      spec =
        { glyphs: glyphsResult.value
        , opacity: opacity
        }
  
  Just { value: Text spec, bytesRead: glyphsEnd + 4 - offset }

-- | Deserialize array of GlyphSpec
deserializeGlyphs :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array GlyphSpec))
deserializeGlyphs arr offset count =
  deserializeGlyphsLoop arr offset count []

-- | Helper loop for glyph deserialization
deserializeGlyphsLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array GlyphSpec 
  -> Maybe (DeserializeResult (Array GlyphSpec))
deserializeGlyphsLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      glyphResult <- deserializeGlyph arr offset
      let newOffset = offset + glyphResult.bytesRead
      restResult <- deserializeGlyphsLoop arr newOffset (remaining - 1) (Array.snoc acc glyphResult.value)
      pure { value: restResult.value, bytesRead: glyphResult.bytesRead + restResult.bytesRead }

-- | Deserialize single GlyphSpec
deserializeGlyph :: Array Int -> Int -> Maybe (DeserializeResult GlyphSpec)
deserializeGlyph arr offset = do
  -- GlyphPath (variable)
  glyphPathResult <- deserializeGlyphPath arr offset
  let glyphPathEnd = offset + glyphPathResult.bytesRead
  
  -- Transform2D (36 bytes)
  transform <- deserializeTransform2D arr glyphPathEnd
  let transformEnd = glyphPathEnd + 36
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr transformEnd
  let fillEnd = transformEnd + fillResult.bytesRead
  
  -- Maybe Stroke (variable)
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr strokeEnd
  let opacityEnd = strokeEnd + 4
  
  -- Progress (4 bytes)
  progressVal <- readF32 arr opacityEnd
  
  let spec =
        { glyph: glyphPathResult.value
        , transform: transform
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        , progress: Progress.progress progressVal
        }
  
  Just { value: spec, bytesRead: opacityEnd + 4 - offset }

-- | Deserialize GlyphPath
deserializeGlyphPath :: Array Int -> Int -> Maybe (DeserializeResult Glyph.GlyphPath)
deserializeGlyphPath arr offset = do
  -- Contour count (4 bytes)
  contourCount <- readU32 arr offset
  
  -- Contours (variable)
  contoursResult <- deserializeContours arr (offset + 4) contourCount
  let contoursEnd = offset + 4 + contoursResult.bytesRead
  
  -- Bounds (24 bytes)
  bounds <- deserializeGlyphBounds arr contoursEnd
  let boundsEnd = contoursEnd + 24
  
  -- Advance width (4 bytes)
  advanceWidth <- readF32 arr boundsEnd
  
  -- Left side bearing (4 bytes)
  leftSideBearing <- readF32 arr (boundsEnd + 4)
  
  let gp =
        { contours: contoursResult.value
        , bounds: bounds
        , advanceWidth: Device.Pixel advanceWidth
        , leftSideBearing: Device.Pixel leftSideBearing
        }
  
  Just { value: gp, bytesRead: boundsEnd + 8 - offset }

-- | Deserialize array of Contours
deserializeContours :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Glyph.Contour))
deserializeContours arr offset count =
  deserializeContoursLoop arr offset count []

-- | Helper loop for contour deserialization
deserializeContoursLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Glyph.Contour 
  -> Maybe (DeserializeResult (Array Glyph.Contour))
deserializeContoursLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      contourResult <- deserializeContour arr offset
      let newOffset = offset + contourResult.bytesRead
      restResult <- deserializeContoursLoop arr newOffset (remaining - 1) (Array.snoc acc contourResult.value)
      pure { value: restResult.value, bytesRead: contourResult.bytesRead + restResult.bytesRead }

-- | Deserialize single Contour
deserializeContour :: Array Int -> Int -> Maybe (DeserializeResult Glyph.Contour)
deserializeContour arr offset = do
  -- Winding (1 byte)
  windingByte <- readU8 arr offset
  let winding = if windingByte == 0 
        then Glyph.WindingClockwise 
        else Glyph.WindingCounterClockwise
  
  -- Command count (4 bytes)
  commandCount <- readU32 arr (offset + 1)
  
  -- Commands (variable)
  commandsResult <- deserializePathCommands3D arr (offset + 5) commandCount
  
  let c = { commands: commandsResult.value, winding: winding }
  
  Just { value: c, bytesRead: 5 + commandsResult.bytesRead }

-- | Deserialize array of 3D path commands
deserializePathCommands3D :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Glyph.PathCommand3D))
deserializePathCommands3D arr offset count =
  deserializePathCommands3DLoop arr offset count []

-- | Helper loop for 3D path command deserialization
deserializePathCommands3DLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Glyph.PathCommand3D 
  -> Maybe (DeserializeResult (Array Glyph.PathCommand3D))
deserializePathCommands3DLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      cmdResult <- deserializePathCommand3D arr offset
      let newOffset = offset + cmdResult.bytesRead
      restResult <- deserializePathCommands3DLoop arr newOffset (remaining - 1) (Array.snoc acc cmdResult.value)
      pure { value: restResult.value, bytesRead: cmdResult.bytesRead + restResult.bytesRead }

-- | Deserialize single 3D path command
deserializePathCommand3D :: Array Int -> Int -> Maybe (DeserializeResult Glyph.PathCommand3D)
deserializePathCommand3D arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do  -- MoveTo3D
      pt <- deserializeControlPoint3D arr (offset + 1)
      pure { value: Glyph.MoveTo3D pt, bytesRead: 13 }
    1 -> do  -- LineTo3D
      pt <- deserializeControlPoint3D arr (offset + 1)
      pure { value: Glyph.LineTo3D pt, bytesRead: 13 }
    2 -> do  -- QuadraticTo3D
      c1 <- deserializeControlPoint3D arr (offset + 1)
      end <- deserializeControlPoint3D arr (offset + 13)
      pure { value: Glyph.QuadraticTo3D c1 end, bytesRead: 25 }
    3 -> do  -- CubicTo3D
      c1 <- deserializeControlPoint3D arr (offset + 1)
      c2 <- deserializeControlPoint3D arr (offset + 13)
      end <- deserializeControlPoint3D arr (offset + 25)
      pure { value: Glyph.CubicTo3D c1 c2 end, bytesRead: 37 }
    4 ->     -- ClosePath3D
      pure { value: Glyph.ClosePath3D, bytesRead: 1 }
    _ -> Nothing

-- | Deserialize ControlPoint3D (12 bytes)
deserializeControlPoint3D :: Array Int -> Int -> Maybe Glyph.ControlPoint3D
deserializeControlPoint3D arr offset = do
  x <- readF32 arr offset
  y <- readF32 arr (offset + 4)
  z <- readF32 arr (offset + 8)
  pure (Glyph.controlPoint3D (Device.Pixel x) (Device.Pixel y) (Device.Pixel z))

-- | Deserialize GlyphBounds (24 bytes)
deserializeGlyphBounds :: Array Int -> Int -> Maybe Glyph.GlyphBounds
deserializeGlyphBounds arr offset = do
  minX <- readF32 arr offset
  maxX <- readF32 arr (offset + 4)
  minY <- readF32 arr (offset + 8)
  maxY <- readF32 arr (offset + 12)
  minZ <- readF32 arr (offset + 16)
  maxZ <- readF32 arr (offset + 20)
  pure (Glyph.glyphBounds 
    (Device.Pixel minX) (Device.Pixel maxX)
    (Device.Pixel minY) (Device.Pixel maxY)
    (Device.Pixel minZ) (Device.Pixel maxZ))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // transform deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Transform2D (36 bytes)
deserializeTransform2D :: Array Int -> Int -> Maybe Transform.Transform2D
deserializeTransform2D arr offset = do
  tx <- readF32 arr offset
  ty <- readF32 arr (offset + 4)
  sx <- readF32 arr (offset + 8)
  sy <- readF32 arr (offset + 12)
  rot <- readF32 arr (offset + 16)
  skx <- readF32 arr (offset + 20)
  sky <- readF32 arr (offset + 24)
  ox <- readF32 arr (offset + 28)
  oy <- readF32 arr (offset + 32)
  
  -- Reconstruct Transform2D from components
  let translate = if tx == 0.0 && ty == 0.0 
        then Nothing 
        else Just (Transform.Translate { x: tx, y: ty })
      
      scale = if sx == 1.0 && sy == 1.0 
        then Nothing 
        else Just (Transform.Scale { x: sx, y: sy })
      
      rotate = if rot == 0.0 
        then Nothing 
        else Just (Transform.Rotate { angle: degrees rot })
      
      skew = if skx == 0.0 && sky == 0.0 
        then Nothing 
        else Just (Transform.Skew { x: skx, y: sky })
      
      origin = Transform.Origin { x: ox, y: oy }
  
  Just (Transform.Transform2D { translate, rotate, scale, skew, origin })
