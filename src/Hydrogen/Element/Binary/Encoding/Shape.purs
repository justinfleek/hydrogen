-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // binary // encoding // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape Serialization
-- |
-- | Binary encoding for Rectangle, Ellipse, Path, and geometric primitives.

module Hydrogen.Element.Binary.Encoding.Shape
  ( -- * Rectangle
    serializeRectangleSpec
  , serializeRectangleShape
  , serializePixelPoint2D
  , serializeCorners
  
  -- * Ellipse
  , serializeEllipseSpec
  , serializeEllipseShape
  
  -- * Path
  , serializePathSpec
  , serializePathShape
  , serializePathCommands
  , serializePathCommand
  , serializeArcParams
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
  ( RectangleSpec
  , EllipseSpec
  , PathSpec
  )

import Hydrogen.Schema.Geometry.Shape as Shape
import Hydrogen.Schema.Geometry.Radius as Radius

import Hydrogen.Element.Binary.Encoding.Helpers
  ( unwrapPixel
  , radiusToNumber
  )

import Hydrogen.Element.Binary.Encoding.Material
  ( serializeFill
  , serializeMaybeStroke
  , serializeOpacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // rectangle serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize RectangleSpec
serializeRectangleSpec :: RectangleSpec -> Bytes
serializeRectangleSpec spec =
  concatBytes (serializeRectangleShape spec.shape) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  serializeOpacity spec.opacity

-- | Serialize RectangleShape
serializeRectangleShape :: Shape.RectangleShape -> Bytes
serializeRectangleShape shape =
  concatBytes (serializePixelPoint2D shape.center) $
  concatBytes (writeF32 (unwrapPixel shape.width)) $
  concatBytes (writeF32 (unwrapPixel shape.height)) $
  serializeCorners shape.corners

-- | Serialize PixelPoint2D (8 bytes)
serializePixelPoint2D :: Shape.PixelPoint2D -> Bytes
serializePixelPoint2D pt =
  concatBytes (writeF32 (unwrapPixel pt.x)) $
  writeF32 (unwrapPixel pt.y)

-- | Serialize corner radii (16 bytes: 4 corners x 4 bytes each)
serializeCorners :: Radius.Corners -> Bytes
serializeCorners corners =
  concatBytes (writeF32 (radiusToNumber corners.topLeft)) $
  concatBytes (writeF32 (radiusToNumber corners.topRight)) $
  concatBytes (writeF32 (radiusToNumber corners.bottomRight)) $
  writeF32 (radiusToNumber corners.bottomLeft)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // ellipse serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize EllipseSpec
serializeEllipseSpec :: EllipseSpec -> Bytes
serializeEllipseSpec spec =
  concatBytes (serializeEllipseShape spec.shape) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  serializeOpacity spec.opacity

-- | Serialize EllipseShape (16 bytes)
serializeEllipseShape :: Shape.EllipseShape -> Bytes
serializeEllipseShape shape =
  concatBytes (serializePixelPoint2D shape.center) $
  concatBytes (writeF32 (unwrapPixel shape.radiusX)) $
  writeF32 (unwrapPixel shape.radiusY)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // path serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize PathSpec
serializePathSpec :: PathSpec -> Bytes
serializePathSpec spec =
  concatBytes (serializePathShape spec.shape) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  serializeOpacity spec.opacity

-- | Serialize PathShape
serializePathShape :: Shape.PathShape -> Bytes
serializePathShape shape =
  let
    windingByte = case shape.windingRule of
      Shape.WindingNonZero -> writeU8 0
      Shape.WindingEvenOdd -> writeU8 1
    countBytes = writeU32 (Array.length shape.commands)
    commandBytes = serializePathCommands shape.commands
  in
    concatBytes windingByte $
    concatBytes countBytes $
    commandBytes

-- | Serialize array of PathCommands
serializePathCommands :: Array Shape.PathCommand -> Bytes
serializePathCommands cmds =
  Array.foldl (\acc cmd -> concatBytes acc (serializePathCommand cmd)) emptyBytes cmds

-- | Serialize single PathCommand
serializePathCommand :: Shape.PathCommand -> Bytes
serializePathCommand = case _ of
  Shape.MoveTo pt ->
    concatBytes (writeU8 0) (serializePixelPoint2D pt)
  Shape.LineTo pt ->
    concatBytes (writeU8 1) (serializePixelPoint2D pt)
  Shape.CubicTo cp1 cp2 end ->
    concatBytes (writeU8 2) $
    concatBytes (serializePixelPoint2D cp1) $
    concatBytes (serializePixelPoint2D cp2) $
    serializePixelPoint2D end
  Shape.QuadraticTo cp end ->
    concatBytes (writeU8 3) $
    concatBytes (serializePixelPoint2D cp) $
    serializePixelPoint2D end
  Shape.ClosePath ->
    writeU8 4
  Shape.HorizontalTo x ->
    concatBytes (writeU8 5) (writeF32 (unwrapPixel x))
  Shape.VerticalTo y ->
    concatBytes (writeU8 6) (writeF32 (unwrapPixel y))
  Shape.ArcTo params endPt ->
    concatBytes (writeU8 7) $
    concatBytes (serializeArcParams params) $
    serializePixelPoint2D endPt

-- | Serialize ArcParams
serializeArcParams :: Shape.ArcParams -> Bytes
serializeArcParams params =
  concatBytes (writeF32 (unwrapPixel params.radiusX)) $
  concatBytes (writeF32 (unwrapPixel params.radiusY)) $
  concatBytes (writeF32 params.rotation) $
  concatBytes (writeU8 (if params.largeArc then 1 else 0)) $
  writeU8 (if params.sweep then 1 else 0)
