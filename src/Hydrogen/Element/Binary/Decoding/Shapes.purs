-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // binary // decoding // shapes
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape Decoding
-- |
-- | Deserialize Rectangle, Ellipse, Path elements from binary format.

module Hydrogen.Element.Binary.Decoding.Shapes
  ( -- * Rectangle
    deserializeRectangle
  
  -- * Ellipse
  , deserializeEllipse
  , deserializeEllipseShape
  
  -- * Path
  , deserializePath
  , deserializePathShape
  , deserializePathCommands
  , deserializePathCommand
  , deserializeArcParams
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
  , (/=)
  , (>)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Binary.Types (DeserializeResult)
import Hydrogen.Element.Binary.Primitives (readU32, readU8, readF32)

import Hydrogen.Element.Binary.Decoding.Common
  ( deserializePixelPoint2D
  , deserializeRectangleShape
  , deserializeFillAt
  , deserializeMaybeStroke
  , deserializeOpacity
  )

import Hydrogen.Element.Core
  ( Element(Rectangle, Ellipse, Path)
  , RectangleSpec
  , EllipseSpec
  , PathSpec
  )

import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Shape as Shape

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // rectangle deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Rectangle at offset
deserializeRectangle :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeRectangle arr offset = do
  -- RectangleShape: center (8) + width (4) + height (4) + corners (16) = 32 bytes
  shapeResult <- deserializeRectangleShape arr offset
  let shapeEnd = offset + shapeResult.bytesRead
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr shapeEnd
  let fillEnd = shapeEnd + fillResult.bytesRead
  
  -- Maybe Stroke
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4)
  opacity <- deserializeOpacity arr strokeEnd
  
  let spec :: RectangleSpec
      spec = 
        { shape: shapeResult.value
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        }
  
  Just { value: Rectangle spec, bytesRead: strokeEnd + 4 - offset }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // ellipse deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Ellipse at offset
deserializeEllipse :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeEllipse arr offset = do
  -- EllipseShape: center (8) + radiusX (4) + radiusY (4) = 16 bytes
  shapeResult <- deserializeEllipseShape arr offset
  let shapeEnd = offset + shapeResult.bytesRead
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr shapeEnd
  let fillEnd = shapeEnd + fillResult.bytesRead
  
  -- Maybe Stroke
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4)
  opacity <- deserializeOpacity arr strokeEnd
  
  let spec :: EllipseSpec
      spec = 
        { shape: shapeResult.value
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        }
  
  Just { value: Ellipse spec, bytesRead: strokeEnd + 4 - offset }

-- | Deserialize EllipseShape (16 bytes)
deserializeEllipseShape :: Array Int -> Int -> Maybe (DeserializeResult Shape.EllipseShape)
deserializeEllipseShape arr offset = do
  center <- deserializePixelPoint2D arr offset
  rx <- readF32 arr (offset + 8)
  ry <- readF32 arr (offset + 12)
  
  let shape = 
        { center: center
        , radiusX: Device.Pixel rx
        , radiusY: Device.Pixel ry
        }
  
  Just { value: shape, bytesRead: 16 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // path deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Path at offset
deserializePath :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializePath arr offset = do
  -- PathShape: windingRule (1) + commandCount (4) + commands (variable)
  shapeResult <- deserializePathShape arr offset
  let shapeEnd = offset + shapeResult.bytesRead
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr shapeEnd
  let fillEnd = shapeEnd + fillResult.bytesRead
  
  -- Maybe Stroke
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4)
  opacity <- deserializeOpacity arr strokeEnd
  
  let spec :: PathSpec
      spec = 
        { shape: shapeResult.value
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        }
  
  Just { value: Path spec, bytesRead: strokeEnd + 4 - offset }

-- | Deserialize PathShape
deserializePathShape :: Array Int -> Int -> Maybe (DeserializeResult Shape.PathShape)
deserializePathShape arr offset = do
  -- Winding rule (1 byte)
  windingByte <- readU8 arr offset
  let winding = if windingByte == 0 then Shape.WindingNonZero else Shape.WindingEvenOdd
  
  -- Command count (4 bytes)
  count <- readU32 arr (offset + 1)
  
  -- Commands (variable)
  commandsResult <- deserializePathCommands arr (offset + 5) count
  
  let shape = 
        { commands: commandsResult.value
        , windingRule: winding
        , closed: count > 0
        }
  
  Just { value: shape, bytesRead: 5 + commandsResult.bytesRead }

-- | Deserialize array of PathCommands
deserializePathCommands :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Shape.PathCommand))
deserializePathCommands arr offset count = 
  deserializePathCommandsLoop arr offset count []

-- | Helper for deserializing path commands
deserializePathCommandsLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Shape.PathCommand 
  -> Maybe (DeserializeResult (Array Shape.PathCommand))
deserializePathCommandsLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      cmdResult <- deserializePathCommand arr offset
      restResult <- deserializePathCommandsLoop arr (offset + cmdResult.bytesRead) (remaining - 1) (acc <> [cmdResult.value])
      Just { value: restResult.value, bytesRead: cmdResult.bytesRead + restResult.bytesRead }

-- | Deserialize single PathCommand
deserializePathCommand :: Array Int -> Int -> Maybe (DeserializeResult Shape.PathCommand)
deserializePathCommand arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do -- MoveTo
      pt <- deserializePixelPoint2D arr (offset + 1)
      Just { value: Shape.MoveTo pt, bytesRead: 9 }
    1 -> do -- LineTo
      pt <- deserializePixelPoint2D arr (offset + 1)
      Just { value: Shape.LineTo pt, bytesRead: 9 }
    2 -> do -- CubicTo
      cp1 <- deserializePixelPoint2D arr (offset + 1)
      cp2 <- deserializePixelPoint2D arr (offset + 9)
      end <- deserializePixelPoint2D arr (offset + 17)
      Just { value: Shape.CubicTo cp1 cp2 end, bytesRead: 25 }
    3 -> do -- QuadraticTo
      cp <- deserializePixelPoint2D arr (offset + 1)
      end <- deserializePixelPoint2D arr (offset + 9)
      Just { value: Shape.QuadraticTo cp end, bytesRead: 17 }
    4 -> -- ClosePath
      Just { value: Shape.ClosePath, bytesRead: 1 }
    5 -> do -- HorizontalTo
      x <- readF32 arr (offset + 1)
      Just { value: Shape.HorizontalTo (Device.Pixel x), bytesRead: 5 }
    6 -> do -- VerticalTo
      y <- readF32 arr (offset + 1)
      Just { value: Shape.VerticalTo (Device.Pixel y), bytesRead: 5 }
    7 -> do -- ArcTo
      arcResult <- deserializeArcParams arr (offset + 1)
      endPt <- deserializePixelPoint2D arr (offset + 1 + arcResult.bytesRead)
      Just { value: Shape.ArcTo arcResult.value endPt, bytesRead: 1 + arcResult.bytesRead + 8 }
    _ -> Nothing

-- | Deserialize ArcParams
deserializeArcParams :: Array Int -> Int -> Maybe (DeserializeResult Shape.ArcParams)
deserializeArcParams arr offset = do
  rx <- readF32 arr offset
  ry <- readF32 arr (offset + 4)
  rotation <- readF32 arr (offset + 8)
  largeArcByte <- readU8 arr (offset + 12)
  sweepByte <- readU8 arr (offset + 13)
  
  let params = 
        { radiusX: Device.Pixel rx
        , radiusY: Device.Pixel ry
        , rotation: rotation
        , largeArc: largeArcByte /= 0
        , sweep: sweepByte /= 0
        }
  
  Just { value: params, bytesRead: 14 }
