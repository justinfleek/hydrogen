-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // binary // decoding // common
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Common Decoding Utilities
-- |
-- | Shared types and helpers for binary decoding submodules.

module Hydrogen.Element.Binary.Decoding.Common
  ( -- * Shared Shape Helpers
    deserializePixelPoint2D
  , deserializeCorners
  , deserializeRectangleShape
  
  -- * Shared Fill/Stroke Helpers
  , deserializeFillAt
  , deserializeRGB
  , deserializeMaybeStroke
  , deserializeStrokeSpec
  , deserializeDashPattern
  , deserializeOpacity
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
  , (*)
  , (==)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (floor)

import Hydrogen.Element.Binary.Types (DeserializeResult)
import Hydrogen.Element.Binary.Primitives (readU32, readU8, readF32)

import Hydrogen.Element.Core (StrokeSpec)
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Stroke as Stroke
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Shape as Shape
import Hydrogen.Schema.Geometry.Stroke as GeomStroke
import Hydrogen.Schema.Surface.Fill as Fill

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // shared shape helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize PixelPoint2D (8 bytes)
deserializePixelPoint2D :: Array Int -> Int -> Maybe Shape.PixelPoint2D
deserializePixelPoint2D arr offset = do
  x <- readF32 arr offset
  y <- readF32 arr (offset + 4)
  Just { x: Device.Pixel x, y: Device.Pixel y }

-- | Deserialize Corners (16 bytes)
deserializeCorners :: Array Int -> Int -> Maybe Radius.Corners
deserializeCorners arr offset = do
  tl <- readF32 arr offset
  tr <- readF32 arr (offset + 4)
  br <- readF32 arr (offset + 8)
  bl <- readF32 arr (offset + 12)
  Just 
    { topLeft: Radius.RadiusPx tl
    , topRight: Radius.RadiusPx tr
    , bottomRight: Radius.RadiusPx br
    , bottomLeft: Radius.RadiusPx bl
    }

-- | Deserialize RectangleShape
deserializeRectangleShape :: Array Int -> Int -> Maybe (DeserializeResult Shape.RectangleShape)
deserializeRectangleShape arr offset = do
  -- center (8 bytes)
  center <- deserializePixelPoint2D arr offset
  -- width (4 bytes)
  width <- readF32 arr (offset + 8)
  -- height (4 bytes)
  height <- readF32 arr (offset + 12)
  -- corners (16 bytes)
  corners <- deserializeCorners arr (offset + 16)
  
  let shape = 
        { center: center
        , width: Device.Pixel width
        , height: Device.Pixel height
        , corners: corners
        }
  
  Just { value: shape, bytesRead: 32 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // shared fill/stroke helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Fill at offset
deserializeFillAt :: Array Int -> Int -> Maybe (DeserializeResult Fill.Fill)
deserializeFillAt arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> -- FillNone
      Just { value: Fill.FillNone, bytesRead: 1 }
    1 -> do -- FillSolid (RGB = 3 bytes)
      color <- deserializeRGB arr (offset + 1)
      Just { value: Fill.FillSolid color, bytesRead: 4 }
    2 -> -- FillGradient (not fully serialized yet)
      Just { value: Fill.FillNone, bytesRead: 1 }
    3 -> -- FillPattern (not fully serialized yet)
      Just { value: Fill.FillNone, bytesRead: 1 }
    4 -> -- FillNoise (not fully serialized yet)
      Just { value: Fill.FillNone, bytesRead: 1 }
    _ -> Nothing

-- | Deserialize RGB color (3 bytes)
deserializeRGB :: Array Int -> Int -> Maybe RGB.RGB
deserializeRGB arr offset = do
  r <- readU8 arr offset
  g <- readU8 arr (offset + 1)
  b <- readU8 arr (offset + 2)
  Just (RGB.rgb r g b)

-- | Deserialize Maybe StrokeSpec
deserializeMaybeStroke :: Array Int -> Int -> Maybe (DeserializeResult (Maybe StrokeSpec))
deserializeMaybeStroke arr offset = do
  hasStroke <- readU8 arr offset
  if hasStroke == 0
    then Just { value: Nothing, bytesRead: 1 }
    else do
      strokeResult <- deserializeStrokeSpec arr (offset + 1)
      Just { value: Just strokeResult.value, bytesRead: 1 + strokeResult.bytesRead }

-- | Deserialize StrokeSpec
deserializeStrokeSpec :: Array Int -> Int -> Maybe (DeserializeResult StrokeSpec)
deserializeStrokeSpec arr offset = do
  -- width (4)
  width <- readF32 arr offset
  
  -- fill (variable)
  fillResult <- deserializeFillAt arr (offset + 4)
  let afterFill = offset + 4 + fillResult.bytesRead
  
  -- cap (1)
  capByte <- readU8 arr afterFill
  let cap = case capByte of
        1 -> GeomStroke.CapRound
        2 -> GeomStroke.CapSquare
        _ -> GeomStroke.CapButt
  
  -- join (1)
  joinByte <- readU8 arr (afterFill + 1)
  let join = case joinByte of
        1 -> GeomStroke.JoinRound
        2 -> GeomStroke.JoinBevel
        _ -> GeomStroke.JoinMiter
  
  -- miterLimit (4)
  miterLimit <- readF32 arr (afterFill + 2)
  
  -- dashPattern (variable)
  dashResult <- deserializeDashPattern arr (afterFill + 6)
  let afterDash = afterFill + 6 + dashResult.bytesRead
  
  -- opacity (4)
  opacityVal <- readF32 arr afterDash
  
  let spec = 
        { width: Stroke.strokeWidth width
        , fill: fillResult.value
        , cap: cap
        , join: join
        , miterLimit: GeomStroke.miterLimit miterLimit
        , dashPattern: dashResult.value
        , opacity: Opacity.opacity (floor opacityVal)
        }
  
  Just { value: spec, bytesRead: afterDash + 4 - offset }

-- | Deserialize DashPattern
deserializeDashPattern :: Array Int -> Int -> Maybe (DeserializeResult Stroke.DashPattern)
deserializeDashPattern arr offset = do
  count <- readU32 arr offset
  segments <- deserializeDashSegments arr (offset + 4) count
  -- Convert raw Numbers (alternating dash/gap) to DashPattern
  let pairs = segmentsToPairs segments
      pattern = Stroke.dashPattern pairs
  Just { value: pattern, bytesRead: 4 + count * 4 }

-- | Convert flat array of segments [d1, g1, d2, g2, ...] to pairs
segmentsToPairs :: Array Number -> Array { dash :: Number, gap :: Number }
segmentsToPairs segments = segmentsToPairsLoop segments []

segmentsToPairsLoop :: Array Number -> Array { dash :: Number, gap :: Number } -> Array { dash :: Number, gap :: Number }
segmentsToPairsLoop segments acc =
  case Array.uncons segments of
    Nothing -> acc
    Just { head: dash, tail: rest1 } ->
      case Array.uncons rest1 of
        Nothing -> acc <> [{ dash: dash, gap: 0.0 }]  -- Odd element, default gap to 0
        Just { head: gap, tail: rest2 } ->
          segmentsToPairsLoop rest2 (acc <> [{ dash: dash, gap: gap }])

-- | Helper to deserialize dash segments
deserializeDashSegments :: Array Int -> Int -> Int -> Maybe (Array Number)
deserializeDashSegments arr offset count =
  deserializeDashLoop arr offset count []

deserializeDashLoop :: Array Int -> Int -> Int -> Array Number -> Maybe (Array Number)
deserializeDashLoop arr offset remaining acc =
  if remaining == 0
    then Just acc
    else do
      val <- readF32 arr offset
      deserializeDashLoop arr (offset + 4) (remaining - 1) (acc <> [val])

-- | Deserialize Opacity (4 bytes)
deserializeOpacity :: Array Int -> Int -> Maybe Opacity.Opacity
deserializeOpacity arr offset = do
  val <- readF32 arr offset
  Just (Opacity.opacity (floor val))
