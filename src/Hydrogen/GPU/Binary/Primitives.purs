-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // binary // primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core primitive serializers for GPU commands.
-- |
-- | This module provides serialization for the fundamental draw commands:
-- | DrawRect, DrawQuad, DrawGlyph, DrawPath, DrawParticle, and ClipRegion.

module Hydrogen.GPU.Binary.Primitives
  ( -- * Main serialization
    serialize
  , serializeHeader
  , serializeCommand
  
  -- * Primitive serializers
  , serializeRect
  , serializeQuad
  , serializeGlyph
  , serializePath
  , serializeParticle
  , serializeClipRegion
  , serializePathSegment
  , serializeMaybeColor
  
  -- * Helpers
  , pad
  , unwrapPixel
  , radiusToNumber
  , pickIdToInt
  ) where

import Prelude
  ( (<>)
  , (*)
  )

import Data.Array (concatMap, length, replicate) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.GPU.Binary.Constants (magic, version) as Constants
import Hydrogen.GPU.Binary.LowLevel (writeF32, writeU32, writeU16, writeU8)
import Hydrogen.GPU.Binary.Types (Bytes(Bytes), Header)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- Forward imports for v2 serializers (will be called via serializeCommand)
import Hydrogen.GPU.Binary.Typography as Typography
import Hydrogen.GPU.Binary.Media as Media

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // main serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a command buffer to bytes.
serialize :: forall msg. DC.CommandBuffer msg -> Bytes
serialize commands =
  let
    header = serializeHeader
      { magic: Constants.magic
      , version: Constants.version
      , count: Array.length commands
      , flags: 0
      }
    body = Array.concatMap serializeCommand commands
  in
    Bytes (header <> body)

-- | Serialize header.
serializeHeader :: Header -> Array Int
serializeHeader h =
  writeU32 h.magic
  <> writeU32 h.version
  <> writeU32 h.count
  <> writeU32 h.flags

-- | Serialize a single command.
serializeCommand :: forall msg. DC.DrawCommand msg -> Array Int
serializeCommand = case _ of
  DC.Noop -> writeU8 0x00
  
  DC.DrawRect params -> writeU8 0x01 <> pad 3 <> serializeRect params
  
  DC.DrawQuad params -> writeU8 0x02 <> pad 3 <> serializeQuad params
  
  DC.DrawGlyph params -> writeU8 0x03 <> pad 3 <> serializeGlyph params
  
  DC.DrawPath params -> writeU8 0x04 <> pad 3 <> serializePath params
  
  DC.DrawParticle params -> writeU8 0x05 <> pad 3 <> serializeParticle params
  
  DC.PushClip region -> writeU8 0x10 <> pad 3 <> serializeClipRegion region
  
  DC.PopClip -> writeU8 0x11 <> pad 3
  
  -- v2 Typography as Geometry (opcodes 0x20-0x24)
  DC.DrawGlyphPath params -> writeU8 0x20 <> pad 3 <> Typography.serializeGlyphPath params
  
  DC.DrawGlyphInstance params -> writeU8 0x21 <> pad 3 <> Typography.serializeGlyphInstance params
  
  DC.DrawWord params -> writeU8 0x22 <> pad 3 <> Typography.serializeWord params
  
  DC.DefinePathData params -> writeU8 0x23 <> pad 3 <> Typography.serializePathData params
  
  DC.UpdateAnimationState params -> writeU8 0x24 <> pad 3 <> Typography.serializeAnimationState params
  
  -- Media commands (opcodes 0x30-0x32)
  DC.DrawImage params -> writeU8 0x30 <> pad 3 <> Media.serializeImage params
  
  DC.DrawVideo params -> writeU8 0x31 <> pad 3 <> Media.serializeVideo params
  
  DC.Draw3D params -> writeU8 0x32 <> pad 3 <> Media.serialize3D params

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // primitive serializers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize DrawRect payload.
serializeRect :: forall msg. DC.RectParams msg -> Array Int
serializeRect p =
  let
    rgb = RGB.fromRGBA p.fill
  in
    -- Position and size (bounded coordinate types)
    writeF32 (Coord.unwrapScreenX p.x)
    <> writeF32 (Coord.unwrapScreenY p.y)
    <> writeF32 (Coord.unwrapPixelWidth p.width)
    <> writeF32 (Coord.unwrapPixelHeight p.height)
    -- Color (unpacked to f32 for GPU, unit interval 0.0-1.0)
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.fill))
    -- Corner radii
    <> writeF32 (radiusToNumber p.cornerRadius.topLeft)
    <> writeF32 (radiusToNumber p.cornerRadius.topRight)
    <> writeF32 (radiusToNumber p.cornerRadius.bottomRight)
    <> writeF32 (radiusToNumber p.cornerRadius.bottomLeft)
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawQuad payload.
serializeQuad :: forall msg. DC.QuadParams msg -> Array Int
serializeQuad p =
  let
    rgb = RGB.fromRGBA p.fill
  in
    -- 4 vertices (Point2D uses Device.Pixel)
    writeF32 (unwrapPixel p.v0.x) <> writeF32 (unwrapPixel p.v0.y)
    <> writeF32 (unwrapPixel p.v1.x) <> writeF32 (unwrapPixel p.v1.y)
    <> writeF32 (unwrapPixel p.v2.x) <> writeF32 (unwrapPixel p.v2.y)
    <> writeF32 (unwrapPixel p.v3.x) <> writeF32 (unwrapPixel p.v3.y)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.fill))
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawGlyph payload.
serializeGlyph :: forall msg. DC.GlyphParams msg -> Array Int
serializeGlyph p =
  let
    rgb = RGB.fromRGBA p.color
  in
    -- Position (bounded coordinate types)
    writeF32 (Coord.unwrapScreenX p.x)
    <> writeF32 (Coord.unwrapScreenY p.y)
    <> writeU32 p.glyphIndex
    <> writeU32 p.fontId
    <> writeF32 (unwrapPixel p.fontSize)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.color))
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawParticle payload.
serializeParticle :: forall msg. DC.ParticleParams msg -> Array Int
serializeParticle p =
  let
    rgb = RGB.fromRGBA p.color
  in
    -- Position (bounded coordinate types)
    writeF32 (Coord.unwrapScreenX p.x)
    <> writeF32 (Coord.unwrapScreenY p.y)
    <> writeF32 (Coord.unwrapDepthValue p.z)
    <> writeF32 (unwrapPixel p.size)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.color))
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawPath payload (variable length).
-- |
-- | Wire format:
-- | - segmentCount: u32 (number of path segments)
-- | - fillPresent: u8 (1 = has fill, 0 = no fill)
-- | - strokePresent: u8 (1 = has stroke, 0 = no stroke)
-- | - padding: u16 (alignment)
-- | - [fill color if present]: 4 x f32
-- | - [stroke color if present]: 4 x f32
-- | - strokeWidth: f32
-- | - depth: f32
-- | - pickId: u32
-- | - [segments]: variable path segment data
serializePath :: forall msg. DC.PathParams msg -> Array Int
serializePath p =
  let
    segmentCount = Array.length p.segments
    fillPresent = case p.fill of
      Just _ -> 1
      Nothing -> 0
    strokePresent = case p.stroke of
      Just _ -> 1
      Nothing -> 0
  in
    -- Header
    writeU32 segmentCount
    <> writeU8 fillPresent
    <> writeU8 strokePresent
    <> writeU16 0  -- padding for alignment
    -- Fill color (if present)
    <> serializeMaybeColor p.fill
    -- Stroke color (if present)
    <> serializeMaybeColor p.stroke
    -- Stroke width
    <> writeF32 (unwrapPixel p.strokeWidth)
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)
    -- Path segments
    <> Array.concatMap serializePathSegment p.segments

-- | Serialize an optional color (RGBA as 4 x f32, or nothing).
serializeMaybeColor :: Maybe RGB.RGBA -> Array Int
serializeMaybeColor = case _ of
  Nothing -> []
  Just rgba ->
    let rgb = RGB.fromRGBA rgba
    in writeF32 (Channel.toUnitInterval (RGB.red rgb))
       <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
       <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
       <> writeF32 (Opacity.toUnitInterval (RGB.alpha rgba))

-- | Serialize ClipRegion payload.
-- |
-- | Wire format for ClipRect:
-- | - subtype: u8 = 0x00 (rectangle)
-- | - padding: u8[3]
-- | - x, y, width, height: 4 x f32
-- | - cornerRadii: 4 x f32 (topLeft, topRight, bottomRight, bottomLeft)
-- |
-- | Wire format for ClipPath:
-- | - subtype: u8 = 0x01 (path)
-- | - padding: u8[3]
-- | - segmentCount: u32
-- | - [segments]: variable path segment data
serializeClipRegion :: DC.ClipRegion -> Array Int
serializeClipRegion = case _ of
  DC.ClipRect rect ->
    writeU8 0x00  -- subtype: rectangle
    <> pad 3      -- alignment padding
    -- Position and size
    <> writeF32 (unwrapPixel rect.x)
    <> writeF32 (unwrapPixel rect.y)
    <> writeF32 (unwrapPixel rect.width)
    <> writeF32 (unwrapPixel rect.height)
    -- Corner radii
    <> writeF32 (radiusToNumber rect.cornerRadius.topLeft)
    <> writeF32 (radiusToNumber rect.cornerRadius.topRight)
    <> writeF32 (radiusToNumber rect.cornerRadius.bottomRight)
    <> writeF32 (radiusToNumber rect.cornerRadius.bottomLeft)
  
  DC.ClipPath segments ->
    let segmentCount = Array.length segments
    in writeU8 0x01  -- subtype: path
       <> pad 3       -- alignment padding
       <> writeU32 segmentCount
       <> Array.concatMap serializePathSegment segments

-- | Serialize a path segment.
serializePathSegment :: DC.PathSegment -> Array Int
serializePathSegment = case _ of
  DC.MoveTo pt -> 
    writeU8 0x01 <> pad 3
    <> writeF32 (unwrapPixel pt.x)
    <> writeF32 (unwrapPixel pt.y)
  
  DC.LineTo pt ->
    writeU8 0x02 <> pad 3
    <> writeF32 (unwrapPixel pt.x)
    <> writeF32 (unwrapPixel pt.y)
  
  DC.QuadraticTo ctrl end ->
    writeU8 0x03 <> pad 3
    <> writeF32 (unwrapPixel ctrl.x)
    <> writeF32 (unwrapPixel ctrl.y)
    <> writeF32 (unwrapPixel end.x)
    <> writeF32 (unwrapPixel end.y)
  
  DC.CubicTo c1 c2 end ->
    writeU8 0x04 <> pad 3
    <> writeF32 (unwrapPixel c1.x)
    <> writeF32 (unwrapPixel c1.y)
    <> writeF32 (unwrapPixel c2.x)
    <> writeF32 (unwrapPixel c2.y)
    <> writeF32 (unwrapPixel end.x)
    <> writeF32 (unwrapPixel end.y)
  
  DC.ClosePath ->
    writeU8 0x05 <> pad 3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Padding bytes for alignment.
pad :: Int -> Array Int
pad n = Array.replicate n 0

-- | Unwrap Pixel to Number.
unwrapPixel :: Device.Pixel -> Number
unwrapPixel (Device.Pixel n) = n

-- | Convert Radius to Number (pixels).
radiusToNumber :: Radius.Radius -> Number
radiusToNumber = case _ of
  Radius.RadiusPx n -> n
  Radius.RadiusPercent n -> n  -- Runtime resolves to pixels
  Radius.RadiusRem n -> n * 16.0  -- Assume 16px base
  Radius.RadiusFull -> 9999.0
  Radius.RadiusNone -> 0.0

-- | Convert Maybe PickId to Int (0 = no hit).
pickIdToInt :: Maybe DC.PickId -> Int
pickIdToInt = case _ of
  Nothing -> 0
  Just pid -> DC.unwrapPickId pid
