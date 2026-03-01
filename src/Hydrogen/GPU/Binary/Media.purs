-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // gpu // binary // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Media serializers for GPU commands.
-- |
-- | This module provides serialization for media commands:
-- | DrawImage, DrawVideo, and Draw3D.
-- |
-- | ## Wire Format
-- |
-- | Media commands use opcodes 0x30-0x32 and include variable-length
-- | URL payloads.

module Hydrogen.GPU.Binary.Media
  ( -- * Media serializers
    serializeImage
  , serializeVideo
  , serialize3D
  ) where

import Prelude
  ( (<>)
  )

import Data.Array (length, replicate) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.GPU.Binary.LowLevel (writeF32, writeU32, writeU8, stringToBytes)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // media serializers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize DrawImage payload.
-- |
-- | Wire format:
-- | - url length: u32
-- | - url bytes: variable (ASCII)
-- | - x, y, width, height: 4 x f32
-- | - depth: f32
-- | - pickId: u32
serializeImage :: forall msg. DC.ImageParams msg -> Array Int
serializeImage p =
  let
    urlBytes = stringToBytes p.url
    urlLen = Array.length urlBytes
  in
    writeU32 urlLen
    <> urlBytes
    -- Position and size (bounded coordinate types)
    <> writeF32 (Coord.unwrapScreenX p.x)
    <> writeF32 (Coord.unwrapScreenY p.y)
    <> writeF32 (Coord.unwrapPixelWidth p.width)
    <> writeF32 (Coord.unwrapPixelHeight p.height)
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawVideo payload.
-- |
-- | Wire format:
-- | - url length: u32
-- | - url bytes: variable (ASCII)
-- | - x, y, width, height: 4 x f32
-- | - currentTime: f32
-- | - playing: u8 (boolean)
-- | - padding: 3 bytes
-- | - depth: f32
-- | - pickId: u32
serializeVideo :: forall msg. DC.VideoParams msg -> Array Int
serializeVideo p =
  let
    urlBytes = stringToBytes p.url
    urlLen = Array.length urlBytes
    playingFlag = if p.playing then 1 else 0
  in
    writeU32 urlLen
    <> urlBytes
    -- Position and size (bounded coordinate types)
    <> writeF32 (Coord.unwrapScreenX p.x)
    <> writeF32 (Coord.unwrapScreenY p.y)
    <> writeF32 (Coord.unwrapPixelWidth p.width)
    <> writeF32 (Coord.unwrapPixelHeight p.height)
    -- currentTime (bounded NormalizedX)
    <> writeF32 (Coord.unwrapNormalizedX p.currentTime)
    <> writeU8 playingFlag
    <> pad 3
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize Draw3D payload.
-- |
-- | Wire format:
-- | - url length: u32
-- | - url bytes: variable (ASCII)
-- | - x, y, width, height: 4 x f32
-- | - camera (distance, azimuth, elevation, fov): 4 x f32
-- | - animationProgress: f32
-- | - depth: f32
-- | - pickId: u32
serialize3D :: forall msg. DC.Model3DParams msg -> Array Int
serialize3D p =
  let
    urlBytes = stringToBytes p.url
    urlLen = Array.length urlBytes
  in
    writeU32 urlLen
    <> urlBytes
    -- Position and size (bounded coordinate types)
    <> writeF32 (Coord.unwrapScreenX p.x)
    <> writeF32 (Coord.unwrapScreenY p.y)
    <> writeF32 (Coord.unwrapPixelWidth p.width)
    <> writeF32 (Coord.unwrapPixelHeight p.height)
    -- Camera params (unbounded Numbers)
    <> writeF32 p.cameraDistance
    <> writeF32 p.cameraAzimuth
    <> writeF32 p.cameraElevation
    <> writeF32 p.cameraFov
    -- animationProgress (bounded NormalizedX)
    <> writeF32 (Coord.unwrapNormalizedX p.animationProgress)
    -- Depth (bounded)
    <> writeF32 (Coord.unwrapDepthValue p.depth)
    <> writeU32 (pickIdToInt p.pickId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Padding bytes for alignment.
pad :: Int -> Array Int
pad n = Array.replicate n 0

-- | Convert Maybe PickId to Int (0 = no hit).
pickIdToInt :: Maybe DC.PickId -> Int
pickIdToInt = case _ of
  Nothing -> 0
  Just pid -> DC.unwrapPickId pid
