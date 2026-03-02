-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // binary // deserialize
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deserialization for GPU command buffers.
-- |
-- | This module provides functions to parse binary GPU command buffers
-- | back into DrawCommand structures.

module Hydrogen.GPU.Binary.Deserialize
  ( -- * Deserialization
    deserialize
  , deserializeHeader
  , deserializeCommand
  ) where

import Prelude
  ( Unit
  , bind
  , pure
  , (+)
  , (-)
  , (*)
  , (>=)
  , (==)
  )

import Data.Int (floor, toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.GPU.Binary.Constants (magic, rectPayloadSize)
import Hydrogen.GPU.Binary.LowLevel (readU32, readU8, readF32, toByteArray)
import Hydrogen.GPU.Binary.Types (Bytes, Header)
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize bytes to command buffer.
-- | Returns Nothing if invalid format.
deserialize :: Bytes -> Maybe (Tuple Header (Array (DC.DrawCommand Unit)))
deserialize bytes = do
  let arr = toByteArray bytes
  header <- deserializeHeader arr
  -- For now, return header only - full deserialization needs more work
  pure (Tuple header [])

-- | Deserialize header.
deserializeHeader :: Array Int -> Maybe Header
deserializeHeader arr = do
  m <- readU32 arr 0
  v <- readU32 arr 4
  c <- readU32 arr 8
  f <- readU32 arr 12
  if m == magic
    then Just { magic: m, version: v, count: c, flags: f }
    else Nothing

-- | Deserialize a single command at offset.
-- | Returns the command and new offset.
deserializeCommand :: Array Int -> Int -> Maybe (Tuple (DC.DrawCommand Unit) Int)
deserializeCommand arr offset = do
  cmdType <- readU8 arr offset
  case cmdType of
    0x00 -> Just (Tuple DC.Noop (offset + 1))
    0x01 -> deserializeRect arr (offset + 4)
    _ -> Nothing

-- | Deserialize DrawRect command from byte array.
-- | Layout: x, y, width, height (4xf32), r, g, b, a (4xf32), 
-- |         cornerRadius (4xf32), depth (f32), pickId (u32)
deserializeRect :: Array Int -> Int -> Maybe (Tuple (DC.DrawCommand Unit) Int)
deserializeRect arr offset = do
  -- Position and size
  xVal <- readF32 arr offset
  yVal <- readF32 arr (offset + 4)
  wVal <- readF32 arr (offset + 8)
  hVal <- readF32 arr (offset + 12)
  -- Color (normalized 0-1 -> 0-255)
  rVal <- readF32 arr (offset + 16)
  gVal <- readF32 arr (offset + 20)
  bVal <- readF32 arr (offset + 24)
  aVal <- readF32 arr (offset + 28)
  -- Corner radius
  tlVal <- readF32 arr (offset + 32)
  trVal <- readF32 arr (offset + 36)
  brVal <- readF32 arr (offset + 40)
  blVal <- readF32 arr (offset + 44)
  -- Depth
  depthVal <- readF32 arr (offset + 48)
  -- PickId
  pickIdVal <- readU32 arr (offset + 52)
  
  let params = 
        { x: Coord.screenX xVal
        , y: Coord.screenY yVal
        , width: Coord.pixelWidth wVal
        , height: Coord.pixelHeight hVal
        , fill: RGB.rgba (floatToInt255 rVal) (floatToInt255 gVal) (floatToInt255 bVal) (floatToInt100 aVal)
        , cornerRadius: Radius.corners 
            (Radius.RadiusPx tlVal) 
            (Radius.RadiusPx trVal) 
            (Radius.RadiusPx brVal) 
            (Radius.RadiusPx blVal)
        , depth: Coord.depthValue depthVal
        , pickId: if pickIdVal == 0 then Nothing else Just (DC.pickId pickIdVal)
        , onClick: Nothing
        }
  pure (Tuple (DC.DrawRect params) (offset + rectPayloadSize))
  where
    -- Convert normalized float (0.0-1.0) to channel value (0-255)
    floatToInt255 :: Number -> Int
    floatToInt255 f = roundToInt (f * 255.0)
    
    -- Convert normalized float (0.0-1.0) to opacity (0-100)
    floatToInt100 :: Number -> Int
    floatToInt100 f = roundToInt (f * 100.0)
    
    -- Simple rounding function using Data.Int.floor
    roundToInt :: Number -> Int
    roundToInt n = 
      let base = Int.floor n
          frac = n - Int.toNumber base
      in if frac >= 0.5 then base + 1 else base
