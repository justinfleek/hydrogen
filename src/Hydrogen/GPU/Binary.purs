-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // gpu // binary
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Serialization Format for GPU Commands
-- |
-- | This module defines the binary wire format for DrawCommands. Any GPU
-- | runtime that consumes Hydrogen output reads this format.
-- |
-- | ## Design Principles
-- |
-- | 1. **Fixed-size records**: Every command type has a known byte size.
-- |    No variable-length encoding on the hot path.
-- |
-- | 2. **Little-endian**: Matches WebGPU/native GPU expectations.
-- |
-- | 3. **Aligned**: All fields are naturally aligned (f32 on 4-byte, etc.)
-- |
-- | 4. **Deterministic**: Same DrawCommand produces identical bytes.
-- |    Enables caching, hashing, deduplication.
-- |
-- | 5. **Schema atoms map to GPU types**:
-- |    - Pixel → f32
-- |    - RGB channels → u8 (packed) or f32 (unpacked)
-- |    - PickId → u32
-- |    - Radius → f32
-- |
-- | ## Wire Format Overview
-- |
-- | ```
-- | CommandBuffer := Header + Array Command
-- |
-- | Header (16 bytes):
-- |   magic     : u32 = 0x48594447 ("HYDG")
-- |   version   : u32 = 1
-- |   count     : u32 = number of commands
-- |   flags     : u32 = reserved
-- |
-- | Command := CommandType (u8) + Padding (alignment) + Payload
-- |
-- | CommandType:
-- |   0x01 = DrawRect
-- |   0x02 = DrawQuad
-- |   0x03 = DrawGlyph
-- |   0x04 = DrawPath (variable size - stored separately)
-- |   0x05 = DrawParticle
-- |   0x10 = PushClip
-- |   0x11 = PopClip
-- |   0x00 = Noop
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.GPU.Binary as Binary
-- | import Hydrogen.GPU.DrawCommand as DC
-- |
-- | -- Serialize a command buffer
-- | bytes :: Binary.Bytes
-- | bytes = Binary.serialize commands
-- |
-- | -- Get raw byte array for transmission
-- | raw :: Array Int
-- | raw = Binary.toByteArray bytes
-- | ```

module Hydrogen.GPU.Binary
  ( -- * Types
    Bytes
  , Header
  , CommandType(..)
  
  -- * Constants
  , magic
  , version
  , headerSize
  , rectPayloadSize
  , quadPayloadSize
  , glyphPayloadSize
  , particlePayloadSize
  
  -- * Serialization
  , serialize
  , serializeHeader
  , serializeCommand
  , serializeRect
  , serializeQuad
  , serializeGlyph
  , serializeParticle
  
  -- * Deserialization
  , deserialize
  , deserializeHeader
  , deserializeCommand
  
  -- * Low-level
  , toByteArray
  , fromByteArray
  , writeF32
  , writeU32
  , writeU8
  , readF32
  , readU32
  , readU8
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , bind
  , map
  , mod
  , negate
  , otherwise
  , pure
  , show
  , ($)
  , (&&)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (*)
  )

import Data.Array as Array
import Data.Int (floor, toNumber)
import Data.Int.Bits (shl, shr, (.&.), (.|.))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Raw bytes as array of integers (0-255).
-- | This is the pure representation — actual TypedArray created at boundary.
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes

instance showBytes :: Show Bytes where
  show (Bytes arr) = "Bytes[" <> show (Array.length arr) <> "]"

-- | Buffer header.
type Header =
  { magic :: Int      -- 0x48594447 "HYDG"
  , version :: Int    -- Format version
  , count :: Int      -- Number of commands
  , flags :: Int      -- Reserved
  }

-- | Command type discriminant.
data CommandType
  = CmdNoop
  | CmdDrawRect
  | CmdDrawQuad
  | CmdDrawGlyph
  | CmdDrawPath
  | CmdDrawParticle
  | CmdPushClip
  | CmdPopClip

derive instance eqCommandType :: Eq CommandType
derive instance ordCommandType :: Ord CommandType

instance showCommandType :: Show CommandType where
  show CmdNoop = "Noop"
  show CmdDrawRect = "DrawRect"
  show CmdDrawQuad = "DrawQuad"
  show CmdDrawGlyph = "DrawGlyph"
  show CmdDrawPath = "DrawPath"
  show CmdDrawParticle = "DrawParticle"
  show CmdPushClip = "PushClip"
  show CmdPopClip = "PopClip"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Magic number: "HYDG" in little-endian ASCII
magic :: Int
magic = 0x48594447

-- | Current format version
version :: Int
version = 1

-- | Header size in bytes
headerSize :: Int
headerSize = 16

-- | DrawRect payload size (excluding command type byte)
-- | x, y, width, height: 4 × f32 = 16
-- | r, g, b, a: 4 × f32 = 16 (unpacked for GPU)
-- | cornerRadius (4 corners): 4 × f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 56 bytes + 4 alignment = 60 bytes
rectPayloadSize :: Int
rectPayloadSize = 60

-- | DrawQuad payload size
-- | 4 vertices × 2 coords × f32 = 32
-- | color: 4 × f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 56 bytes
quadPayloadSize :: Int
quadPayloadSize = 56

-- | DrawGlyph payload size
-- | x, y: 2 × f32 = 8
-- | glyphIndex: u32 = 4
-- | fontId: u32 = 4
-- | fontSize: f32 = 4
-- | color: 4 × f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 44 bytes
glyphPayloadSize :: Int
glyphPayloadSize = 44

-- | DrawParticle payload size
-- | x, y, z: 3 × f32 = 12
-- | size: f32 = 4
-- | color: 4 × f32 = 16
-- | pickId: u32 = 4
-- | Total: 36 bytes
particlePayloadSize :: Int
particlePayloadSize = 36

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // low level ops
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Bytes to raw byte array.
toByteArray :: Bytes -> Array Int
toByteArray (Bytes arr) = arr

-- | Create Bytes from raw byte array.
fromByteArray :: Array Int -> Bytes
fromByteArray = Bytes

-- | Write a 32-bit float as 4 bytes (little-endian).
-- | IEEE 754 single precision.
writeF32 :: Number -> Array Int
writeF32 n =
  let
    -- Convert float to IEEE 754 bits
    bits = floatToBits n
  in
    [ bits .&. 0xFF
    , (shr bits 8) .&. 0xFF
    , (shr bits 16) .&. 0xFF
    , (shr bits 24) .&. 0xFF
    ]

-- | Write a 32-bit unsigned integer as 4 bytes (little-endian).
writeU32 :: Int -> Array Int
writeU32 n =
  [ n .&. 0xFF
  , (shr n 8) .&. 0xFF
  , (shr n 16) .&. 0xFF
  , (shr n 24) .&. 0xFF
  ]

-- | Write an 8-bit unsigned integer.
writeU8 :: Int -> Array Int
writeU8 n = [n .&. 0xFF]

-- | Read a 32-bit float from bytes at offset.
readF32 :: Array Int -> Int -> Maybe Number
readF32 arr offset =
  case Array.index arr offset
     , Array.index arr (offset + 1)
     , Array.index arr (offset + 2)
     , Array.index arr (offset + 3) of
    Just b0, Just b1, Just b2, Just b3 ->
      let bits = b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24)
      in Just (bitsToFloat bits)
    _, _, _, _ -> Nothing

-- | Read a 32-bit unsigned integer from bytes at offset.
readU32 :: Array Int -> Int -> Maybe Int
readU32 arr offset =
  case Array.index arr offset
     , Array.index arr (offset + 1)
     , Array.index arr (offset + 2)
     , Array.index arr (offset + 3) of
    Just b0, Just b1, Just b2, Just b3 ->
      Just (b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24))
    _, _, _, _ -> Nothing

-- | Read an 8-bit unsigned integer from bytes at offset.
readU8 :: Array Int -> Int -> Maybe Int
readU8 arr offset = Array.index arr offset

-- | Convert float to IEEE 754 bits.
-- | Pure implementation without FFI.
floatToBits :: Number -> Int
floatToBits n
  | n == 0.0 = 0
  | otherwise =
      let
        sign = if n < 0.0 then 1 else 0
        absN = if n < 0.0 then negate n else n
        
        -- Find exponent and mantissa
        -- This is a simplified implementation
        -- For production, would need proper IEEE 754 handling
        logResult = log2Approx absN
        exp = floor logResult + 127
        mantissa = floor ((absN / pow2 (exp - 127) - 1.0) * 8388608.0)
      in
        (shl sign 31) .|. (shl (exp .&. 0xFF) 23) .|. (mantissa .&. 0x7FFFFF)
  where
    negate x = 0.0 - x

-- | Convert IEEE 754 bits to float.
bitsToFloat :: Int -> Number
bitsToFloat bits =
  let
    sign = shr bits 31
    exp = (shr bits 23) .&. 0xFF
    mantissa = bits .&. 0x7FFFFF
    
    signMult = if sign == 0 then 1.0 else (0.0 - 1.0)
  in
    if exp == 0 && mantissa == 0 then 0.0
    else signMult * pow2 (exp - 127) * (1.0 + toNumber mantissa / 8388608.0)

-- | Approximate log base 2.
log2Approx :: Number -> Number
log2Approx n = log n / log 2.0
  where
    log x = nativeLog x

-- | Power of 2.
pow2 :: Int -> Number
pow2 e = 
  if e >= 0 
    then pow2Positive e 1.0
    else 1.0 / pow2Positive (0 - e) 1.0
  where
    pow2Positive :: Int -> Number -> Number
    pow2Positive 0 acc = acc
    pow2Positive n acc = pow2Positive (n - 1) (acc * 2.0)

-- | Native log function (using series expansion for purity).
-- | For production, this would use a more efficient method.
nativeLog :: Number -> Number
nativeLog x = 
  if x == 1.0 
    then 0.0
  else if x > 0.0 && x < 2.0 
    then logSeries (x - 1.0) 1 0.0
  else if x >= 2.0 
    then log2Const + nativeLog (x / 2.0)
  else 0.0  -- Invalid input, return 0
  where
    log2Const :: Number
    log2Const = 0.6931471805599453
    
    logSeries :: Number -> Int -> Number -> Number
    logSeries _ 100 acc = acc  -- Limit iterations
    logSeries y n acc =
      let term = (if mod n 2 == 0 then (0.0 - 1.0) else 1.0) * powNum y n / toNumber n
      in logSeries y (n + 1) (acc + term)
    
    powNum :: Number -> Int -> Number
    powNum _ 0 = 1.0
    powNum base pexp = base * powNum base (pexp - 1)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Serialize a command buffer to bytes.
serialize :: forall msg. DC.CommandBuffer msg -> Bytes
serialize commands =
  let
    header = serializeHeader
      { magic: magic
      , version: version
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
  
  DC.DrawPath _ -> writeU8 0x04 <> pad 3  -- Path needs variable-size handling
  
  DC.DrawParticle params -> writeU8 0x05 <> pad 3 <> serializeParticle params
  
  DC.PushClip _ -> writeU8 0x10 <> pad 3  -- Clip needs expansion
  
  DC.PopClip -> writeU8 0x11 <> pad 3

-- | Padding bytes for alignment.
pad :: Int -> Array Int
pad n = Array.replicate n 0

-- | Serialize DrawRect payload.
serializeRect :: forall msg. DC.RectParams msg -> Array Int
serializeRect p =
  let
    rgb = RGB.fromRGBA p.fill
  in
    -- Position and size
    writeF32 (unwrapPixel p.x)
    <> writeF32 (unwrapPixel p.y)
    <> writeF32 (unwrapPixel p.width)
    <> writeF32 (unwrapPixel p.height)
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
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawQuad payload.
serializeQuad :: forall msg. DC.QuadParams msg -> Array Int
serializeQuad p =
  let
    rgb = RGB.fromRGBA p.fill
  in
    -- 4 vertices
    writeF32 (unwrapPixel p.v0.x) <> writeF32 (unwrapPixel p.v0.y)
    <> writeF32 (unwrapPixel p.v1.x) <> writeF32 (unwrapPixel p.v1.y)
    <> writeF32 (unwrapPixel p.v2.x) <> writeF32 (unwrapPixel p.v2.y)
    <> writeF32 (unwrapPixel p.v3.x) <> writeF32 (unwrapPixel p.v3.y)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.fill))
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawGlyph payload.
serializeGlyph :: forall msg. DC.GlyphParams msg -> Array Int
serializeGlyph p =
  let
    rgb = RGB.fromRGBA p.color
  in
    writeF32 (unwrapPixel p.x)
    <> writeF32 (unwrapPixel p.y)
    <> writeU32 p.glyphIndex
    <> writeU32 p.fontId
    <> writeF32 (unwrapPixel p.fontSize)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.color))
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawParticle payload.
serializeParticle :: forall msg. DC.ParticleParams msg -> Array Int
serializeParticle p =
  let
    rgb = RGB.fromRGBA p.color
  in
    writeF32 (unwrapPixel p.x)
    <> writeF32 (unwrapPixel p.y)
    <> writeF32 p.z
    <> writeF32 (unwrapPixel p.size)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.color))
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // deserialization
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Deserialize bytes to command buffer.
-- | Returns Nothing if invalid format.
deserialize :: Bytes -> Maybe (Tuple Header (Array (DC.DrawCommand Unit)))
deserialize (Bytes arr) = do
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
    0x01 -> Just (Tuple DC.Noop (offset + 4 + rectPayloadSize))  -- Placeholder
    _ -> Nothing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

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
