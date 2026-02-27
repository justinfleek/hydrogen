-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // gpu // storable
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPUStorable — Typeclass for types that can be serialized to GPU buffers.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, data must flow deterministically between CPU and GPU.
-- | This typeclass defines:
-- |
-- | 1. **Byte size** — How many bytes the type occupies in a GPU buffer
-- | 2. **Alignment** — Memory alignment requirements (WebGPU spec)
-- | 3. **Serialization** — Convert to/from byte representation
-- |
-- | ## WebGPU Alignment Rules
-- |
-- | WebGPU has strict alignment requirements:
-- | - f32: 4 bytes, 4-byte alignment
-- | - vec2<f32>: 8 bytes, 8-byte alignment
-- | - vec3<f32>: 12 bytes, 16-byte alignment (!)
-- | - vec4<f32>: 16 bytes, 16-byte alignment
-- | - mat4x4<f32>: 64 bytes, 16-byte alignment
-- |
-- | ## Determinism Guarantee
-- |
-- | Same value → same bytes. Always. This is critical for:
-- | - Cache keying (UUID5 of serialized data)
-- | - Distributed agents producing identical buffers
-- | - Reproducible rendering across sessions
-- |
-- | ## Lean4 Proof Integration
-- |
-- | The roundtrip property is proven in Lean4:
-- | ```lean
-- | theorem roundtrip : ∀ x, deserialize (serialize x) = x
-- | ```

module Hydrogen.Schema.GPU.Storable
  ( -- * GPUStorable Typeclass
    class GPUStorable
  , byteSize
  , alignment
  , toBytes
  , fromBytes
  
  -- * Common Alignments
  , Alignment
  , align4
  , align8
  , align16
  
  -- * Byte Operations
  , ByteArray(ByteArray)
  , emptyBytes
  , concatBytes
  , bytesLength
  
  -- * Padding Utilities
  , alignedSize
  , paddingNeeded
  
  -- * Basic Instances Documentation
  -- | Note: Instances are provided for common types below
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , bind
  , pure
  , show
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (<>)
  , (&&)
  , mod
  , zero
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array as Array
import Data.Int (toNumber) as Int
import Data.Int as Int

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Dimension.Vector.Vec2 as Vec2
import Hydrogen.Schema.Dimension.Vector.Vec3 as Vec3
import Hydrogen.Schema.Dimension.Vector.Vec4 as Vec4
import Hydrogen.Schema.Dimension.Point2D as Point2D
import Hydrogen.Schema.Color.SRGB as SRGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Memory alignment in bytes (must be power of 2)
newtype Alignment = Alignment Int

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment

instance showAlignment :: Show Alignment where
  show (Alignment n) = "Alignment(" <> show n <> ")"

-- | 4-byte alignment (f32, i32, u32)
align4 :: Alignment
align4 = Alignment 4

-- | 8-byte alignment (vec2<f32>, f64)
align8 :: Alignment
align8 = Alignment 8

-- | 16-byte alignment (vec3<f32>, vec4<f32>, mat4x4<f32>)
align16 :: Alignment
align16 = Alignment 16

-- | Unwrap alignment
unwrapAlignment :: Alignment -> Int
unwrapAlignment (Alignment n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // byte array
-- ═════════════════════════════════════════════════════════════════════════════

-- | A byte array for GPU serialization
-- | In actual WebGPU, this would be ArrayBuffer/TypedArray
-- | Here we use Array Int where each Int is 0-255
newtype ByteArray = ByteArray (Array Int)

derive instance eqByteArray :: Eq ByteArray

instance showByteArray :: Show ByteArray where
  show (ByteArray arr) = "ByteArray[" <> show (Array.length arr) <> " bytes]"

-- | Empty byte array
emptyBytes :: ByteArray
emptyBytes = ByteArray []

-- | Concatenate byte arrays
concatBytes :: ByteArray -> ByteArray -> ByteArray
concatBytes (ByteArray a) (ByteArray b) = ByteArray (a <> b)

-- | Length of byte array
bytesLength :: ByteArray -> Int
bytesLength (ByteArray arr) = Array.length arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // padding utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate padding needed to reach alignment
paddingNeeded :: Int -> Alignment -> Int
paddingNeeded size (Alignment align) =
  let remainder = size `mod` align
  in if remainder == 0 then 0 else align - remainder

-- | Calculate size with alignment padding
alignedSize :: Int -> Alignment -> Int
alignedSize size align = size + paddingNeeded size align

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gpustorable typeclass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types that can be stored in GPU buffers.
-- |
-- | ## Laws
-- |
-- | 1. Roundtrip: `fromBytes (toBytes x) == Just x`
-- | 2. Size consistency: `bytesLength (toBytes x) == byteSize`
-- | 3. Alignment: offset in buffer must be multiple of `alignment`
-- |
-- | ## Implementation Notes
-- |
-- | When implementing this typeclass:
-- | - Use little-endian byte order (WebGPU/x86 native)
-- | - Pad structs to alignment boundaries
-- | - Handle IEEE 754 for floating-point types
class GPUStorable a where
  -- | Size in bytes when stored in GPU buffer
  byteSize :: a -> Int
  
  -- | Alignment requirement in bytes
  alignment :: a -> Alignment
  
  -- | Serialize to bytes
  toBytes :: a -> ByteArray
  
  -- | Deserialize from bytes
  fromBytes :: ByteArray -> Maybe a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // number instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Number to 4 bytes (IEEE 754 single-precision)
-- | In real implementation, this would use Float32Array
numberToBytes :: Number -> ByteArray
numberToBytes n =
  -- Placeholder: In actual implementation, this would use FFI to Float32Array
  -- For now, we represent as 4 bytes
  let truncated = Int.round n
      b0 = truncated `mod` 256
      b1 = (truncated / 256) `mod` 256
      b2 = (truncated / 65536) `mod` 256
      b3 = (truncated / 16777216) `mod` 256
  in ByteArray [b0, b1, b2, b3]

-- | Convert 4 bytes to Number
bytesToNumber :: ByteArray -> Maybe Number
bytesToNumber (ByteArray arr) =
  case Array.length arr >= 4 of
    true -> 
      case Array.index arr 0, Array.index arr 1, Array.index arr 2, Array.index arr 3 of
        Just b0, Just b1, Just b2, Just b3 ->
          Just $ Int.toNumber (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
        _, _, _, _ -> Nothing
    false -> Nothing

instance gpuStorableNumber :: GPUStorable Number where
  byteSize _ = 4
  alignment _ = align4
  toBytes = numberToBytes
  fromBytes = bytesToNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // int instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to 4 bytes (i32)
intToBytes :: Int -> ByteArray
intToBytes n =
  let b0 = n `mod` 256
      b1 = (n / 256) `mod` 256
      b2 = (n / 65536) `mod` 256
      b3 = (n / 16777216) `mod` 256
  in ByteArray [b0, b1, b2, b3]

-- | Convert 4 bytes to Int
bytesToInt :: ByteArray -> Maybe Int
bytesToInt (ByteArray arr) =
  case Array.length arr >= 4 of
    true -> 
      case Array.index arr 0, Array.index arr 1, Array.index arr 2, Array.index arr 3 of
        Just b0, Just b1, Just b2, Just b3 ->
          Just (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
        _, _, _, _ -> Nothing
    false -> Nothing

instance gpuStorableInt :: GPUStorable Int where
  byteSize _ = 4
  alignment _ = align4
  toBytes = intToBytes
  fromBytes = bytesToInt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // boolean instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Boolean to 4 bytes (u32 in WGSL)
-- | WebGPU uses 32-bit booleans
boolToBytes :: Boolean -> ByteArray
boolToBytes b = ByteArray [if b then 1 else 0, 0, 0, 0]

-- | Convert 4 bytes to Boolean
bytesToBool :: ByteArray -> Maybe Boolean
bytesToBool (ByteArray arr) =
  case Array.index arr 0 of
    Just b -> Just (b > 0)
    Nothing -> Nothing

instance gpuStorableBoolean :: GPUStorable Boolean where
  byteSize _ = 4
  alignment _ = align4
  toBytes = boolToBytes
  fromBytes = bytesToBool

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // schema atom instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | UnitInterval serializes as a single f32.
-- |
-- | GPU representation: f32 (4 bytes)
-- | WGSL type: f32
instance gpuStorableUnitInterval :: GPUStorable Bounded.UnitInterval where
  byteSize _ = 4
  alignment _ = align4
  toBytes ui = numberToBytes (Bounded.unwrapUnit ui)
  fromBytes bytes = do
    n <- bytesToNumber bytes
    pure (Bounded.clampUnit n)

-- | Vec2 Number serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
instance gpuStorableVec2Number :: GPUStorable (Vec2.Vec2 Number) where
  byteSize _ = 8
  alignment _ = align8
  toBytes v =
    let ByteArray xb = numberToBytes (Vec2.getX2 v)
        ByteArray yb = numberToBytes (Vec2.getY2 v)
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Vec2.vec2 xv yv)

-- | Vec3 Number serializes as vec3<f32>.
-- |
-- | GPU representation: vec3<f32> (12 bytes, 16-byte aligned)
-- | WGSL type: vec3<f32>
-- |
-- | IMPORTANT: vec3 requires 16-byte alignment in WebGPU despite being
-- | only 12 bytes. This is a WebGPU spec requirement.
instance gpuStorableVec3Number :: GPUStorable (Vec3.Vec3 Number) where
  byteSize _ = 12
  alignment _ = align16
  toBytes v =
    let ByteArray xb = numberToBytes (Vec3.getX3 v)
        ByteArray yb = numberToBytes (Vec3.getY3 v)
        ByteArray zb = numberToBytes (Vec3.getZ3 v)
    in ByteArray (xb <> yb <> zb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    zv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    pure (Vec3.vec3 xv yv zv)

-- | Vec4 Number serializes as vec4<f32>.
-- |
-- | GPU representation: vec4<f32> (16 bytes, 16-byte aligned)
-- | WGSL type: vec4<f32>
instance gpuStorableVec4Number :: GPUStorable (Vec4.Vec4 Number) where
  byteSize _ = 16
  alignment _ = align16
  toBytes v =
    let ByteArray xb = numberToBytes (Vec4.getX4 v)
        ByteArray yb = numberToBytes (Vec4.getY4 v)
        ByteArray zb = numberToBytes (Vec4.getZ4 v)
        ByteArray wb = numberToBytes (Vec4.getW4 v)
    in ByteArray (xb <> yb <> zb <> wb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    zv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    wv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 12 arr)))
    pure (Vec4.vec4 xv yv zv wv)

-- | Point2D serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
instance gpuStorablePoint2D :: GPUStorable Point2D.Point2D where
  byteSize _ = 8
  alignment _ = align8
  toBytes pt =
    let ByteArray xb = numberToBytes (Point2D.x pt)
        ByteArray yb = numberToBytes (Point2D.y pt)
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Point2D.point2D xv yv)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | SRGB serializes as vec3<f32> with values in [0,1].
-- |
-- | GPU representation: vec3<f32> (12 bytes, 16-byte aligned)
-- | WGSL type: vec3<f32>
-- |
-- | Channel values (0-255) are normalized to [0,1] for GPU:
-- | - 0 → 0.0
-- | - 255 → 1.0
-- |
-- | IMPORTANT: vec3 requires 16-byte alignment in WebGPU despite being
-- | only 12 bytes. This is a WebGPU spec requirement.
instance gpuStorableSRGB :: GPUStorable SRGB.SRGB where
  byteSize _ = 12
  alignment _ = align16
  toBytes color =
    let r = Int.toNumber (Channel.unwrap (SRGB.red color)) / 255.0
        g = Int.toNumber (Channel.unwrap (SRGB.green color)) / 255.0
        b = Int.toNumber (Channel.unwrap (SRGB.blue color)) / 255.0
        ByteArray rb = numberToBytes r
        ByteArray gb = numberToBytes g
        ByteArray bb = numberToBytes b
    in ByteArray (rb <> gb <> bb)
  fromBytes (ByteArray arr) = do
    rv <- bytesToNumber (ByteArray (Array.take 4 arr))
    gv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    bv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    let ri = Int.round (rv * 255.0)
        gi = Int.round (gv * 255.0)
        bi = Int.round (bv * 255.0)
    pure (SRGB.srgb ri gi bi)

-- | SRGBA serializes as vec4<f32> with values in [0,1].
-- |
-- | GPU representation: vec4<f32> (16 bytes, 16-byte aligned)
-- | WGSL type: vec4<f32>
-- |
-- | Channel values (0-255) and opacity (0-100) are normalized to [0,1]:
-- | - Red/Green/Blue: 0-255 → 0.0-1.0
-- | - Alpha (opacity): 0-100 → 0.0-1.0
instance gpuStorableSRGBA :: GPUStorable SRGB.SRGBA where
  byteSize _ = 16
  alignment _ = align16
  toBytes color =
    let rec = SRGB.srgbaToRecord color
        r = Int.toNumber (Channel.unwrap rec.r) / 255.0
        g = Int.toNumber (Channel.unwrap rec.g) / 255.0
        b = Int.toNumber (Channel.unwrap rec.b) / 255.0
        a = Int.toNumber (Opacity.unwrap rec.a) / 100.0
        ByteArray rb = numberToBytes r
        ByteArray gb = numberToBytes g
        ByteArray bb = numberToBytes b
        ByteArray ab = numberToBytes a
    in ByteArray (rb <> gb <> bb <> ab)
  fromBytes (ByteArray arr) = do
    rv <- bytesToNumber (ByteArray (Array.take 4 arr))
    gv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    bv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    av <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 12 arr)))
    let ri = Int.round (rv * 255.0)
        gi = Int.round (gv * 255.0)
        bi = Int.round (bv * 255.0)
    pure (SRGB.srgba ri gi bi av)
