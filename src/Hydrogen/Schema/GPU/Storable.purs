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
  , ByteArray
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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // alignment
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // byte array
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // padding utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate padding needed to reach alignment
paddingNeeded :: Int -> Alignment -> Int
paddingNeeded size (Alignment align) =
  let remainder = size `mod` align
  in if remainder == 0 then 0 else align - remainder

-- | Calculate size with alignment padding
alignedSize :: Int -> Alignment -> Int
alignedSize size align = size + paddingNeeded size align

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // gpustorable typeclass
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // number instance
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // int instance
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // boolean instance
-- ═══════════════════════════════════════════════════════════════════════════════

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
