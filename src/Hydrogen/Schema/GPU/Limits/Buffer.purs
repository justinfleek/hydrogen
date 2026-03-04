-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // gpu // limits // buffer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Buffer Limits — Bounded types for WebGPU buffer constraints.
-- |
-- | ## Memory Safety
-- |
-- | Buffer sizes and offsets must be bounded to prevent:
-- | - Memory exhaustion attacks
-- | - Integer overflow in size calculations
-- | - Out-of-bounds access
-- |
-- | ## WebGPU Specification Bounds
-- |
-- | - maxBufferSize: 268435456 (256 MB)
-- | - maxUniformBufferBindingSize: 65536 (64 KB)
-- | - maxStorageBufferBindingSize: 134217728 (128 MB)
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.GPU.Limits.Buffer
  ( -- * Buffer Size
    BufferSize
  , bufferSize
  , clampBufferSize
  , unwrapBufferSize
  , bufferSizeBounds
  , bufferSizeZero
  , bufferSizeKB
  , bufferSizeMB
  
  -- * Buffer Offset
  , BufferOffset
  , bufferOffset
  , clampBufferOffset
  , unwrapBufferOffset
  , bufferOffsetBounds
  
  -- * Uniform Buffer Binding Size
  , UniformBufferBindingSize
  , uniformBufferBindingSize
  , clampUniformBufferBindingSize
  , unwrapUniformBufferBindingSize
  , uniformBufferBindingSizeBounds
  
  -- * Storage Buffer Binding Size
  , StorageBufferBindingSize
  , storageBufferBindingSize
  , clampStorageBufferBindingSize
  , unwrapStorageBufferBindingSize
  , storageBufferBindingSizeBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (>=)
  , (<=)
  , (&&)
  , (*)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , IntBounds
  , intBounds
  , clampInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // buffer size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer size in bytes.
-- |
-- | Bounds: 0 to 268435456 (256 MB, WebGPU guaranteed minimum for maxBufferSize)
-- |
-- | This is the maximum size for a single GPU buffer. For larger data sets,
-- | use multiple buffers or streaming techniques.
newtype BufferSize = BufferSize Int

derive instance eqBufferSize :: Eq BufferSize
derive instance ordBufferSize :: Ord BufferSize

instance showBufferSize :: Show BufferSize where
  show (BufferSize n) = "BufferSize(" <> show n <> " bytes)"

-- | Bounds specification for buffer size.
bufferSizeBounds :: IntBounds
bufferSizeBounds = intBounds 0 268435456 Clamps "bufferSize" "Buffer size (0-256MB)"

-- | Smart constructor with validation.
bufferSize :: Int -> Maybe BufferSize
bufferSize n
  | n >= 0 && n <= 268435456 = Just (BufferSize n)
  | otherwise = Nothing

-- | Clamping constructor.
clampBufferSize :: Int -> BufferSize
clampBufferSize n = BufferSize (clampInt 0 268435456 n)

-- | Extract the underlying Int value.
unwrapBufferSize :: BufferSize -> Int
unwrapBufferSize (BufferSize n) = n

-- | Zero-sized buffer (empty).
bufferSizeZero :: BufferSize
bufferSizeZero = BufferSize 0

-- | Construct buffer size from kilobytes.
-- |
-- | Clamps to max 256 MB if the result exceeds the limit.
bufferSizeKB :: Int -> BufferSize
bufferSizeKB kb = clampBufferSize (kb * 1024)

-- | Construct buffer size from megabytes.
-- |
-- | Clamps to max 256 MB if the result exceeds the limit.
bufferSizeMB :: Int -> BufferSize
bufferSizeMB mb = clampBufferSize (mb * 1024 * 1024)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // buffer offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer offset in bytes.
-- |
-- | Bounds: 0 to 268435456 (same as buffer size)
-- |
-- | Offsets into buffers must be within the buffer's size.
-- | The type system ensures offsets don't exceed the maximum buffer size.
newtype BufferOffset = BufferOffset Int

derive instance eqBufferOffset :: Eq BufferOffset
derive instance ordBufferOffset :: Ord BufferOffset

instance showBufferOffset :: Show BufferOffset where
  show (BufferOffset n) = "BufferOffset(" <> show n <> ")"

-- | Bounds specification for buffer offset.
bufferOffsetBounds :: IntBounds
bufferOffsetBounds = intBounds 0 268435456 Clamps "bufferOffset" "Buffer offset (0-256MB)"

-- | Smart constructor with validation.
bufferOffset :: Int -> Maybe BufferOffset
bufferOffset n
  | n >= 0 && n <= 268435456 = Just (BufferOffset n)
  | otherwise = Nothing

-- | Clamping constructor.
clampBufferOffset :: Int -> BufferOffset
clampBufferOffset n = BufferOffset (clampInt 0 268435456 n)

-- | Extract the underlying Int value.
unwrapBufferOffset :: BufferOffset -> Int
unwrapBufferOffset (BufferOffset n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // uniform buffer binding size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Uniform buffer binding size.
-- |
-- | Bounds: 0 to 65536 (64 KB, WebGPU guaranteed minimum)
-- |
-- | Uniform buffers are optimized for small, frequently-updated data:
-- | - Transformation matrices
-- | - Material properties
-- | - Lighting parameters
-- |
-- | The 64 KB limit ensures uniform buffers fit in fast GPU memory.
newtype UniformBufferBindingSize = UniformBufferBindingSize Int

derive instance eqUniformBufferBindingSize :: Eq UniformBufferBindingSize
derive instance ordUniformBufferBindingSize :: Ord UniformBufferBindingSize

instance showUniformBufferBindingSize :: Show UniformBufferBindingSize where
  show (UniformBufferBindingSize n) = "UniformBindingSize(" <> show n <> ")"

-- | Bounds specification for uniform buffer binding size.
uniformBufferBindingSizeBounds :: IntBounds
uniformBufferBindingSizeBounds = intBounds 0 65536 Clamps "uniformBufferBindingSize" "Uniform buffer binding size (0-64KB)"

-- | Smart constructor with validation.
uniformBufferBindingSize :: Int -> Maybe UniformBufferBindingSize
uniformBufferBindingSize n
  | n >= 0 && n <= 65536 = Just (UniformBufferBindingSize n)
  | otherwise = Nothing

-- | Clamping constructor.
clampUniformBufferBindingSize :: Int -> UniformBufferBindingSize
clampUniformBufferBindingSize n = UniformBufferBindingSize (clampInt 0 65536 n)

-- | Extract the underlying Int value.
unwrapUniformBufferBindingSize :: UniformBufferBindingSize -> Int
unwrapUniformBufferBindingSize (UniformBufferBindingSize n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // storage buffer binding size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Storage buffer binding size.
-- |
-- | Bounds: 0 to 134217728 (128 MB, WebGPU guaranteed minimum)
-- |
-- | Storage buffers are for larger, shader-readable/writable data:
-- | - Compute shader input/output
-- | - Large arrays of structs
-- | - GPU-driven rendering data
-- |
-- | Storage buffers can be larger than uniform buffers but may have
-- | different performance characteristics.
newtype StorageBufferBindingSize = StorageBufferBindingSize Int

derive instance eqStorageBufferBindingSize :: Eq StorageBufferBindingSize
derive instance ordStorageBufferBindingSize :: Ord StorageBufferBindingSize

instance showStorageBufferBindingSize :: Show StorageBufferBindingSize where
  show (StorageBufferBindingSize n) = "StorageBindingSize(" <> show n <> ")"

-- | Bounds specification for storage buffer binding size.
storageBufferBindingSizeBounds :: IntBounds
storageBufferBindingSizeBounds = intBounds 0 134217728 Clamps "storageBufferBindingSize" "Storage buffer binding size (0-128MB)"

-- | Smart constructor with validation.
storageBufferBindingSize :: Int -> Maybe StorageBufferBindingSize
storageBufferBindingSize n
  | n >= 0 && n <= 134217728 = Just (StorageBufferBindingSize n)
  | otherwise = Nothing

-- | Clamping constructor.
clampStorageBufferBindingSize :: Int -> StorageBufferBindingSize
clampStorageBufferBindingSize n = StorageBufferBindingSize (clampInt 0 134217728 n)

-- | Extract the underlying Int value.
unwrapStorageBufferBindingSize :: StorageBufferBindingSize -> Int
unwrapStorageBufferBindingSize (StorageBufferBindingSize n) = n
