-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // gpu // limits // vertex
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vertex Limits — Bounded types for WebGPU vertex buffer constraints.
-- |
-- | ## Vertex Pipeline
-- |
-- | WebGPU's vertex pipeline processes vertex data through:
-- | 1. Vertex buffers (raw data)
-- | 2. Vertex attributes (how to interpret the data)
-- | 3. Vertex shader (processing)
-- |
-- | ## Limits
-- |
-- | - maxVertexBuffers: 8 (guaranteed minimum)
-- | - maxVertexAttributes: 16 (guaranteed minimum)
-- | - maxVertexBufferArrayStride: 2048 (guaranteed minimum)
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.GPU.Limits.Vertex
  ( -- * Vertex Buffer Count
    VertexBufferCount
  , vertexBufferCount
  , clampVertexBufferCount
  , unwrapVertexBufferCount
  , vertexBufferCountBounds
  
  -- * Vertex Attribute Count
  , VertexAttributeCount
  , vertexAttributeCount
  , clampVertexAttributeCount
  , unwrapVertexAttributeCount
  , vertexAttributeCountBounds
  
  -- * Vertex Buffer Stride
  , VertexBufferStride
  , vertexBufferStride
  , clampVertexBufferStride
  , unwrapVertexBufferStride
  , vertexBufferStrideBounds
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
--                                                          // vertex buffer count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertex buffer count.
-- |
-- | Bounds: 0 to 8 (WebGPU guaranteed minimum)
-- |
-- | Multiple vertex buffers allow separating vertex attributes:
-- | - Buffer 0: Positions (vec3)
-- | - Buffer 1: Normals (vec3)
-- | - Buffer 2: UVs (vec2)
-- | - Buffer 3: Tangents (vec4)
-- |
-- | This organization allows updating individual attributes without
-- | re-uploading all vertex data.
newtype VertexBufferCount = VertexBufferCount Int

derive instance eqVertexBufferCount :: Eq VertexBufferCount
derive instance ordVertexBufferCount :: Ord VertexBufferCount

instance showVertexBufferCount :: Show VertexBufferCount where
  show (VertexBufferCount n) = "VertexBuffers(" <> show n <> ")"

-- | Bounds specification for vertex buffer count.
vertexBufferCountBounds :: IntBounds
vertexBufferCountBounds = intBounds 0 8 Clamps "vertexBufferCount" "Vertex buffer count (0-8)"

-- | Smart constructor with validation.
vertexBufferCount :: Int -> Maybe VertexBufferCount
vertexBufferCount n
  | n >= 0 && n <= 8 = Just (VertexBufferCount n)
  | otherwise = Nothing

-- | Clamping constructor.
clampVertexBufferCount :: Int -> VertexBufferCount
clampVertexBufferCount n = VertexBufferCount (clampInt 0 8 n)

-- | Extract the underlying Int value.
unwrapVertexBufferCount :: VertexBufferCount -> Int
unwrapVertexBufferCount (VertexBufferCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // vertex attribute count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertex attribute count.
-- |
-- | Bounds: 0 to 16 (WebGPU guaranteed minimum)
-- |
-- | Vertex attributes define how to interpret vertex buffer data:
-- | - Position (3 floats)
-- | - Normal (3 floats)
-- | - Tangent (4 floats)
-- | - UV0 (2 floats)
-- | - UV1 (2 floats)
-- | - Color (4 floats)
-- | - Bone indices (4 ints)
-- | - Bone weights (4 floats)
-- |
-- | 16 attributes is sufficient for most rendering techniques.
newtype VertexAttributeCount = VertexAttributeCount Int

derive instance eqVertexAttributeCount :: Eq VertexAttributeCount
derive instance ordVertexAttributeCount :: Ord VertexAttributeCount

instance showVertexAttributeCount :: Show VertexAttributeCount where
  show (VertexAttributeCount n) = "VertexAttribs(" <> show n <> ")"

-- | Bounds specification for vertex attribute count.
vertexAttributeCountBounds :: IntBounds
vertexAttributeCountBounds = intBounds 0 16 Clamps "vertexAttributeCount" "Vertex attribute count (0-16)"

-- | Smart constructor with validation.
vertexAttributeCount :: Int -> Maybe VertexAttributeCount
vertexAttributeCount n
  | n >= 0 && n <= 16 = Just (VertexAttributeCount n)
  | otherwise = Nothing

-- | Clamping constructor.
clampVertexAttributeCount :: Int -> VertexAttributeCount
clampVertexAttributeCount n = VertexAttributeCount (clampInt 0 16 n)

-- | Extract the underlying Int value.
unwrapVertexAttributeCount :: VertexAttributeCount -> Int
unwrapVertexAttributeCount (VertexAttributeCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // vertex buffer stride
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertex buffer stride.
-- |
-- | Bounds: 0 to 2048 (WebGPU guaranteed minimum)
-- |
-- | The stride is the byte distance between consecutive vertices in a buffer.
-- | For interleaved vertex data (position + normal + uv in one buffer):
-- |
-- | stride = sizeof(position) + sizeof(normal) + sizeof(uv)
-- |        = 12 + 12 + 8 = 32 bytes
-- |
-- | For non-interleaved (separate buffers), stride equals the attribute size.
newtype VertexBufferStride = VertexBufferStride Int

derive instance eqVertexBufferStride :: Eq VertexBufferStride
derive instance ordVertexBufferStride :: Ord VertexBufferStride

instance showVertexBufferStride :: Show VertexBufferStride where
  show (VertexBufferStride n) = "Stride(" <> show n <> ")"

-- | Bounds specification for vertex buffer stride.
vertexBufferStrideBounds :: IntBounds
vertexBufferStrideBounds = intBounds 0 2048 Clamps "vertexBufferStride" "Vertex buffer stride (0-2048)"

-- | Smart constructor with validation.
vertexBufferStride :: Int -> Maybe VertexBufferStride
vertexBufferStride n
  | n >= 0 && n <= 2048 = Just (VertexBufferStride n)
  | otherwise = Nothing

-- | Clamping constructor.
clampVertexBufferStride :: Int -> VertexBufferStride
clampVertexBufferStride n = VertexBufferStride (clampInt 0 2048 n)

-- | Extract the underlying Int value.
unwrapVertexBufferStride :: VertexBufferStride -> Int
unwrapVertexBufferStride (VertexBufferStride n) = n
