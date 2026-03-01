-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // resource // texture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Texture Pool — GPU Texture Pooling by Format and Size
-- |
-- | ## Purpose
-- |
-- | GPU texture allocation is expensive. This module provides:
-- |
-- | - **Format×Size pooling**: Reuse textures by exact match
-- | - **Mipmap handling**: Support for mip chains
-- | - **Memory statistics**: Track allocation patterns
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Textures are reused across viewport regions:
-- | - Agents rendering similar content share texture pools
-- | - Render targets are recycled between frames
-- | - Mipmap chains are preserved for reuse

module Hydrogen.GPU.Resource.Texture
  ( -- * Texture Dimensions
    TextureDimension
      ( Dim2D
      , Dim3D
      , DimCube
      )
  
  -- * Texture Specification
  , TextureSpec
  , TexturePoolKey
  , mkTextureSpec
  
  -- * Texture Handle
  , TextureHandle
      ( TextureHandle )
  
  -- * Texture Pool
  , TexturePool
      ( TexturePool )
  , mkTexturePool
  , defaultTexturePool
  , textureAcquire
  , textureRelease
  
  -- * Pool Statistics
  , texturePoolStats
  
  -- * Memory Estimation
  , estimateTextureMemory
  , texturePoolMemoryUsed
  
  -- * Pool Queries
  , mapFreeTextures
  , largeTextures
  , texturePoolUnderThreshold
  , findSmallestFittingTexture
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (&&)
  , (/=)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set as Set

import Hydrogen.GPU.WebGPU.Types (GPUTextureFormat, GPUTextureUsage)
import Hydrogen.GPU.Resource.Handle 
  ( ResourceHandle
  , ResourceId
  , handleId
  , mkResourceHandle
  )
import Hydrogen.GPU.Resource.Buffer (PoolStats)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // texture dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture dimension type.
data TextureDimension
  = Dim2D
  | Dim3D
  | DimCube

derive instance eqTextureDimension :: Eq TextureDimension
derive instance ordTextureDimension :: Ord TextureDimension

instance showTextureDimension :: Show TextureDimension where
  show Dim2D = "2D"
  show Dim3D = "3D"
  show DimCube = "Cube"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // texture specification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture specification for allocation.
type TextureSpec =
  { width :: Int
  , height :: Int
  , depth :: Int
  , format :: GPUTextureFormat
  , usage :: Array GPUTextureUsage
  , mipLevels :: Int
  , dimension :: TextureDimension
  , label :: String
  }

-- | Texture pool key (format + size + usage).
type TexturePoolKey =
  { width :: Int
  , height :: Int
  , depth :: Int
  , format :: GPUTextureFormat
  , mipLevels :: Int
  }

-- | Create a texture specification.
mkTextureSpec 
  :: Int 
  -> Int 
  -> GPUTextureFormat 
  -> Array GPUTextureUsage 
  -> String 
  -> TextureSpec
mkTextureSpec width height format usage label =
  { width
  , height
  , depth: 1
  , format
  , usage
  , mipLevels: 1
  , dimension: Dim2D
  , label
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // texture handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a pooled texture.
newtype TextureHandle = TextureHandle
  { handle :: ResourceHandle
  , spec :: TextureSpec
  }

derive instance eqTextureHandle :: Eq TextureHandle

instance showTextureHandle :: Show TextureHandle where
  show (TextureHandle h) = 
    "(TextureHandle " <> show h.spec.width <> "x" <> show h.spec.height <> ")"

-- | Extract resource handle from texture handle.
unwrapTextureHandle :: TextureHandle -> ResourceHandle
unwrapTextureHandle (TextureHandle h) = h.handle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // texture pool
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture pool for efficient reuse.
newtype TexturePool = TexturePool
  { freeTextures :: Array TextureHandle
  , acquired :: Set.Set ResourceId
  , totalAllocated :: Int
  , totalAcquired :: Int
  , totalReleased :: Int
  }

derive instance eqTexturePool :: Eq TexturePool

instance showTexturePool :: Show TexturePool where
  show (TexturePool p) = 
    "(TexturePool allocated:" <> show p.totalAllocated <> 
    " acquired:" <> show (Set.size p.acquired) <> ")"

-- | Create a new texture pool.
mkTexturePool :: TexturePool
mkTexturePool = TexturePool
  { freeTextures: []
  , acquired: Set.empty
  , totalAllocated: 0
  , totalAcquired: 0
  , totalReleased: 0
  }

-- | Default texture pool.
defaultTexturePool :: TexturePool
defaultTexturePool = mkTexturePool

-- | Acquire a texture from the pool.
textureAcquire :: TextureSpec -> TexturePool -> { handle :: TextureHandle, pool :: TexturePool }
textureAcquire spec (TexturePool p) =
  let matchingTexture = Array.find (textureMatches spec) p.freeTextures
  in case matchingTexture of
       Just existingHandle ->
         -- Reuse existing texture
         let newFreeTextures = Array.filter 
               (\h -> h /= existingHandle) p.freeTextures
             newAcquired = Set.insert 
               (handleId (unwrapTextureHandle existingHandle)) p.acquired
         in
           { handle: existingHandle
           , pool: TexturePool (p 
               { freeTextures = newFreeTextures
               , acquired = newAcquired
               , totalAcquired = p.totalAcquired + 1
               })
           }
       Nothing ->
         -- Allocate new texture
         let contentKey = spec.label <> "-" <> show spec.width <> "x" <> 
                         show spec.height <> "-" <> show p.totalAllocated
             newHandle = TextureHandle
               { handle: mkResourceHandle contentKey
               , spec
               }
             newAcquired = Set.insert 
               (handleId (unwrapTextureHandle newHandle)) p.acquired
         in
           { handle: newHandle
           , pool: TexturePool (p 
               { acquired = newAcquired
               , totalAllocated = p.totalAllocated + 1
               , totalAcquired = p.totalAcquired + 1
               })
           }

-- | Check if texture matches specification.
textureMatches :: TextureSpec -> TextureHandle -> Boolean
textureMatches spec (TextureHandle h) =
  h.spec.width == spec.width &&
  h.spec.height == spec.height &&
  h.spec.depth == spec.depth &&
  h.spec.format == spec.format &&
  h.spec.mipLevels >= spec.mipLevels

-- | Release a texture back to the pool.
textureRelease :: TextureHandle -> TexturePool -> TexturePool
textureRelease texHandle@(TextureHandle h) (TexturePool p) =
  let resourceId = handleId h.handle
      newAcquired = Set.delete resourceId p.acquired
      newFreeTextures = Array.cons texHandle p.freeTextures
  in
    TexturePool (p 
      { freeTextures = newFreeTextures
      , acquired = newAcquired
      , totalReleased = p.totalReleased + 1
      })

-- | Get texture pool statistics.
texturePoolStats :: TexturePool -> PoolStats
texturePoolStats (TexturePool p) =
  let freeCount = Array.length p.freeTextures
      acquiredCount = Set.size p.acquired
      totalReused = p.totalAcquired - p.totalAllocated
      reuseRate = if p.totalAcquired > 0
                  then Int.toNumber totalReused / Int.toNumber p.totalAcquired
                  else 0.0
  in
    { freeCount
    , acquiredCount
    , totalAllocated: p.totalAllocated
    , reuseRate
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // memory estimation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimate memory usage of a texture specification in bytes.
-- |
-- | Calculation: width × height × depth × bytesPerPixel × mipFactor
-- | where mipFactor ≈ 1.33 for full mip chain (1 + 1/4 + 1/16 + ...)
estimateTextureMemory :: TextureSpec -> Int
estimateTextureMemory spec =
  let baseSize = spec.width * spec.height * spec.depth * bytesPerPixel spec.format
      -- Mip chain adds ~33% for full chain
      mipFactor :: Number
      mipFactor = if spec.mipLevels > 1 then 4.0 / 3.0 else 1.0
      -- Convert to Int (floor)
      mipMultiplied = Int.toNumber baseSize * mipFactor
  in
    Int.floor mipMultiplied
  where
    -- Approximate bytes per pixel for common formats
    bytesPerPixel :: GPUTextureFormat -> Int
    bytesPerPixel _ = 4  -- Default to RGBA8 (4 bytes)
                         -- Full implementation would pattern match on format

-- | Total estimated memory for all acquired textures.
texturePoolMemoryUsed :: TexturePool -> Int
texturePoolMemoryUsed (TexturePool p) =
  foldl (\acc (TextureHandle h) -> acc + estimateTextureMemory h.spec) 0 p.freeTextures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pool queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over all free texture handles.
mapFreeTextures :: (TextureHandle -> TextureHandle) -> TexturePool -> TexturePool
mapFreeTextures f (TexturePool p) =
  let newFreeTextures = map f p.freeTextures
  in TexturePool (p { freeTextures = newFreeTextures })

-- | Get textures larger than dimensions.
largeTextures :: Int -> Int -> TexturePool -> Array TextureHandle
largeTextures minWidth minHeight (TexturePool p) =
  Array.filter (\(TextureHandle h) -> 
    h.spec.width > minWidth && h.spec.height > minHeight) p.freeTextures

-- | Check if texture pool is below a memory threshold.
texturePoolUnderThreshold :: Int -> TexturePool -> Boolean
texturePoolUnderThreshold thresholdBytes pool =
  texturePoolMemoryUsed pool < thresholdBytes

-- | Find smallest texture that fits the requested dimensions.
findSmallestFittingTexture :: Int -> Int -> TexturePool -> Maybe TextureHandle
findSmallestFittingTexture width height (TexturePool p) =
  let fitting = Array.filter (\(TextureHandle h) -> 
                  h.spec.width >= width && h.spec.height >= height) p.freeTextures
      sorted = Array.sortBy (\(TextureHandle a) (TextureHandle b) ->
                 compare (a.spec.width * a.spec.height) (b.spec.width * b.spec.height)) fitting
  in Array.head sorted
