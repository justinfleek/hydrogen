-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // gpu // resource
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Resource Management — Caching, Pooling, and Lifecycle
-- |
-- | ## Purpose
-- |
-- | This module provides the resource management layer between pure kernel
-- | descriptions and actual WebGPU execution. It handles:
-- |
-- | - **Pipeline caching**: Compiled shaders are expensive; cache by content hash
-- | - **Buffer pooling**: Reuse buffers across frames to avoid allocation
-- | - **Texture pooling**: Reuse textures by format/size
-- | - **Resource lifecycle**: Track generation for cache invalidation
-- |
-- | ## Architecture
-- |
-- | ```
-- | ComputeKernel (pure data)
-- |       ↓
-- | Resource.purs (this module)
-- |       ↓ manages
-- | ┌─────────────────────────────────────┐
-- | │ PipelineCache                       │
-- | │   - UUID5-keyed compiled pipelines  │
-- | │   - LRU eviction                    │
-- | ├─────────────────────────────────────┤
-- | │ BufferPool                          │
-- | │   - Size-bucketed buffer pools      │
-- | │   - Free list management            │
-- | ├─────────────────────────────────────┤
-- | │ TexturePool                         │
-- | │   - Format×Size×Usage keyed         │
-- | │   - Mipmap chain handling           │
-- | └─────────────────────────────────────┘
-- |       ↓
-- | Interpreter.purs (executes against WebGPU)
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Hydrogen.GPU.Resource.Handle` — Resource identity and handles
-- | - `Hydrogen.GPU.Resource.Pipeline` — Pipeline caching with LRU
-- | - `Hydrogen.GPU.Resource.Buffer` — Buffer pooling by size bucket
-- | - `Hydrogen.GPU.Resource.Texture` — Texture pooling by format/size
-- | - `Hydrogen.GPU.Resource.Registry` — Central resource management
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Resource identity is content-addressed:
-- | - Same kernel definition → same pipeline UUID5
-- | - Multiple agents can share compiled pipelines
-- | - Buffer pools reduce per-frame allocation to near-zero
-- | - Textures are reused across viewport regions
-- |
-- | ## Council Decision (2026-02-25)
-- |
-- | This module implements P2 from the Council Review:
-- | "TextureDescriptor, BufferDescriptor, PipelineCache"

module Hydrogen.GPU.Resource
  ( -- * Resource Handles (from Handle)
    module Hydrogen.GPU.Resource.Handle
  
  -- * Pipeline Cache (from Pipeline)
  , module Hydrogen.GPU.Resource.Pipeline
  
  -- * Buffer Pool (from Buffer)
  , module Hydrogen.GPU.Resource.Buffer
  
  -- * Texture Pool (from Texture)
  , module Hydrogen.GPU.Resource.Texture
  
  -- * Resource Registry (from Registry)
  , module Hydrogen.GPU.Resource.Registry
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Re-export all submodules
import Hydrogen.GPU.Resource.Handle 
  ( ResourceId
      ( ResourceId )
  , mkResourceId
  , resourceIdToString
  , ResourceHandle
      ( ResourceHandle )
  , handleId
  , handleGeneration
  , mkResourceHandle
  , incrementGeneration
  )

import Hydrogen.GPU.Resource.Pipeline 
  ( PipelineKey
      ( PipelineKey )
  , mkPipelineKey
  , PipelineEntry
  , PipelineCache
      ( PipelineCache )
  , mkPipelineCache
  , defaultPipelineCache
  , pipelineLookup
  , pipelineInsert
  , pipelineEvictLRU
  , pipelineCacheSize
  , CacheStats
  , pipelineCacheStats
  , pipelineKeys
  , recentPipelines
  , expensivePipelines
  , pipelineHasCapacity
  )

import Hydrogen.GPU.Resource.Buffer 
  ( BufferBucket
      ( Bucket1KB
      , Bucket4KB
      , Bucket16KB
      , Bucket64KB
      , Bucket256KB
      , Bucket1MB
      , Bucket4MB
      , Bucket16MB
      , BucketCustom
      )
  , bucketSize
  , bucketForSize
  , BufferSpec
  , mkBufferSpec
  , BufferHandle
      ( BufferHandle )
  , BufferPool
      ( BufferPool )
  , mkBufferPool
  , defaultBufferPool
  , bufferAcquire
  , bufferRelease
  , PoolStats
  , bufferPoolStats
  , estimateBufferMemory
  , bufferPoolMemoryUsed
  , mapFreeBuffers
  , allFreeBuffers
  , bufferCountByBucket
  , largeBuffers
  , bufferPoolUnderThreshold
  , findSmallestFittingBuffer
  )

import Hydrogen.GPU.Resource.Texture 
  ( TextureDimension
      ( Dim2D
      , Dim3D
      , DimCube
      )
  , TextureSpec
  , TexturePoolKey
  , mkTextureSpec
  , TextureHandle
      ( TextureHandle )
  , TexturePool
      ( TexturePool )
  , mkTexturePool
  , defaultTexturePool
  , textureAcquire
  , textureRelease
  , texturePoolStats
  , estimateTextureMemory
  , texturePoolMemoryUsed
  , mapFreeTextures
  , largeTextures
  , texturePoolUnderThreshold
  , findSmallestFittingTexture
  )

import Hydrogen.GPU.Resource.Registry 
  ( ResourceRegistry
      ( ResourceRegistry )
  , mkResourceRegistry
  , defaultResourceRegistry
  , registryPipelines
  , registryBuffers
  , registryTextures
  , registryFrame
  , withPipelines
  , withBuffers
  , withTextures
  , advanceFrame
  , collectGarbage
  , registryMemoryEstimate
  , RegistryStats
  , registryStats
  , registryUnderBudget
  )
