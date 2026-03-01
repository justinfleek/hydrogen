-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // resource // registry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Resource Registry — Central Management for GPU Resources
-- |
-- | ## Purpose
-- |
-- | The registry is the single source of truth for all GPU resources:
-- |
-- | - **Unified access**: Single point for pipelines, buffers, textures
-- | - **Frame tracking**: Enables LRU eviction and garbage collection
-- | - **Memory budgeting**: Monitor and limit total resource usage
-- |
-- | ## Lifecycle Management
-- |
-- | - Tracks frame number for LRU eviction
-- | - Garbage collection removes unused resources
-- | - Single source of truth for resource state
-- |
-- | ## At Billion-Agent Scale
-- |
-- | The registry enables efficient resource sharing:
-- | - Agents query the registry before allocation
-- | - Frame-based tracking enables predictable eviction
-- | - Memory budgets prevent runaway allocation

module Hydrogen.GPU.Resource.Registry
  ( -- * Resource Registry
    ResourceRegistry
      ( ResourceRegistry )
  , mkResourceRegistry
  , defaultResourceRegistry
  
  -- * Registry Accessors
  , registryPipelines
  , registryBuffers
  , registryTextures
  , registryFrame
  
  -- * Registry Updates
  , withPipelines
  , withBuffers
  , withTextures
  
  -- * Frame Management
  , advanceFrame
  , collectGarbage
  
  -- * Memory Estimation
  , registryMemoryEstimate
  
  -- * Registry Statistics
  , RegistryStats
  , registryStats
  
  -- * Capacity Management
  , registryUnderBudget
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (<)
  , (>=)
  , (<>)
  )

import Data.Map as Map

import Hydrogen.GPU.Resource.Pipeline 
  ( PipelineCache
      ( PipelineCache )
  , CacheStats
  , defaultPipelineCache
  , pipelineCacheStats
  )
import Hydrogen.GPU.Resource.Buffer 
  ( BufferPool
  , PoolStats
  , defaultBufferPool
  , bufferPoolStats
  , bufferPoolMemoryUsed
  )
import Hydrogen.GPU.Resource.Texture 
  ( TexturePool
  , defaultTexturePool
  , texturePoolStats
  , texturePoolMemoryUsed
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // resource registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Central registry for all GPU resources.
-- |
-- | ## Lifecycle Management
-- |
-- | - Tracks frame number for LRU eviction
-- | - Garbage collection removes unused resources
-- | - Single source of truth for resource state
newtype ResourceRegistry = ResourceRegistry
  { pipelines :: PipelineCache
  , buffers :: BufferPool
  , textures :: TexturePool
  , currentFrame :: Int
  , gcThreshold :: Int        -- Frames before GC eligible
  }

derive instance eqResourceRegistry :: Eq ResourceRegistry

instance showResourceRegistry :: Show ResourceRegistry where
  show (ResourceRegistry r) = 
    "(ResourceRegistry frame:" <> show r.currentFrame <> ")"

-- | Create a new resource registry.
mkResourceRegistry :: ResourceRegistry
mkResourceRegistry = ResourceRegistry
  { pipelines: defaultPipelineCache
  , buffers: defaultBufferPool
  , textures: defaultTexturePool
  , currentFrame: 0
  , gcThreshold: 60           -- 60 frames (~1 second at 60fps)
  }

-- | Default resource registry.
defaultResourceRegistry :: ResourceRegistry
defaultResourceRegistry = mkResourceRegistry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // registry accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pipeline cache from registry.
registryPipelines :: ResourceRegistry -> PipelineCache
registryPipelines (ResourceRegistry r) = r.pipelines

-- | Get buffer pool from registry.
registryBuffers :: ResourceRegistry -> BufferPool
registryBuffers (ResourceRegistry r) = r.buffers

-- | Get texture pool from registry.
registryTextures :: ResourceRegistry -> TexturePool
registryTextures (ResourceRegistry r) = r.textures

-- | Get current frame number.
registryFrame :: ResourceRegistry -> Int
registryFrame (ResourceRegistry r) = r.currentFrame

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // registry updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update pipelines in registry.
withPipelines :: (PipelineCache -> PipelineCache) -> ResourceRegistry -> ResourceRegistry
withPipelines f (ResourceRegistry r) =
  ResourceRegistry (r { pipelines = f r.pipelines })

-- | Update buffers in registry.
withBuffers :: (BufferPool -> BufferPool) -> ResourceRegistry -> ResourceRegistry
withBuffers f (ResourceRegistry r) =
  ResourceRegistry (r { buffers = f r.buffers })

-- | Update textures in registry.
withTextures :: (TexturePool -> TexturePool) -> ResourceRegistry -> ResourceRegistry
withTextures f (ResourceRegistry r) =
  ResourceRegistry (r { textures = f r.textures })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // frame management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Advance to next frame.
advanceFrame :: ResourceRegistry -> ResourceRegistry
advanceFrame (ResourceRegistry r) =
  let (PipelineCache pc) = r.pipelines
      newPipelines = PipelineCache (pc { currentFrame = r.currentFrame + 1 })
  in
    ResourceRegistry (r 
      { currentFrame = r.currentFrame + 1
      , pipelines = newPipelines
      })

-- | Run garbage collection on stale resources.
-- |
-- | Evicts pipelines not used within gcThreshold frames.
collectGarbage :: ResourceRegistry -> ResourceRegistry
collectGarbage (ResourceRegistry r) =
  let (PipelineCache pc) = r.pipelines
      threshold = r.currentFrame - r.gcThreshold
      -- Filter out stale pipelines
      freshEntries = Map.filter 
        (\entry -> entry.lastUsedFrame >= threshold) pc.entries
      newPipelines = PipelineCache (pc { entries = freshEntries })
  in
    ResourceRegistry (r { pipelines = newPipelines })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // memory estimation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Total memory estimate across all resource types.
registryMemoryEstimate :: ResourceRegistry -> Int
registryMemoryEstimate (ResourceRegistry r) =
  bufferPoolMemoryUsed r.buffers + texturePoolMemoryUsed r.textures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // registry statistics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined statistics for all resource pools.
type RegistryStats =
  { pipelineStats :: CacheStats
  , bufferStats :: PoolStats
  , textureStats :: PoolStats
  , totalMemoryBytes :: Int
  , currentFrame :: Int
  }

-- | Get combined registry statistics.
registryStats :: ResourceRegistry -> RegistryStats
registryStats reg@(ResourceRegistry r) =
  { pipelineStats: pipelineCacheStats r.pipelines
  , bufferStats: bufferPoolStats r.buffers
  , textureStats: texturePoolStats r.textures
  , totalMemoryBytes: registryMemoryEstimate reg
  , currentFrame: r.currentFrame
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // capacity management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if registry total memory is under budget.
registryUnderBudget :: Int -> ResourceRegistry -> Boolean
registryUnderBudget budgetBytes reg =
  registryMemoryEstimate reg < budgetBytes
