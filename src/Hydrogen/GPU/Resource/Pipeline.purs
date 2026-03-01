-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // resource // pipeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pipeline Cache — Compiled Shader Caching with LRU Eviction
-- |
-- | ## Purpose
-- |
-- | Compiled shaders are expensive to create. This module provides:
-- |
-- | - **Content-addressed caching**: Same kernel → same pipeline
-- | - **LRU eviction**: Removes least-recently-used when at capacity
-- | - **Hit/miss statistics**: Monitor cache effectiveness
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Multiple agents creating identical compute kernels will:
-- | - Share the same compiled pipeline (by UUID5 content hash)
-- | - Avoid redundant compilation
-- | - Benefit from warm caches across agent boundaries

module Hydrogen.GPU.Resource.Pipeline
  ( -- * Pipeline Key
    PipelineKey
      ( PipelineKey )
  , mkPipelineKey
  
  -- * Pipeline Entry
  , PipelineEntry
  
  -- * Pipeline Cache
  , PipelineCache
      ( PipelineCache )
  , mkPipelineCache
  , defaultPipelineCache
  , pipelineLookup
  , pipelineInsert
  , pipelineEvictLRU
  , pipelineCacheSize
  
  -- * Cache Statistics
  , CacheStats
  , pipelineCacheStats
  
  -- * Cache Queries
  , pipelineKeys
  , recentPipelines
  , expensivePipelines
  , pipelineHasCapacity
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
  , ($)
  , (+)
  , (-)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<>)
  )

import Data.Array as Array
import Data.Int as Int
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.GPU.Resource.Handle (ResourceHandle)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pipeline key
-- ═════════════════════════════════════════════════════════════════════════════

-- | Key for pipeline lookup.
-- |
-- | Derived from kernel specification content hash.
newtype PipelineKey = PipelineKey String

derive instance eqPipelineKey :: Eq PipelineKey
derive instance ordPipelineKey :: Ord PipelineKey

instance showPipelineKey :: Show PipelineKey where
  show (PipelineKey s) = "(PipelineKey " <> s <> ")"

-- | Create pipeline key from content description.
mkPipelineKey :: String -> PipelineKey
mkPipelineKey = PipelineKey

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pipeline entry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cached pipeline entry.
-- |
-- | ## Fields
-- |
-- | - `handle`: Resource handle for this pipeline
-- | - `lastUsedFrame`: Frame number when last accessed (for LRU)
-- | - `compilationTime`: How long compilation took (for metrics)
-- | - `shaderSource`: WGSL source (for debugging/recompilation)
type PipelineEntry =
  { handle :: ResourceHandle
  , lastUsedFrame :: Int
  , compilationTime :: Number    -- milliseconds
  , shaderSource :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // pipeline cache
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pipeline cache with LRU eviction.
-- |
-- | ## Capacity Management
-- |
-- | - `maxEntries`: Hard limit on cached pipelines
-- | - Eviction uses LRU (least recently used frame)
-- | - Evicted pipelines can be recompiled on next use
newtype PipelineCache = PipelineCache
  { entries :: Map.Map PipelineKey PipelineEntry
  , maxEntries :: Int
  , currentFrame :: Int
  , hits :: Int
  , misses :: Int
  }

derive instance eqPipelineCache :: Eq PipelineCache

instance showPipelineCache :: Show PipelineCache where
  show (PipelineCache c) = 
    "(PipelineCache entries:" <> show (Map.size c.entries) <> 
    "/" <> show c.maxEntries <> ")"

-- | Create a new pipeline cache.
mkPipelineCache :: Int -> PipelineCache
mkPipelineCache maxEntries = PipelineCache
  { entries: Map.empty
  , maxEntries
  , currentFrame: 0
  , hits: 0
  , misses: 0
  }

-- | Default pipeline cache (256 entries).
defaultPipelineCache :: PipelineCache
defaultPipelineCache = mkPipelineCache 256

-- | Look up a pipeline in the cache.
-- |
-- | Returns the entry and an updated cache (with LRU timestamp).
pipelineLookup :: PipelineKey -> PipelineCache -> { entry :: Maybe PipelineEntry, cache :: PipelineCache }
pipelineLookup key (PipelineCache c) =
  case Map.lookup key c.entries of
    Nothing -> 
      { entry: Nothing
      , cache: PipelineCache (c { misses = c.misses + 1 })
      }
    Just entry ->
      let updatedEntry = entry { lastUsedFrame = c.currentFrame }
          updatedEntries = Map.insert key updatedEntry c.entries
      in
        { entry: Just updatedEntry
        , cache: PipelineCache (c { entries = updatedEntries, hits = c.hits + 1 })
        }

-- | Insert a pipeline into the cache.
-- |
-- | If at capacity, evicts LRU entry first.
pipelineInsert :: PipelineKey -> PipelineEntry -> PipelineCache -> PipelineCache
pipelineInsert key entry cache@(PipelineCache c) =
  let 
    -- Evict if at capacity
    cache' = if Map.size c.entries >= c.maxEntries
             then pipelineEvictLRU cache
             else cache
    (PipelineCache c') = cache'
    updatedEntry = entry { lastUsedFrame = c'.currentFrame }
  in
    PipelineCache (c' { entries = Map.insert key updatedEntry c'.entries })

-- | Evict the least recently used pipeline.
pipelineEvictLRU :: PipelineCache -> PipelineCache
pipelineEvictLRU (PipelineCache c) =
  case findLRU c.entries of
    Nothing -> PipelineCache c
    Just lruKey -> 
      PipelineCache (c { entries = Map.delete lruKey c.entries })
  where
    findLRU :: Map.Map PipelineKey PipelineEntry -> Maybe PipelineKey
    findLRU entries =
      let pairs = Map.toUnfoldable entries :: Array (Tuple PipelineKey PipelineEntry)
          sorted = Array.sortBy (\(Tuple _ a) (Tuple _ b) -> 
                     compare a.lastUsedFrame b.lastUsedFrame) pairs
      in case Array.head sorted of
           Nothing -> Nothing
           Just (Tuple k _) -> Just k

-- | Get cache size.
pipelineCacheSize :: PipelineCache -> Int
pipelineCacheSize (PipelineCache c) = Map.size c.entries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // cache statistics
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cache statistics.
type CacheStats =
  { entries :: Int
  , maxEntries :: Int
  , hits :: Int
  , misses :: Int
  , hitRate :: Number
  }

-- | Get cache statistics.
pipelineCacheStats :: PipelineCache -> CacheStats
pipelineCacheStats (PipelineCache c) =
  let total = c.hits + c.misses
      hitRate = if total > 0 
                then Int.toNumber c.hits / Int.toNumber total
                else 0.0
  in
    { entries: Map.size c.entries
    , maxEntries: c.maxEntries
    , hits: c.hits
    , misses: c.misses
    , hitRate
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cache queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all pipeline keys in the cache.
pipelineKeys :: PipelineCache -> Array PipelineKey
pipelineKeys (PipelineCache c) =
  map (\(Tuple k _) -> k) $ Map.toUnfoldable c.entries

-- | Filter pipelines by last used frame.
-- |
-- | Returns pipelines used within the last N frames.
recentPipelines :: Int -> PipelineCache -> Array PipelineEntry
recentPipelines withinFrames (PipelineCache c) =
  let threshold = c.currentFrame - withinFrames
      allEntries = map (\(Tuple _ e) -> e) $ Map.toUnfoldable c.entries
  in Array.filter (\e -> e.lastUsedFrame >= threshold) allEntries

-- | Filter pipelines by compilation time.
-- |
-- | Returns pipelines that took longer than threshold to compile.
-- | Useful for identifying expensive shaders.
expensivePipelines :: Number -> PipelineCache -> Array PipelineEntry
expensivePipelines thresholdMs (PipelineCache c) =
  let allEntries = map (\(Tuple _ e) -> e) $ Map.toUnfoldable c.entries
  in Array.filter (\e -> e.compilationTime > thresholdMs) allEntries

-- | Check if pipeline cache has room for more entries.
pipelineHasCapacity :: PipelineCache -> Boolean
pipelineHasCapacity (PipelineCache c) =
  Map.size c.entries < c.maxEntries
