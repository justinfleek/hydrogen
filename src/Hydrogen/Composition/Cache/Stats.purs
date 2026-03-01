-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // cache // stats
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache Statistics — Hit/miss rates and performance metrics.
-- |
-- | Provides functions for calculating cache performance metrics:
-- | - Hit rate: Fraction of accesses that found data
-- | - Miss rate: Fraction of accesses that missed
-- | - Eviction rate: Evictions per access
-- | - Memory utilization: Current usage vs capacity

module Hydrogen.Composition.Cache.Stats
  ( -- * Rate Calculations
    hitRate
  , missRate
  , evictionRate
  
  -- * Memory Metrics
  , memoryUtilization
  
  -- * Debugging
  , showCacheStats
  
  -- * FFI
  , toNumberImpl
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , ($)
  , (+)
  , (/)
  , (==)
  , (<>)
  )

import Hydrogen.Composition.Cache.Types 
  ( CacheStats
  , CacheConfig
  , CompositionCache
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                          // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
-- |
-- | Foreign implementation for Int -> Number conversion.
foreign import toNumberImpl :: Int -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // rate calculations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate hit rate (0.0 to 1.0).
-- |
-- | Returns 0.0 if no accesses have occurred.
-- | A higher hit rate indicates better cache efficiency.
hitRate :: CacheStats -> Number
hitRate stats =
  let total = stats.hits + stats.misses
  in if total == 0 
     then 0.0 
     else toNumber stats.hits / toNumber total
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- | Calculate miss rate (0.0 to 1.0).
-- |
-- | Returns 0.0 if no accesses have occurred.
-- | Miss rate = 1 - hit rate.
missRate :: CacheStats -> Number
missRate stats =
  let total = stats.hits + stats.misses
  in if total == 0 
     then 0.0 
     else toNumber stats.misses / toNumber total
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- | Calculate eviction rate (evictions per access).
-- |
-- | Returns 0.0 if no accesses have occurred.
-- | A high eviction rate may indicate cache is undersized.
evictionRate :: CacheStats -> Number
evictionRate stats =
  let total = stats.hits + stats.misses
  in if total == 0 
     then 0.0 
     else toNumber stats.evictions / toNumber total
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // memory metrics
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate memory utilization ratio (0.0 to 1.0+).
-- |
-- | Compares current memory usage against total configured capacity
-- | across all tiers. Values > 1.0 indicate over-capacity.
memoryUtilization :: forall a. CompositionCache a -> Number
memoryUtilization cache =
  let maxBytes = cache.config.l0.maxSizeBytes 
               + cache.config.l1.maxSizeBytes 
               + cache.config.l2.maxSizeBytes
      currentBytes = cache.stats.totalSizeBytes
  in toNumber currentBytes / toNumber maxBytes
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // debugging
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show cache statistics for debugging.
-- |
-- | Produces a human-readable summary of cache state.
showCacheStats :: CacheStats -> String
showCacheStats stats =
  "CacheStats { entries: " <> show stats.entryCount
  <> ", size: " <> show stats.totalSizeBytes <> "b"
  <> ", hits: " <> show stats.hits
  <> ", misses: " <> show stats.misses
  <> ", evictions: " <> show stats.evictions
  <> ", L0: " <> show stats.l0Count
  <> ", L1: " <> show stats.l1Count
  <> ", L2: " <> show stats.l2Count <> " }"
