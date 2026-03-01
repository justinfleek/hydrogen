-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // cache // query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache Query Operations — Read-only queries and filtering.
-- |
-- | This module provides query operations that don't modify cache state
-- | (except for pruning expired entries):
-- | - cacheContains: Check if key exists
-- | - cacheSize/cacheSizeBytes: Size metrics
-- | - cacheGetByTier: Filter by tier
-- | - cachePruneExpired: Remove expired entries
-- | - cacheGetTop: Get most recently accessed entries

module Hydrogen.Composition.Cache.Query
  ( -- * Existence Checks
    cacheContains
    
  -- * Size Metrics
  , cacheSize
  , cacheSizeBytes
  , cacheLength
  
  -- * Filtering
  , cacheGetByTier
  , cacheGetTop
  , filterEntries
  
  -- * Maintenance
  , cachePruneExpired
  , cacheNeedsEviction
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (||)
  , otherwise
  , Ordering(LT, GT, EQ)
  )

import Data.Array (filter, length, sortBy, take) as Array
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.Map as Map
import Data.Tuple (Tuple, fst, snd)
import Data.Foldable (foldl)

import Hydrogen.Composition.Cache.Types 
  ( CacheTier(TierL0, TierL1, TierL2)
  , CacheEntry
  , CacheStats
  , CacheConfig
  , TierConfig
  , CompositionCache
  )

import Hydrogen.Composition.Cache.Operations (cacheInvalidate)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // existence checks
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a key exists in the cache (without updating LRU).
-- |
-- | This is a fast O(log n) check that doesn't modify cache state.
-- | Does NOT check expiration - use cacheGet for expiration-aware access.
cacheContains :: forall a. String -> CompositionCache a -> Boolean
cacheContains key cache = isJust $ Map.lookup key cache.entries

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // size metrics
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the number of entries in the cache.
-- |
-- | O(1) operation using cached statistics.
cacheSize :: forall a. CompositionCache a -> Int
cacheSize cache = cache.stats.entryCount

-- | Get the total size in bytes.
-- |
-- | O(1) operation using cached statistics.
cacheSizeBytes :: forall a. CompositionCache a -> Int
cacheSizeBytes cache = cache.stats.totalSizeBytes

-- | Get the total number of entries (alias for direct map access).
-- |
-- | O(n) operation - counts entries directly from map.
-- | Use cacheSize for O(1) access via statistics.
cacheLength :: forall a. CompositionCache a -> Int
cacheLength cache = Array.length allEntries
  where
    allEntries :: Array (Tuple String (CacheEntry a))
    allEntries = Map.toUnfoldable cache.entries

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // filtering
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get entries filtered by tier.
-- |
-- | Returns all entries belonging to the specified tier.
cacheGetByTier :: forall a. CacheTier -> CompositionCache a -> Array (Tuple String (CacheEntry a))
cacheGetByTier tier cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
  in Array.filter (\entry -> (snd entry).metadata.tier == tier) allEntries

-- | Get top N most recently accessed entries.
-- |
-- | Returns entries sorted by lastAccessed descending, limited to n.
cacheGetTop :: forall a. Int -> CompositionCache a -> Array (Tuple String (CacheEntry a))
cacheGetTop n cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
      sorted = Array.sortBy (\a b -> compareLastAccessed (snd a) (snd b)) allEntries
  in Array.take n sorted
  where
    compareLastAccessed :: CacheEntry a -> CacheEntry a -> Ordering
    compareLastAccessed a b = 
      if a.metadata.lastAccessed > b.metadata.lastAccessed
      then LT  -- Higher access time = more recent = should come first
      else if a.metadata.lastAccessed < b.metadata.lastAccessed
      then GT
      else EQ

-- | Filter entries by multiple conditions.
-- |
-- | Applies two predicates in sequence. Useful for complex queries.
filterEntries :: forall a. 
  (CacheEntry a -> Boolean) -> 
  (CacheEntry a -> Boolean) -> 
  CompositionCache a -> 
  Array (Tuple String (CacheEntry a))
filterEntries pred1 pred2 cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
      filtered1 = Array.filter (\e -> pred1 (snd e)) allEntries
  in Array.filter (\e -> pred2 (snd e)) filtered1

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // maintenance
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Prune all expired entries.
-- |
-- | Scans all entries and removes those past their expiresAt time.
-- | Should be called periodically for cache hygiene.
cachePruneExpired :: forall a. Number -> CompositionCache a -> CompositionCache a
cachePruneExpired now cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
      expiredKeys = Array.filter (\entry -> isExpiredEntry (snd entry) now) allEntries
  in foldl (\acc entry -> cacheInvalidate (fst entry) acc) cache expiredKeys
  where
    isExpiredEntry :: CacheEntry a -> Number -> Boolean
    isExpiredEntry entry timestamp = 
      case entry.metadata.expiresAt of
        Nothing -> false
        Just exp -> timestamp >= exp

-- | Check if cache needs eviction based on config.
-- |
-- | Returns true if the specified tier has reached its maxEntries limit.
cacheNeedsEviction :: forall a. CacheTier -> CompositionCache a -> Boolean
cacheNeedsEviction tier cache =
  let tierConfig = getTierConfig tier cache.config
      tierCount = getTierCount tier cache.stats
  in tierCount >= tierConfig.maxEntries || otherwise
  where
    getTierConfig :: CacheTier -> CacheConfig -> TierConfig
    getTierConfig TierL0 cfg = cfg.l0
    getTierConfig TierL1 cfg = cfg.l1
    getTierConfig TierL2 cfg = cfg.l2
    
    getTierCount :: CacheTier -> CacheStats -> Int
    getTierCount TierL0 s = s.l0Count
    getTierCount TierL1 s = s.l1Count
    getTierCount TierL2 s = s.l2Count
