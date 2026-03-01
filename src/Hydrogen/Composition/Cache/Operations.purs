-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // cache // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache Operations — Core get/put/invalidate/evict operations.
-- |
-- | This module provides the fundamental cache operations:
-- | - emptyCache: Create a new empty cache
-- | - cacheGet: Retrieve entries (with LRU update)
-- | - cachePut: Store entries (with tag indexing)
-- | - cacheInvalidate: Remove specific entries
-- | - cacheInvalidateByTag: Bulk invalidation by tag
-- | - cacheEvictLRU: Evict least recently used entries
-- | - cacheStats: Get current statistics

module Hydrogen.Composition.Cache.Operations
  ( -- * Cache Construction
    emptyCache
    
  -- * Core Operations
  , cacheGet
  , cachePut
  , cacheInvalidate
  , cacheInvalidateByTag
  , cacheEvictLRU
  , cacheStats
  
  -- * Internal Helpers (exported for Query module)
  , updateTierCount
  , addToTagIndex
  , removeFromTagIndex
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( negate
  , ($)
  , (+)
  , (-)
  , (>=)
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set (empty, insert, delete, toUnfoldable) as Set
import Data.Foldable (foldl)

import Hydrogen.Composition.Cache.Types 
  ( CacheTier(TierL0, TierL1, TierL2)
  , CacheTag
  , CacheEntry
  , EntryMetadata
  , CacheStats
  , CacheConfig
  , CompositionCache
  )

import Hydrogen.Composition.Cache.LRU 
  ( emptyLRU
  , lruAdd
  , lruTouch
  , lruRemove
  , lruOldest
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // cache construction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an empty cache with the given configuration.
-- |
-- | Initializes all counters to zero and creates empty data structures.
emptyCache :: forall a. CacheConfig -> CompositionCache a
emptyCache config =
  { entries: Map.empty
  , lru: emptyLRU
  , tagIndex: Map.empty
  , config: config
  , stats: emptyStats
  }
  where
    emptyStats :: CacheStats
    emptyStats =
      { entryCount: 0
      , totalSizeBytes: 0
      , hits: 0
      , misses: 0
      , evictions: 0
      , l0Count: 0
      , l1Count: 0
      , l2Count: 0
      }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // core operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get an entry from the cache.
-- |
-- | Returns Just entry if found and not expired, Nothing otherwise.
-- | Updates LRU on hit, removes expired entries on access.
-- |
-- | The returned cache has updated statistics (hit/miss counters).
cacheGet :: forall a. String -> Number -> CompositionCache a -> { result :: Maybe a, cache :: CompositionCache a }
cacheGet key now cache =
  case Map.lookup key cache.entries of
    Nothing -> 
      -- Cache miss
      { result: Nothing
      , cache: cache { stats = cache.stats { misses = cache.stats.misses + 1 } }
      }
    Just entry ->
      -- Check expiration
      if isExpired entry.metadata now
      then 
        -- Expired: remove and return miss
        let newEntries = Map.delete key cache.entries
            newLRU = lruRemove key cache.lru
        in { result: Nothing
           , cache: cache 
               { entries = newEntries
               , lru = newLRU
               , stats = cache.stats { misses = cache.stats.misses + 1, entryCount = cache.stats.entryCount - 1 }
               }
           }
      else
        -- Hit: update LRU and stats
        let newLRU = lruTouch key cache.lru
            newEntry = entry { metadata = entry.metadata { hitCount = entry.metadata.hitCount + 1, lastAccessed = now } }
            newEntries = Map.insert key newEntry cache.entries
        in { result: Just entry.value
           , cache: cache 
               { entries = newEntries
               , lru = newLRU
               , stats = cache.stats { hits = cache.stats.hits + 1 }
               }
           }
  where
    isExpired :: EntryMetadata -> Number -> Boolean
    isExpired meta timestamp = 
      case meta.expiresAt of
        Nothing -> false
        Just exp -> timestamp >= exp

-- | Put an entry into the cache.
-- |
-- | Adds the entry to the cache, updates LRU tracking, and indexes by tags.
-- | Does NOT automatically evict - call cacheEvictLRU separately if needed.
cachePut :: forall a. String -> a -> EntryMetadata -> CompositionCache a -> CompositionCache a
cachePut key value metadata cache =
  let 
    -- Create entry
    entry :: CacheEntry a
    entry = { value: value, metadata: metadata }
    
    -- Add to entries and LRU
    newEntries = Map.insert key entry cache.entries
    newLRU = lruAdd key cache.lru
    
    -- Update tag index
    newTagIndex = addToTagIndex key metadata.tags cache.tagIndex
    
    -- Update tier counts
    newStats = updateTierCount metadata.tier 1 cache.stats
    
  in cache
    { entries = newEntries
    , lru = newLRU
    , tagIndex = newTagIndex
    , stats = newStats { entryCount = newStats.entryCount + 1, totalSizeBytes = newStats.totalSizeBytes + metadata.sizeBytes }
    }

-- | Invalidate a specific cache entry by key.
-- |
-- | Removes the entry from all data structures and updates statistics.
-- | No-op if key doesn't exist.
cacheInvalidate :: forall a. String -> CompositionCache a -> CompositionCache a
cacheInvalidate key cache =
  case Map.lookup key cache.entries of
    Nothing -> cache
    Just entry ->
      let 
        newEntries = Map.delete key cache.entries
        newLRU = lruRemove key cache.lru
        newTagIndex = removeFromTagIndex key entry.metadata.tags cache.tagIndex
        newStats = updateTierCount entry.metadata.tier (-1) cache.stats
      in cache
        { entries = newEntries
        , lru = newLRU
        , tagIndex = newTagIndex
        , stats = newStats { entryCount = newStats.entryCount - 1, totalSizeBytes = newStats.totalSizeBytes - entry.metadata.sizeBytes }
        }

-- | Invalidate all entries with a specific tag.
-- |
-- | Useful for bulk invalidation when a related entity changes
-- | (e.g., brand update invalidates all brand-tagged entries).
cacheInvalidateByTag :: forall a. CacheTag -> CompositionCache a -> CompositionCache a
cacheInvalidateByTag tag cache =
  case Map.lookup tag cache.tagIndex of
    Nothing -> cache
    Just keys -> 
      let keyArray :: Array String
          keyArray = Set.toUnfoldable keys
      in foldl (\acc k -> cacheInvalidate k acc) cache keyArray

-- | Evict LRU entries until entry count is at or below target.
-- |
-- | Repeatedly removes the least recently used entry until the cache
-- | has at most targetCount entries. Updates eviction statistics.
cacheEvictLRU :: forall a. Int -> CompositionCache a -> CompositionCache a
cacheEvictLRU targetCount cache =
  if cache.stats.entryCount >= targetCount
  then case lruOldest cache.lru of
    Nothing -> cache
    Just oldestKey ->
      let newCache = cacheInvalidate oldestKey cache
          updatedCache = newCache { stats = newCache.stats { evictions = newCache.stats.evictions + 1 } }
      in cacheEvictLRU targetCount updatedCache
  else cache

-- | Get cache statistics.
-- |
-- | Returns the current statistics snapshot.
cacheStats :: forall a. CompositionCache a -> CacheStats
cacheStats cache = cache.stats

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // internal helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Add a key to the tag index for all its tags.
addToTagIndex :: String -> Set CacheTag -> Map CacheTag (Set String) -> Map CacheTag (Set String)
addToTagIndex k tags idx =
  let tagArray :: Array CacheTag
      tagArray = Set.toUnfoldable tags
  in foldl (\acc tag -> 
       let existing = fromMaybe Set.empty (Map.lookup tag acc)
       in Map.insert tag (Set.insert k existing) acc
     ) idx tagArray

-- | Remove a key from the tag index for all its tags.
removeFromTagIndex :: String -> Set CacheTag -> Map CacheTag (Set String) -> Map CacheTag (Set String)
removeFromTagIndex k tags idx =
  let tagArray :: Array CacheTag
      tagArray = Set.toUnfoldable tags
  in foldl (\acc tag ->
       case Map.lookup tag acc of
         Nothing -> acc
         Just keys -> Map.insert tag (Set.delete k keys) acc
     ) idx tagArray

-- | Update tier-specific entry count.
updateTierCount :: CacheTier -> Int -> CacheStats -> CacheStats
updateTierCount TierL0 delta stats = stats { l0Count = stats.l0Count + delta }
updateTierCount TierL1 delta stats = stats { l1Count = stats.l1Count + delta }
updateTierCount TierL2 delta stats = stats { l2Count = stats.l2Count + delta }
