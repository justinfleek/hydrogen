-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // cache // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache Types — Core type definitions for the composition cache.
-- |
-- | This module defines the fundamental types used throughout the cache system:
-- | - CacheTier: L0/L1/L2 tiering for different access patterns
-- | - CacheTag: Tags for bulk invalidation
-- | - EntryMetadata: Per-entry tracking data
-- | - CacheEntry: Value + metadata wrapper
-- | - CacheStats: Hit/miss/eviction statistics
-- | - TierConfig: Per-tier configuration
-- | - CacheConfig: Full cache configuration
-- | - CompositionCache: The main cache structure

module Hydrogen.Composition.Cache.Types
  ( -- * Cache Tiers
    CacheTier
      ( TierL0
      , TierL1
      , TierL2
      )
    
  -- * Cache Tags
  , CacheTag
      ( TagBrand
      , TagComposition
      , TagNode
      , TagTrigger
      , TagCustom
      )
  
  -- * Entry Types
  , EntryMetadata
  , CacheEntry
  
  -- * Statistics
  , CacheStats
  
  -- * Configuration
  , TierConfig
  , CacheConfig
  
  -- * Main Cache Structure
  , CompositionCache
  
  -- * LRU Types
  , LRUNode
  , LRUTracker
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe)
import Data.Map (Map)
import Data.Set (Set)

import Hydrogen.Schema.Identity.Temporal (Generation)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // cache tiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cache tier — determines eviction policy and TTL.
-- |
-- | - **L0 (Stable State)**: Hot path, <1ms, short TTL
-- |   Currently visible compositions, immediate access
-- |   
-- | - **L1 (Composition)**: Rendered compositions, <5ms, medium TTL
-- |   Fully composed nodes ready for GPU submission
-- |   
-- | - **L2 (Computed)**: Derived properties, <10ms, longer TTL
-- |   Layout calculations, bounding boxes, hit testing data
data CacheTier
  = TierL0  -- Stable state: hot path, shortest TTL
  | TierL1  -- Composition: rendered results, medium TTL
  | TierL2  -- Computed: derived data, longer TTL

derive instance eqCacheTier :: Eq CacheTier
derive instance ordCacheTier :: Ord CacheTier

instance showCacheTier :: Show CacheTier where
  show TierL0 = "L0:StableState"
  show TierL1 = "L1:Composition"
  show TierL2 = "L2:Computed"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // cache tags
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tags for bulk invalidation.
-- |
-- | When a brand changes, invalidate all entries tagged with that brand.
-- | When a composition changes, invalidate its dependents.
data CacheTag
  = TagBrand String        -- Brand identifier
  | TagComposition String  -- Composition identifier
  | TagNode String         -- Node identifier
  | TagTrigger String      -- Trigger identifier
  | TagCustom String       -- Custom tag

derive instance eqCacheTag :: Eq CacheTag
derive instance ordCacheTag :: Ord CacheTag

instance showCacheTag :: Show CacheTag where
  show (TagBrand b) = "brand:" <> b
  show (TagComposition c) = "comp:" <> c
  show (TagNode n) = "node:" <> n
  show (TagTrigger t) = "trigger:" <> t
  show (TagCustom c) = "custom:" <> c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // entry metadata
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Metadata for a cache entry.
-- |
-- | Tracks:
-- | - tier: Which cache tier this entry belongs to
-- | - generation: Content-addressed generation for invalidation
-- | - createdAt: Timestamp when entry was created
-- | - expiresAt: Optional TTL expiration time
-- | - lastAccessed: For LRU tracking
-- | - hitCount: Access statistics
-- | - sizeBytes: Memory footprint estimate
-- | - tags: For bulk invalidation
type EntryMetadata =
  { tier :: CacheTier
  , generation :: Generation
  , createdAt :: Number      -- Timestamp (ms since epoch)
  , expiresAt :: Maybe Number -- TTL expiration
  , lastAccessed :: Number   -- For LRU tracking
  , hitCount :: Int          -- Access statistics
  , sizeBytes :: Int         -- Memory footprint estimate
  , tags :: Set CacheTag     -- For bulk invalidation
  }

-- | A cache entry with value and metadata.
type CacheEntry a =
  { value :: a
  , metadata :: EntryMetadata
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // cache stats
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cache statistics.
-- |
-- | Tracks overall cache performance:
-- | - entryCount: Total number of cached entries
-- | - totalSizeBytes: Aggregate memory usage
-- | - hits/misses: Access pattern statistics
-- | - evictions: How many entries have been evicted
-- | - l0Count/l1Count/l2Count: Per-tier entry counts
type CacheStats =
  { entryCount :: Int
  , totalSizeBytes :: Int
  , hits :: Int
  , misses :: Int
  , evictions :: Int
  , l0Count :: Int
  , l1Count :: Int
  , l2Count :: Int
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // tier configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for a single cache tier.
-- |
-- | Each tier has different characteristics:
-- | - maxEntries: Maximum entries allowed in this tier
-- | - maxSizeBytes: Maximum memory budget for this tier
-- | - ttlMs: Time-to-live before automatic expiration
-- | - targetLatencyMs: Target access latency (for monitoring)
type TierConfig =
  { maxEntries :: Int        -- Maximum entries in this tier
  , maxSizeBytes :: Int      -- Maximum memory for this tier
  , ttlMs :: Number          -- Time-to-live in milliseconds
  , targetLatencyMs :: Number -- Target access latency
  }

-- | Full cache configuration.
-- |
-- | Combines tier configs with global settings:
-- | - l0/l1/l2: Per-tier configuration
-- | - evictionRatio: Fraction to evict when at capacity (0.1 = 10%)
type CacheConfig =
  { l0 :: TierConfig
  , l1 :: TierConfig
  , l2 :: TierConfig
  , evictionRatio :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // lru tracker
-- ═══════════════════════════════════════════════════════════════════════════════

-- | LRU node for doubly-linked list simulation.
-- |
-- | In pure PureScript, we simulate O(1) LRU with sorted access times.
-- | For true O(1), this would use foreign code with mutable structures.
type LRUNode =
  { key :: String
  , accessTime :: Number
  }

-- | LRU tracker using access time ordering.
-- |
-- | Operations:
-- | - add: O(1) - insert with current time
-- | - touch: O(n) - update access time (requires rebuild)
-- | - oldest: O(n) - find minimum access time
-- | - remove: O(n) - filter out key
-- |
-- | For billion-agent scale, this should be replaced with foreign O(1) impl.
type LRUTracker =
  { entries :: Map String Number  -- key -> accessTime
  , currentTime :: Number         -- monotonic counter
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // composition cache
-- ═══════════════════════════════════════════════════════════════════════════════

-- | The composition cache — tiered, content-addressed, LRU-evicting.
-- |
-- | This is the main cache structure. It stores composition results
-- | indexed by content-addressed keys (UUID5 + generation).
-- |
-- | Fields:
-- | - entries: CacheKey string -> entry mapping
-- | - lru: Access ordering for LRU eviction
-- | - tagIndex: Tag -> keys mapping for bulk invalidation
-- | - config: Cache configuration
-- | - stats: Running statistics
type CompositionCache a =
  { entries :: Map String (CacheEntry a)  -- CacheKey string -> entry
  , lru :: LRUTracker                     -- Access ordering
  , tagIndex :: Map CacheTag (Set String) -- Tag -> keys
  , config :: CacheConfig
  , stats :: CacheStats
  }
