-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // cache // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache Configuration — Default configurations for cache tiers.
-- |
-- | Provides sensible defaults for the three-tier cache system:
-- | - L0: Stable state (hot path, sub-millisecond)
-- | - L1: Composition results (rendered, low milliseconds)
-- | - L2: Computed/derived data (longer TTL)

module Hydrogen.Composition.Cache.Config
  ( -- * Tier Configurations
    defaultTierConfig
  , tierConfigL0
  , tierConfigL1
  , tierConfigL2
  
  -- * Full Cache Configuration
  , defaultConfig
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Hydrogen.Composition.Cache.Types (TierConfig, CacheConfig)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // tier configurations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default tier configuration.
-- |
-- | Conservative defaults suitable for most use cases:
-- | - 100 entries maximum
-- | - 10MB memory budget
-- | - 1 minute TTL
-- | - 5ms target latency
defaultTierConfig :: TierConfig
defaultTierConfig =
  { maxEntries: 100
  , maxSizeBytes: 10000000   -- 10MB
  , ttlMs: 60000.0           -- 1 minute
  , targetLatencyMs: 5.0
  }

-- | L0 tier: Stable state (hot path).
-- |
-- | Optimized for immediate access to currently visible compositions:
-- | - 1000 entries (high capacity for active UI)
-- | - 50MB memory budget
-- | - 1 minute TTL (short, frequently refreshed)
-- | - 0.1ms target latency (sub-millisecond)
tierConfigL0 :: TierConfig
tierConfigL0 =
  { maxEntries: 1000
  , maxSizeBytes: 50000000   -- 50MB
  , ttlMs: 60000.0           -- 1 minute
  , targetLatencyMs: 0.1     -- <0.1ms
  }

-- | L1 tier: Composition results.
-- |
-- | For fully composed nodes ready for GPU submission:
-- | - 500 entries (medium capacity)
-- | - 100MB memory budget (compositions can be large)
-- | - 5 minute TTL (medium duration)
-- | - 1ms target latency
tierConfigL1 :: TierConfig
tierConfigL1 =
  { maxEntries: 500
  , maxSizeBytes: 100000000  -- 100MB
  , ttlMs: 300000.0          -- 5 minutes
  , targetLatencyMs: 1.0     -- <1ms
  }

-- | L2 tier: Computed/derived data.
-- |
-- | For layout calculations, bounding boxes, hit testing data:
-- | - 200 entries (lower capacity, larger entries)
-- | - 50MB memory budget
-- | - 10 minute TTL (longer duration, computed values change less)
-- | - 5ms target latency
tierConfigL2 :: TierConfig
tierConfigL2 =
  { maxEntries: 200
  , maxSizeBytes: 50000000   -- 50MB
  , ttlMs: 600000.0          -- 10 minutes
  , targetLatencyMs: 5.0     -- <5ms
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // full configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default cache configuration.
-- |
-- | Combines all tier configurations with:
-- | - 10% eviction ratio (evict 10% when at capacity)
defaultConfig :: CacheConfig
defaultConfig =
  { l0: tierConfigL0
  , l1: tierConfigL1
  , l2: tierConfigL2
  , evictionRatio: 0.1
  }
