-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // composition // cache
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition Cache — Event-driven stable state caching.
-- |
-- | ## Design Philosophy
-- |
-- | The composition layer is **event-driven, not frame-driven**. UI is stable
-- | until an event occurs. This means:
-- |
-- | 1. **Stable states don't recalculate** — Cache composition results until
-- |    a trigger fires
-- | 2. **Content-addressed** — Same Node tree = same cache key (UUID5)
-- | 3. **Generation-aware** — Track when compositions change
-- | 4. **Tiered** — Hot path (L0) vs composition results (L1) vs computed (L2)
-- |
-- | ## Cache Tiers
-- |
-- | - **L0 (Stable State)**: Hot path, <1ms, short TTL
-- |   Currently visible compositions, immediate access
-- |   
-- | - **L1 (Composition)**: Rendered compositions, <5ms, medium TTL
-- |   Fully composed nodes ready for GPU submission
-- |   
-- | - **L2 (Computed)**: Derived properties, <10ms, longer TTL
-- |   Layout calculations, bounding boxes, hit testing data
-- |
-- | ## Invalidation Strategies
-- |
-- | 1. **Generation-based**: Entity updated → generation bumped → cache miss
-- | 2. **TTL-based**: Entries expire after configured duration
-- | 3. **Tag-based**: Invalidate related entries (e.g., brand change)
-- | 4. **Memory pressure**: Evict LRU when at capacity
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Content-addressed caching is critical:
-- | - Same composition across agents → same cache key → shared computation
-- | - Diff by ID, not content → O(1) change detection
-- | - Hierarchical grouping → 1000 agents moving = 1 invalidation
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Cache.Types`: Core type definitions
-- | - `Cache.Config`: Default configurations
-- | - `Cache.LRU`: LRU tracking operations
-- | - `Cache.Operations`: Core get/put/invalidate/evict
-- | - `Cache.Query`: Read-only queries and filtering
-- | - `Cache.Stats`: Hit/miss rates and metrics
-- | - `Cache.Identified`: Content-addressed integration
-- | - `Cache.Debug`: Debugging utilities

module Hydrogen.Composition.Cache
  ( module Types
  , module Config
  , module LRU
  , module Operations
  , module Query
  , module Stats
  , module Identified
  , module Debug
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

-- Re-export all submodules
import Hydrogen.Composition.Cache.Types as Types
import Hydrogen.Composition.Cache.Config as Config
import Hydrogen.Composition.Cache.LRU as LRU
import Hydrogen.Composition.Cache.Operations as Operations
import Hydrogen.Composition.Cache.Query as Query
import Hydrogen.Composition.Cache.Stats as Stats
import Hydrogen.Composition.Cache.Identified as Identified
import Hydrogen.Composition.Cache.Debug as Debug
