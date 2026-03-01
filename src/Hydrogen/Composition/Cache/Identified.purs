-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // cache // identified
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Content-Addressed Cache Integration — Operations using Identified values.
-- |
-- | This module bridges the cache system with Hydrogen's content-addressed
-- | identity system. Identified values carry UUID5 + Generation, enabling:
-- | - Deterministic cache keys from content
-- | - Generation-aware invalidation
-- | - Same content = same key across agents

module Hydrogen.Composition.Cache.Identified
  ( -- * Content-Addressed Operations
    cacheGetIdentified
  , cachePutIdentified
  
  -- * Key Generation
  , identifiedToCacheKey
  , makeCacheKeyPair
  
  -- * Generation Utilities
  , initialEntryGeneration
  , bumpEntryGeneration
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( ($)
  )

import Data.Maybe (Maybe)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Schema.Identity.Temporal 
  ( CacheKey
  , Generation
  , Identified
  , toCacheKey
  , cacheKeyString
  , initialGeneration
  , nextGeneration
  )

import Hydrogen.Composition.Cache.Types 
  ( CacheEntry
  , EntryMetadata
  , CompositionCache
  )

import Hydrogen.Composition.Cache.Operations 
  ( cacheGet
  , cachePut
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // content-addressed operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get an entry using an Identified value's cache key.
-- |
-- | Extracts the content-addressed key from the Identified value
-- | and performs a standard cache lookup.
cacheGetIdentified :: forall a b. Identified b -> Number -> CompositionCache a -> { result :: Maybe a, cache :: CompositionCache a }
cacheGetIdentified identified now cache =
  let key = cacheKeyString $ toCacheKey identified
  in cacheGet key now cache

-- | Put an entry using an Identified value's cache key.
-- |
-- | Uses the content-addressed key and updates the metadata
-- | with the Identified value's generation for proper tracking.
cachePutIdentified :: forall a b. Identified b -> a -> EntryMetadata -> CompositionCache a -> CompositionCache a
cachePutIdentified identified value metadata cache =
  let key = cacheKeyString $ toCacheKey identified
      -- Update metadata generation from the identified value
      updatedMetadata = metadata { generation = getGeneration identified }
  in cachePut key value updatedMetadata cache
  where
    getGeneration :: Identified b -> Generation
    getGeneration id = id.generation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // key generation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get the cache key for an identified value.
-- |
-- | Useful for pre-computing keys before cache operations,
-- | or for comparing keys across different identified values.
identifiedToCacheKey :: forall a. Identified a -> CacheKey
identifiedToCacheKey = toCacheKey

-- | Tuple constructor wrapper for explicit usage.
-- |
-- | Creates a key-entry pair for use in cache iteration results.
makeCacheKeyPair :: forall a. String -> CacheEntry a -> Tuple String (CacheEntry a)
makeCacheKeyPair key entry = Tuple key entry

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // generation utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create initial generation for new entries.
-- |
-- | Use this when creating cache entries for values that don't
-- | yet have a generation (e.g., freshly computed results).
initialEntryGeneration :: Generation
initialEntryGeneration = initialGeneration

-- | Bump generation for cache invalidation tracking.
-- |
-- | When a cached value is updated, bump its generation to ensure
-- | stale cache entries are recognized as outdated.
bumpEntryGeneration :: Generation -> Generation
bumpEntryGeneration = nextGeneration
