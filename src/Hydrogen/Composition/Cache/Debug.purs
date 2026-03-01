-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // cache // debug
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache Debugging — Utilities for inspecting and comparing cache entries.
-- |
-- | This module provides debugging and diagnostic utilities:
-- | - showCacheEntry: Human-readable entry display
-- | - compareByGeneration: Compare entry generations
-- | - sameEntryContent: Check content equivalence
-- | - entryScore: Calculate eviction priority score

module Hydrogen.Composition.Cache.Debug
  ( -- * Display
    showCacheEntry
    
  -- * Comparison
  , compareByGeneration
  , sameEntryContent
  
  -- * Scoring
  , entryScore
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , not
  , ($)
  , (-)
  , (*)
  , (==)
  , (/=)
  , (<>)
  , (&&)
  )

import Hydrogen.Schema.Identity.Temporal (unwrapGeneration)

import Data.Int (toNumber)

import Hydrogen.Composition.Cache.Types (CacheEntry)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // display
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show a cache entry for debugging.
-- |
-- | Produces a human-readable summary including:
-- | - Cache tier
-- | - Generation number
-- | - Hit count
-- | - Size in bytes
showCacheEntry :: forall a. CacheEntry a -> String
showCacheEntry entry = 
  "CacheEntry { tier: " <> show entry.metadata.tier 
  <> ", gen: " <> show (unwrapGeneration entry.metadata.generation)
  <> ", hits: " <> show entry.metadata.hitCount
  <> ", size: " <> show entry.metadata.sizeBytes <> "b }"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // comparison
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compare two cache entries by generation.
-- |
-- | Returns true if the entries have different generations,
-- | indicating one is newer than the other.
compareByGeneration :: forall a. CacheEntry a -> CacheEntry a -> Boolean
compareByGeneration a b = 
  unwrapGeneration a.metadata.generation /= unwrapGeneration b.metadata.generation

-- | Check if two entries have same content (same generation and tier).
-- |
-- | Returns true if entries are considered equivalent for caching purposes.
-- | This does NOT compare the actual values, only metadata.
sameEntryContent :: forall a. CacheEntry a -> CacheEntry a -> Boolean
sameEntryContent a b = 
  not (compareByGeneration a b) && a.metadata.tier == b.metadata.tier

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // scoring
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate weighted score for cache entry (for smart eviction).
-- |
-- | Score = hitCount * recencyWeight - ageWeight * age
-- |
-- | Higher scores indicate entries that should be kept longer:
-- | - More hits = higher score
-- | - More recent access = higher score
-- | - Older entries = lower score
-- |
-- | Use this for priority-based eviction instead of pure LRU.
entryScore :: forall a. CacheEntry a -> Number -> Number
entryScore entry now =
  let hits = toNumber entry.metadata.hitCount
      age = now - entry.metadata.lastAccessed
      recencyWeight = 10.0
      ageWeight = 0.001
  in hits * recencyWeight - age * ageWeight
