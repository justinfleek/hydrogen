-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // cache // lru
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LRU Tracker — Least Recently Used tracking for cache eviction.
-- |
-- | Provides pure PureScript LRU tracking using access time ordering.
-- | Operations are O(1) for add, O(n) for touch/oldest/remove.
-- |
-- | For billion-agent scale with true O(1) requirements, this should
-- | be replaced with foreign code using mutable doubly-linked lists.

module Hydrogen.Composition.Cache.LRU
  ( -- * LRU Operations
    emptyLRU
  , lruAdd
  , lruTouch
  , lruRemove
  , lruOldest
  , lruSize
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , compare
  , ($)
  , (+)
  )

import Data.Array (head, sortBy) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Map as Map
import Data.Tuple (Tuple, fst, snd)

import Hydrogen.Composition.Cache.Types (LRUTracker)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // lru operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty LRU tracker.
-- |
-- | Creates a new tracker with no entries and time starting at 0.
emptyLRU :: LRUTracker
emptyLRU = { entries: Map.empty, currentTime: 0.0 }

-- | Add a key to LRU (or update if exists).
-- |
-- | O(1) operation. Inserts the key with current time and bumps the counter.
lruAdd :: String -> LRUTracker -> LRUTracker
lruAdd key tracker =
  { entries: Map.insert key tracker.currentTime tracker.entries
  , currentTime: tracker.currentTime + 1.0
  }

-- | Touch a key (update access time).
-- |
-- | O(n) operation due to map update. Returns unchanged tracker if key
-- | doesn't exist.
lruTouch :: String -> LRUTracker -> LRUTracker
lruTouch key tracker =
  case Map.lookup key tracker.entries of
    Nothing -> tracker
    Just _ -> 
      { entries: Map.insert key tracker.currentTime tracker.entries
      , currentTime: tracker.currentTime + 1.0
      }

-- | Remove a key from LRU.
-- |
-- | O(n) operation. Returns unchanged tracker if key doesn't exist.
lruRemove :: String -> LRUTracker -> LRUTracker
lruRemove key tracker =
  { entries: Map.delete key tracker.entries
  , currentTime: tracker.currentTime
  }

-- | Get the oldest key (lowest access time).
-- |
-- | O(n) operation - must scan all entries to find minimum.
-- | Returns Nothing if tracker is empty.
lruOldest :: LRUTracker -> Maybe String
lruOldest tracker =
  let pairs = Map.toUnfoldable tracker.entries :: Array (Tuple String Number)
      sorted = Array.sortBy (\a b -> compare (snd a) (snd b)) pairs
  in map fst (Array.head sorted)

-- | Get LRU size (number of tracked keys).
-- |
-- | O(1) operation using Map.size.
lruSize :: LRUTracker -> Int
lruSize tracker = Map.size tracker.entries
