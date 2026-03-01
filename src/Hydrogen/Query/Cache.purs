-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // query // cache
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Cache invalidation operations for the Query system.
-- |
-- | This module provides functions to mark cached data as stale or remove it:
-- | - invalidate: Mark queries matching a prefix as stale
-- | - invalidateExact: Mark a specific query as stale
-- | - invalidateAll: Mark all queries as stale
-- | - removeQuery: Remove a query from cache entirely
module Hydrogen.Query.Cache
  ( -- * Cache invalidation
    invalidate
  , invalidateExact
  , invalidateAll
  , removeQuery
  ) where

import Prelude
  ( Unit
  , bind
  , map
  , otherwise
  )

import Data.Map as Map
import Data.Maybe (Maybe(Just))
import Data.String as String
import Effect (Effect)
import Effect.Now (now)
import Effect.Ref as Ref
import Hydrogen.Query.Types
  ( QueryClient(QueryClient)
  , QueryKey
  , keyToString
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // cache invalidation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Invalidate all queries matching a key prefix.
-- |
-- | ```purescript
-- | -- Invalidate all user queries
-- | Q.invalidate client ["user"]
-- | 
-- | -- Invalidate specific user
-- | Q.invalidate client ["user", "123"]
-- | ```
invalidate :: QueryClient -> QueryKey -> Effect Unit
invalidate (QueryClient c) prefix = do
  let prefixStr = keyToString prefix
  currentTime <- now
  Ref.modify_ (Map.mapMaybeWithKey (markStaleIfMatches prefixStr currentTime)) c.cache
  where
  markStaleIfMatches prefixStr currentTime key entry
    | String.contains (String.Pattern prefixStr) key = 
        Just entry { staleAt = currentTime }
    | otherwise = Just entry

-- | Invalidate a query with an exact key match.
invalidateExact :: QueryClient -> QueryKey -> Effect Unit
invalidateExact (QueryClient c) key = do
  currentTime <- now
  Ref.modify_ (Map.update (\e -> Just e { staleAt = currentTime }) (keyToString key)) c.cache

-- | Invalidate all queries in the cache.
invalidateAll :: QueryClient -> Effect Unit
invalidateAll (QueryClient c) = do
  currentTime <- now
  Ref.modify_ (map \e -> e { staleAt = currentTime }) c.cache

-- | Remove a query from the cache entirely.
removeQuery :: QueryClient -> QueryKey -> Effect Unit
removeQuery (QueryClient c) key = 
  Ref.modify_ (Map.delete (keyToString key)) c.cache
