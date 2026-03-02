-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // query // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for the Query system.
-- |
-- | This module defines the foundational types used throughout Hydrogen.Query:
-- | - QueryClient: The opaque client managing cache and in-flight requests
-- | - QueryState: Query state with RemoteData plus metadata
-- | - QueryOptions: Configuration for individual queries
-- | - CacheEntry: Internal cache storage format
module Hydrogen.Query.Types
  ( -- * Client
    QueryClient
      ( QueryClient
      )
  , ClientOptions
  , defaultClientOptions
  , newClient
  , newClientWith
  
    -- * Query types
  , QueryKey
  , QueryOptions
  , defaultQueryOptions
  , QueryState
  , initialQueryState
  
    -- * Internal types (exported for sibling modules)
  , CacheEntry
  , keyToString
  , isEntryStale
  , addMs
  ) where

import Prelude
  ( bind
  , pure
  , ($)
  , (>)
  , (+)
  )

import Data.Argonaut (Json)
import Data.DateTime.Instant (Instant, unInstant, instant)
import Data.Either (Either)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing), fromMaybe)
import Data.Newtype (unwrap)
import Data.String as String
import Data.Time.Duration (Milliseconds(Milliseconds))
import Effect (Effect)
import Effect.Aff (Aff, Fiber)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Hydrogen.Data.RemoteData (RemoteData(NotAsked))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // client
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Opaque query client that manages cache and in-flight requests.
newtype QueryClient = QueryClient
  { cache :: Ref (Map.Map String CacheEntry)
  , inFlight :: Ref (Map.Map String (Fiber (Either String Json)))
  , options :: ClientOptions
  }

-- | Client-level configuration.
type ClientOptions =
  { -- | Default time (ms) before queries are considered stale.
    -- | Stale queries will refetch in the background.
    staleTime :: Milliseconds
    -- | Default time (ms) to keep unused data in cache.
  , cacheTime :: Milliseconds
  }

-- | Default client options.
-- | 
-- | - staleTime: 0 (always refetch)
-- | - cacheTime: 5 minutes
defaultClientOptions :: ClientOptions
defaultClientOptions =
  { staleTime: Milliseconds 0.0
  , cacheTime: Milliseconds 300000.0
  }

-- | Create a new query client with default options.
newClient :: Effect QueryClient
newClient = newClientWith defaultClientOptions

-- | Create a new query client with custom options.
newClientWith :: ClientOptions -> Effect QueryClient
newClientWith options = do
  cache <- Ref.new Map.empty
  inFlight <- Ref.new Map.empty
  pure $ QueryClient { cache, inFlight, options }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // query types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Query key - identifies a unique query.
-- | Convention: ["resource", "id"] or ["resource", "list", "filter:value"]
type QueryKey = Array String

-- | Options for a query.
type QueryOptions a =
  { -- | Unique key for this query
    key :: QueryKey
    -- | Function to fetch the data
  , fetch :: Aff (Either String a)
    -- | Override stale time for this query
  , staleTime :: Maybe Milliseconds
    -- | Number of retry attempts on failure
  , retry :: Int
    -- | Delay between retries
  , retryDelay :: Milliseconds
  }

-- | Default query options (just provide key and fetch).
defaultQueryOptions :: forall a. QueryKey -> Aff (Either String a) -> QueryOptions a
defaultQueryOptions key fetch =
  { key
  , fetch
  , staleTime: Nothing
  , retry: 0
  , retryDelay: Milliseconds 1000.0
  }

-- | Query state with RemoteData plus metadata.
-- |
-- | The `data` field contains the core RemoteData (lawful Monad).
-- | The metadata fields track additional state:
-- |
-- | - `isStale`: Data exists but may be outdated (triggers background refetch)
-- | - `isFetching`: A fetch is currently in progress (initial or refetch)
-- |
-- | This separation allows you to:
-- | 1. Use RemoteData's Monad instance for combining queries
-- | 2. Show stale data while refetching in the background
-- | 3. Distinguish between "loading for first time" vs "refreshing"
type QueryState e a =
  { data :: RemoteData e a
  , isStale :: Boolean
  , isFetching :: Boolean
  }

-- | Initial query state (not asked, not fetching).
initialQueryState :: forall e a. QueryState e a
initialQueryState =
  { data: NotAsked
  , isStale: false
  , isFetching: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // internal
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Internal cache entry format.
type CacheEntry =
  { json :: Json
  , updatedAt :: Instant
  , staleAt :: Instant
  }

-- | Convert a query key to a cache key string.
keyToString :: QueryKey -> String
keyToString = String.joinWith ":"

-- | Check if a cache entry is stale at the given time.
isEntryStale :: CacheEntry -> Instant -> Boolean
isEntryStale entry currentTime = 
  toMs currentTime > toMs entry.staleAt
  where
  toMs inst = unwrap (unInstant inst)

-- | Add milliseconds to an instant.
-- | Falls back to original instant if result would be invalid.
addMs :: Instant -> Milliseconds -> Instant
addMs inst (Milliseconds delta) =
  let Milliseconds current = unInstant inst
      newMs = Milliseconds (current + delta)
  in fromMaybe inst (instant newMs)
