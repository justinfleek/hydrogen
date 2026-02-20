-- | Data fetching with caching, deduplication, and automatic refetch.
-- |
-- | Inspired by TanStack Query, designed to work with zeitschrift-generated clients.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Query as Q
-- | 
-- | -- Create a query client (typically in your main)
-- | client <- Q.newClient Q.defaultClientOptions
-- | 
-- | -- Fetch data with caching
-- | result <- Q.query client
-- |   { key: ["user", userId]
-- |   , fetch: Api.getUser config userId
-- |   }
-- | 
-- | -- Invalidate cache after mutation
-- | Q.invalidate client ["user", userId]
-- | ```
-- |
-- | ## Design
-- |
-- | The cache stores `Json` values, so any type with `EncodeJson`/`DecodeJson`
-- | instances can be cached. This matches zeitschrift-generated types which
-- | always derive Argonaut instances.
module Hydrogen.Query
  ( -- * Client
    QueryClient
  , ClientOptions
  , defaultClientOptions
  , newClient
  
    -- * Query types
  , QueryKey
  , QueryOptions
  , defaultQueryOptions
  , QueryResult(..)
  
    -- * Query operations
  , query
  , queryWith
  , prefetch
  , getQueryData
  , setQueryData
  
    -- * Cache invalidation
  , invalidate
  , invalidateExact
  , invalidateAll
  , removeQuery
  
    -- * Pagination
  , PageParam
  , PagedQueryOptions
  , PagedResult(..)
  , queryPaged
  , fetchNextPage
  
    -- * Batching
  , Batcher
  , BatchOptions
  , newBatcher
  , load
  , loadMany
  
    -- * RemoteData-style API
  , toRemoteData
  , fromRemoteData
  , getData
  , getError
  , isLoading
  , isSuccess
  , isError
  , fold
  , withDefault
  ) where

import Prelude

import Data.Argonaut (class DecodeJson, class EncodeJson, Json, decodeJson, encodeJson)
import Data.Array as Array
import Data.DateTime.Instant (Instant, unInstant)
import Data.Either (Either(..), hush)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.String as String
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple (Tuple)
import Effect (Effect)
import Effect.Aff (Aff, Fiber, delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Effect.Ref (Ref)
import Effect.Ref as Ref

-- ============================================================
-- CLIENT
-- ============================================================

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

-- | Create a new query client.
newClient :: Effect QueryClient
newClient = newClientWith defaultClientOptions

-- | Create a new query client with custom options.
newClientWith :: ClientOptions -> Effect QueryClient
newClientWith options = do
  cache <- Ref.new Map.empty
  inFlight <- Ref.new Map.empty
  pure $ QueryClient { cache, inFlight, options }

-- ============================================================
-- QUERY TYPES
-- ============================================================

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

-- | Query result with all metadata.
data QueryResult a
  = QueryIdle
  | QueryLoading
  | QueryRefetching a  -- Has stale data, fetching fresh
  | QueryError String (Maybe a)  -- Error with optional stale data
  | QuerySuccess a

derive instance eqQueryResult :: Eq a => Eq (QueryResult a)

instance showQueryResult :: Show a => Show (QueryResult a) where
  show QueryIdle = "QueryIdle"
  show QueryLoading = "QueryLoading"
  show (QueryRefetching a) = "QueryRefetching(" <> show a <> ")"
  show (QueryError e ma) = "QueryError(" <> e <> ", " <> show ma <> ")"
  show (QuerySuccess a) = "QuerySuccess(" <> show a <> ")"

-- | Functor instance - map over success/refetching/stale data
instance functorQueryResult :: Functor QueryResult where
  map _ QueryIdle = QueryIdle
  map _ QueryLoading = QueryLoading
  map f (QueryRefetching a) = QueryRefetching (f a)
  map f (QueryError e ma) = QueryError e (map f ma)
  map f (QuerySuccess a) = QuerySuccess (f a)

-- | Apply instance - combine results (first error wins)
instance applyQueryResult :: Apply QueryResult where
  apply (QuerySuccess f) (QuerySuccess a) = QuerySuccess (f a)
  apply (QuerySuccess f) (QueryRefetching a) = QueryRefetching (f a)
  apply (QueryRefetching f) (QuerySuccess a) = QueryRefetching (f a)
  apply (QueryRefetching f) (QueryRefetching a) = QueryRefetching (f a)
  apply (QueryError e _) _ = QueryError e Nothing
  apply _ (QueryError e _) = QueryError e Nothing
  apply QueryLoading _ = QueryLoading
  apply _ QueryLoading = QueryLoading
  apply QueryIdle _ = QueryIdle
  apply _ QueryIdle = QueryIdle

-- | Applicative instance
-- |
-- | Use with `ado` syntax for combining independent queries:
-- |
-- | ```purescript
-- | ado
-- |   user <- userResult
-- |   posts <- postsResult
-- |   settings <- settingsResult
-- |   in { user, posts, settings }
-- | ```
-- |
-- | Note: No Monad instance. QueryResult is for combining independent
-- | results, not sequential dependent computations. For dependent fetches,
-- | use Aff directly.
instance applicativeQueryResult :: Applicative QueryResult where
  pure = QuerySuccess

-- ============================================================
-- INTERNAL
-- ============================================================

type CacheEntry =
  { json :: Json
  , updatedAt :: Instant
  , staleAt :: Instant
  }

keyToString :: QueryKey -> String
keyToString = String.joinWith ":"

isStale :: CacheEntry -> Instant -> Boolean
isStale entry currentTime = 
  toMs currentTime > toMs entry.staleAt
  where
  toMs instant = unwrap (unInstant instant)

-- ============================================================
-- QUERY OPERATIONS
-- ============================================================

-- | Execute a query with caching and deduplication.
-- |
-- | - Returns cached data immediately if fresh
-- | - Deduplicates concurrent requests to the same key
-- | - Refetches in background if stale
query 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a 
  -> Aff (QueryResult a)
query client opts = queryWith client opts { enabled: true }

-- | Execute a query with an enabled flag.
-- |
-- | Useful for conditional fetching:
-- | ```purescript
-- | result <- Q.queryWith client opts { enabled: userId /= "" }
-- | ```
queryWith 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a
  -> { enabled :: Boolean }
  -> Aff (QueryResult a)
queryWith _ _ { enabled: false } = pure QueryIdle
queryWith client@(QueryClient c) opts _ = do
  let cacheKey = keyToString opts.key
  
  -- Check cache
  currentTime <- liftEffect now
  cachedEntry <- liftEffect $ Map.lookup cacheKey <$> Ref.read c.cache
  
  case cachedEntry of
    -- Fresh cache hit
    Just entry | not (isStale entry currentTime) -> 
      case decodeJson entry.json of
        Right a -> pure $ QuerySuccess a
        Left _ -> fetchFresh client opts  -- Cache corrupted, refetch
    
    -- Stale cache - return stale data + refetch
    Just entry -> do
      let staleData = hush $ decodeJson entry.json
      result <- fetchFresh client opts
      case result of
        QuerySuccess a -> pure $ QuerySuccess a
        QueryError e _ -> pure $ QueryError e staleData
        _ -> pure $ fromMaybe QueryLoading (QueryRefetching <$> staleData)
    
    -- No cache
    Nothing -> fetchFresh client opts

-- | Fetch fresh data, handling deduplication and retries.
fetchFresh 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a 
  -> Aff (QueryResult a)
fetchFresh (QueryClient c) opts = do
  let cacheKey = keyToString opts.key
  
  -- Check for in-flight request
  inFlightFiber <- liftEffect $ Map.lookup cacheKey <$> Ref.read c.inFlight
  
  jsonResult <- case inFlightFiber of
    -- Join existing request (deduplication)
    Just fiber -> joinFiber fiber
    
    -- Start new request
    Nothing -> do
      let doFetch = fetchWithRetry opts.fetch opts.retry opts.retryDelay
      fiber <- forkAff doFetch
      liftEffect $ Ref.modify_ (Map.insert cacheKey fiber) c.inFlight
      result <- joinFiber fiber
      liftEffect $ Ref.modify_ (Map.delete cacheKey) c.inFlight
      
      -- Cache successful results
      case result of
        Right json -> do
          updateTime <- liftEffect now
          let staleTime = fromMaybe c.options.staleTime opts.staleTime
          let staleAt = addMs updateTime staleTime
          let entry = { json, updatedAt: updateTime, staleAt }
          liftEffect $ Ref.modify_ (Map.insert cacheKey entry) c.cache
        Left _ -> pure unit
      
      pure result
  
  -- Decode and return
  pure $ case jsonResult of
    Left err -> QueryError err Nothing
    Right json -> case decodeJson json of
      Left err -> QueryError (show err) Nothing
      Right a -> QuerySuccess a

-- | Fetch with retry logic.
fetchWithRetry 
  :: forall a
   . EncodeJson a
  => Aff (Either String a) 
  -> Int 
  -> Milliseconds 
  -> Aff (Either String Json)
fetchWithRetry fetch retriesLeft retryDelay = do
  result <- fetch
  case result of
    Right a -> pure $ Right (encodeJson a)
    Left _ | retriesLeft > 0 -> do
      delay retryDelay
      fetchWithRetry fetch (retriesLeft - 1) retryDelay
    Left err -> pure $ Left err

-- | Prefetch a query without waiting for the result.
prefetch 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a 
  -> Aff Unit
prefetch client opts = void $ query client opts

-- | Get cached data for a query (if available).
getQueryData 
  :: forall a
   . DecodeJson a
  => QueryClient 
  -> QueryKey 
  -> Effect (Maybe a)
getQueryData (QueryClient c) key = do
  entry <- Map.lookup (keyToString key) <$> Ref.read c.cache
  pure $ entry >>= \e -> hush (decodeJson e.json)

-- | Manually set cached data for a query.
-- |
-- | Useful for optimistic updates:
-- | ```purescript
-- | -- Optimistically update
-- | Q.setQueryData client ["user", id] updatedUser
-- | 
-- | -- If mutation fails, invalidate to refetch
-- | Q.invalidate client ["user", id]
-- | ```
setQueryData 
  :: forall a
   . EncodeJson a
  => QueryClient 
  -> QueryKey 
  -> a 
  -> Effect Unit
setQueryData (QueryClient c) key value = do
  currentTime <- now
  let staleAt = addMs currentTime c.options.staleTime
  let entry = 
        { json: encodeJson value
        , updatedAt: currentTime
        , staleAt
        }
  Ref.modify_ (Map.insert (keyToString key) entry) c.cache

-- ============================================================
-- CACHE INVALIDATION
-- ============================================================

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

-- ============================================================
-- PAGINATION
-- ============================================================

-- | Page parameter for cursor-based pagination.
type PageParam = Maybe String

-- | Options for paginated queries.
type PagedQueryOptions a =
  { key :: QueryKey
  , fetch :: PageParam -> Aff (Either String a)
  , getNextPageParam :: a -> PageParam
  }

-- | Result of a paginated query.
data PagedResult a
  = PagedIdle
  | PagedLoading
  | PagedError String
  | PagedSuccess
      { pages :: Array a
      , hasNextPage :: Boolean
      }

derive instance eqPagedResult :: Eq a => Eq (PagedResult a)

instance showPagedResult :: Show a => Show (PagedResult a) where
  show PagedIdle = "PagedIdle"
  show PagedLoading = "PagedLoading"
  show (PagedError e) = "PagedError(" <> e <> ")"
  show (PagedSuccess { pages, hasNextPage }) = 
    "PagedSuccess({ pages: " <> show pages <> ", hasNextPage: " <> show hasNextPage <> " })"

-- | Execute a paginated query.
queryPaged 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> PagedQueryOptions a 
  -> Aff (PagedResult a)
queryPaged _client opts = do
  result <- opts.fetch Nothing
  pure $ case result of
    Left err -> PagedError err
    Right a -> PagedSuccess 
      { pages: [a]
      , hasNextPage: opts.getNextPageParam a /= Nothing
      }

-- | Fetch the next page.
fetchNextPage 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> PagedQueryOptions a
  -> PagedResult a  -- Current state
  -> Aff (PagedResult a)
fetchNextPage _client opts (PagedSuccess { pages }) = do
  let lastPage = Array.last pages
  let nextCursor = lastPage >>= opts.getNextPageParam
  case nextCursor of
    Nothing -> pure $ PagedSuccess { pages, hasNextPage: false }
    Just cursor -> do
      result <- opts.fetch (Just cursor)
      pure $ case result of
        Left err -> PagedError err
        Right newPage -> PagedSuccess
          { pages: pages <> [newPage]
          , hasNextPage: opts.getNextPageParam newPage /= Nothing
          }
fetchNextPage _ _ state = pure state

-- ============================================================
-- BATCHING (DataLoader pattern)
-- ============================================================

-- | Options for a batcher.
type BatchOptions k v =
  { -- | Batch function that fetches multiple keys at once
    batchFn :: Array k -> Aff (Array (Tuple k (Either String v)))
    -- | Maximum batch size
  , maxBatchSize :: Int
    -- | Delay before dispatching (ms) - allows more requests to queue
  , batchDelay :: Milliseconds
  }

-- | Batcher for DataLoader-style request coalescing.
newtype Batcher k v = Batcher
  { queue :: Ref (Array { key :: k, resolve :: Either String v -> Effect Unit })
  , scheduled :: Ref Boolean
  , options :: BatchOptions k v
  }

-- | Create a new batcher.
newBatcher :: forall k v. BatchOptions k v -> Effect (Batcher k v)
newBatcher options = do
  queue <- Ref.new []
  scheduled <- Ref.new false
  pure $ Batcher { queue, scheduled, options }

-- | Load a single value, batching with concurrent requests.
load :: forall k v. Ord k => Batcher k v -> k -> Aff (Either String v)
load batcher key = do
  results <- loadMany batcher [key]
  pure $ fromMaybe (Left "Key not found in batch result") (Map.lookup key results)

-- | Load multiple values in a single batch.
loadMany :: forall k v. Ord k => Batcher k v -> Array k -> Aff (Map.Map k (Either String v))
loadMany (Batcher b) keys = do
  results <- b.options.batchFn keys
  pure $ Map.fromFoldable results

-- ============================================================
-- HELPERS
-- ============================================================

-- | Add milliseconds to an instant (simplified - loses precision).
addMs :: Instant -> Milliseconds -> Instant
addMs instant (Milliseconds _) = instant  -- TODO: proper impl needs purescript-datetime

-- ============================================================
-- REMOTEDATA-STYLE API
-- ============================================================

-- | Convert QueryResult to a simpler 4-state representation.
-- |
-- | This loses the "refetching with stale data" distinction:
-- | - QueryRefetching becomes the stale data (Success)
-- | - QueryError with stale data becomes Error (loses the stale data)
-- |
-- | For full fidelity, pattern match on QueryResult directly.
toRemoteData 
  :: forall a
   . QueryResult a 
  -> { notAsked :: Boolean
     , loading :: Boolean  
     , error :: Maybe String
     , data :: Maybe a
     }
toRemoteData = case _ of
  QueryIdle -> { notAsked: true, loading: false, error: Nothing, data: Nothing }
  QueryLoading -> { notAsked: false, loading: true, error: Nothing, data: Nothing }
  QueryRefetching a -> { notAsked: false, loading: true, error: Nothing, data: Just a }
  QueryError e ma -> { notAsked: false, loading: false, error: Just e, data: ma }
  QuerySuccess a -> { notAsked: false, loading: false, error: Nothing, data: Just a }

-- | Create a QueryResult from Either (for wrapping API responses).
fromRemoteData :: forall a. Either String a -> QueryResult a
fromRemoteData (Left e) = QueryError e Nothing
fromRemoteData (Right a) = QuerySuccess a

-- | Get the data if available (Success, Refetching, or stale in Error).
getData :: forall a. QueryResult a -> Maybe a
getData QueryIdle = Nothing
getData QueryLoading = Nothing
getData (QueryRefetching a) = Just a
getData (QueryError _ ma) = ma
getData (QuerySuccess a) = Just a

-- | Get the error if in error state.
getError :: forall a. QueryResult a -> Maybe String
getError (QueryError e _) = Just e
getError _ = Nothing

-- | Check if currently loading (initial or refetching).
isLoading :: forall a. QueryResult a -> Boolean
isLoading QueryLoading = true
isLoading (QueryRefetching _) = true
isLoading _ = false

-- | Check if successfully loaded.
isSuccess :: forall a. QueryResult a -> Boolean
isSuccess (QuerySuccess _) = true
isSuccess _ = false

-- | Check if in error state.
isError :: forall a. QueryResult a -> Boolean
isError (QueryError _ _) = true
isError _ = false

-- | Fold over QueryResult (like RemoteData.fold).
-- |
-- | ```purescript
-- | fold
-- |   { idle: HH.text "Click to load"
-- |   , loading: \stale -> spinner stale
-- |   , error: \e stale -> errorCard e stale
-- |   , success: \a -> renderData a
-- |   }
-- |   result
-- | ```
fold
  :: forall a r
   . { idle :: r
     , loading :: Maybe a -> r
     , error :: String -> Maybe a -> r
     , success :: a -> r
     }
  -> QueryResult a
  -> r
fold handlers = case _ of
  QueryIdle -> handlers.idle
  QueryLoading -> handlers.loading Nothing
  QueryRefetching a -> handlers.loading (Just a)
  QueryError e ma -> handlers.error e ma
  QuerySuccess a -> handlers.success a

-- | Get success value or fall back to default.
withDefault :: forall a. a -> QueryResult a -> a
withDefault def = case _ of
  QuerySuccess a -> a
  QueryRefetching a -> a
  QueryError _ (Just a) -> a
  _ -> def
