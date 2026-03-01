-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // query // execution
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Query execution with caching and deduplication.
-- |
-- | This module handles the core fetch logic:
-- | - Checking cache freshness
-- | - Deduplicating concurrent requests
-- | - Retry logic
-- | - Cache updates
module Hydrogen.Query.Execution
  ( -- * Query operations
    query
  , queryWith
  , prefetch
  , getQueryData
  , setQueryData
  ) where

import Prelude
  ( class Show
  , Unit
  , bind
  , discard
  , not
  , pure
  , show
  , unit
  , void
  , ($)
  , (>)
  , (-)
  , (<$>)
  , (>>=)
  )

import Data.Argonaut (class DecodeJson, class EncodeJson, Json, decodeJson, encodeJson)
import Data.Either (Either(Left, Right), hush)
import Data.Map as Map
import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Time.Duration (Milliseconds)
import Effect (Effect)
import Effect.Aff (Aff, delay, forkAff, joinFiber)
import Effect.Class (liftEffect)
import Effect.Now (now)
import Effect.Ref as Ref
import Hydrogen.Data.RemoteData (RemoteData(Failure, Success))
import Hydrogen.Query.Types
  ( QueryClient(QueryClient)
  , QueryOptions
  , QueryState
  , CacheEntry
  , initialQueryState
  , keyToString
  , isEntryStale
  , addMs
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // query operations
-- ═══════════════════════════════════════════════════════════════════════════════

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
  -> Aff (QueryState String a)
query client opts = queryWith client opts { enabled: true }

-- | Execute a query with an enabled flag.
-- |
-- | Useful for conditional fetching:
-- | ```purescript
-- | state <- Q.queryWith client opts { enabled: userId /= "" }
-- | ```
queryWith 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a
  -> { enabled :: Boolean }
  -> Aff (QueryState String a)
queryWith _ _ { enabled: false } = pure initialQueryState
queryWith client@(QueryClient c) opts _ = do
  let cacheKey = keyToString opts.key
  
  -- Check cache
  currentTime <- liftEffect now
  cachedEntry <- liftEffect $ Map.lookup cacheKey <$> Ref.read c.cache
  
  case cachedEntry of
    -- Fresh cache hit
    Just entry | not (isEntryStale entry currentTime) -> 
      case decodeJson entry.json of
        Right a -> pure
          { data: Success a
          , isStale: false
          , isFetching: false
          }
        Left _ -> fetchFresh client opts Nothing  -- Cache corrupted, refetch
    
    -- Stale cache - return stale data + refetch
    Just entry -> do
      let staleData = hush $ decodeJson entry.json
      fetchFresh client opts staleData
    
    -- No cache
    Nothing -> fetchFresh client opts Nothing

-- | Fetch fresh data, handling deduplication and retries.
fetchFresh 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> QueryOptions a
  -> Maybe a  -- Stale data to preserve
  -> Aff (QueryState String a)
fetchFresh (QueryClient c) opts staleData = do
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
  
  -- Build QueryState from result
  pure $ case jsonResult of
    Left err -> 
      -- On error, preserve stale data if available
      case staleData of
        Just a ->
          { data: Success a  -- Keep showing stale data
          , isStale: true
          , isFetching: false
          -- Note: We could also expose the error separately
          -- For now, stale data + isStale=true signals this state
          }
        Nothing ->
          { data: Failure err
          , isStale: false
          , isFetching: false
          }
    Right json -> 
      case decodeJson json of
        Left err ->
          { data: Failure (show err)
          , isStale: false
          , isFetching: false
          }
        Right a ->
          { data: Success a
          , isStale: false
          , isFetching: false
          }

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
  -> Array String
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
  -> Array String
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
