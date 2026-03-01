-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // query // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pagination support for the Query system.
-- |
-- | This module provides cursor-based pagination:
-- | - PageParam: Cursor type for pagination
-- | - PagedQueryOptions: Configuration for paginated queries
-- | - PagedState: State for paginated queries with page tracking
-- | - queryPaged: Execute a paginated query
-- | - fetchNextPage: Fetch the next page of results
module Hydrogen.Query.Pagination
  ( -- * Pagination types
    PageParam
  , PagedQueryOptions
  , PagedState
  , initialPagedState
  
    -- * Pagination operations
  , queryPaged
  , fetchNextPage
  ) where

import Prelude
  ( bind
  , pure
  , ($)
  , (/=)
  , (<>)
  , (>>=)
  )

import Data.Argonaut (class DecodeJson, class EncodeJson)
import Data.Array as Array
import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Nothing, Just))
import Effect.Aff (Aff)
import Hydrogen.Data.RemoteData (RemoteData(NotAsked, Failure, Success))
import Hydrogen.Query.Types (QueryClient, QueryKey)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // pagination types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page parameter for cursor-based pagination.
type PageParam = Maybe String

-- | Options for paginated queries.
type PagedQueryOptions a =
  { key :: QueryKey
  , fetch :: PageParam -> Aff (Either String a)
  , getNextPageParam :: a -> PageParam
  }

-- | State for paginated queries.
type PagedState e a =
  { data :: RemoteData e (Array a)
  , pages :: Array a
  , hasNextPage :: Boolean
  , isFetching :: Boolean
  , isFetchingNextPage :: Boolean
  }

-- | Initial paged state.
initialPagedState :: forall e a. PagedState e a
initialPagedState =
  { data: NotAsked
  , pages: []
  , hasNextPage: false
  , isFetching: false
  , isFetchingNextPage: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // pagination operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Execute a paginated query.
queryPaged 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> PagedQueryOptions a 
  -> Aff (PagedState String a)
queryPaged _client opts = do
  result <- opts.fetch Nothing
  pure $ case result of
    Left err ->
      { data: Failure err
      , pages: []
      , hasNextPage: false
      , isFetching: false
      , isFetchingNextPage: false
      }
    Right a ->
      { data: Success [a]
      , pages: [a]
      , hasNextPage: opts.getNextPageParam a /= Nothing
      , isFetching: false
      , isFetchingNextPage: false
      }

-- | Fetch the next page.
fetchNextPage 
  :: forall a
   . DecodeJson a 
  => EncodeJson a
  => QueryClient 
  -> PagedQueryOptions a
  -> PagedState String a
  -> Aff (PagedState String a)
fetchNextPage _client opts state = do
  let lastPage = Array.last state.pages
  let nextCursor = lastPage >>= opts.getNextPageParam
  case nextCursor of
    Nothing -> pure state { hasNextPage = false }
    Just cursor -> do
      result <- opts.fetch (Just cursor)
      pure $ case result of
        Left err ->
          state { data = Failure err, isFetchingNextPage = false }
        Right newPage ->
          let newPages = state.pages <> [newPage]
          in state
            { data = Success newPages
            , pages = newPages
            , hasNextPage = opts.getNextPageParam newPage /= Nothing
            , isFetchingNextPage = false
            }
