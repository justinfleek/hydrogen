-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // hydrogen // query
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Data fetching with caching, deduplication, and automatic refetch.
-- |
-- | Inspired by TanStack Query, designed to work with zeitschrift-generated clients.
-- |
-- | ## Design
-- |
-- | Query state is split into two concerns:
-- |
-- | 1. **RemoteData e a** - The core data state (NotAsked, Loading, Failure, Success)
-- |    This is a lawful Monad, so you can use `do` notation and all standard combinators.
-- |
-- | 2. **QueryState e a** - Record with metadata:
-- |    ```purescript
-- |    { data :: RemoteData e a
-- |    , isStale :: Boolean      -- Data exists but may be outdated
-- |    , isFetching :: Boolean   -- Currently fetching (initial or refetch)
-- |    }
-- |    ```
-- |
-- | This design mirrors TanStack Query where `data` and `isFetching` are separate.
-- | You can show stale data while a background refetch is in progress.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Query as Q
-- | import Hydrogen.Data.RemoteData as RD
-- | 
-- | -- Create a query client (typically in your main)
-- | client <- Q.newClient Q.defaultClientOptions
-- | 
-- | -- Fetch data with caching
-- | state <- Q.query client
-- |   { key: ["user", userId]
-- |   , fetch: Api.getUser config userId
-- |   }
-- | 
-- | -- Use the RemoteData for rendering
-- | case state.data of
-- |   RD.NotAsked -> HH.text "Not loaded"
-- |   RD.Loading -> spinner
-- |   RD.Failure e -> errorCard e
-- |   RD.Success user -> userCard user
-- |
-- | -- Or use fold
-- | Q.foldData state
-- |   { notAsked: HH.text "Click to load"
-- |   , loading: spinner
-- |   , failure: \e -> errorCard e
-- |   , success: \user -> userCard user
-- |   }
-- |
-- | -- Show stale data with loading indicator
-- | if state.isFetching && Q.hasData state
-- |   then showWithSpinner (Q.getData state)
-- |   else normalRender state.data
-- | 
-- | -- Invalidate cache after mutation
-- | Q.invalidate client ["user", userId]
-- | ```
-- |
-- | ## Combining Queries with RemoteData
-- |
-- | Because RemoteData is a lawful Monad, you can combine queries naturally:
-- |
-- | ```purescript
-- | -- Using ado syntax (Applicative - parallel semantics)
-- | let combined = ado
-- |       user <- userState.data
-- |       posts <- postsState.data
-- |       in { user, posts }
-- |
-- | -- Using do syntax (Monad - sequential semantics)
-- | let dependent = do
-- |       user <- userState.data
-- |       posts <- postsState.data
-- |       pure $ renderUserWithPosts user posts
-- | ```
module Hydrogen.Query
  ( -- * Re-exports from submodules
    module Types
  , module Execution
  , module Cache
  , module Pagination
  , module Batching
  , module Helpers
  
    -- * Re-exports from RemoteData
  , module Hydrogen.Data.RemoteData
  ) where

import Hydrogen.Query.Types
  ( QueryClient
  , ClientOptions
  , defaultClientOptions
  , newClient
  , newClientWith
  , QueryKey
  , QueryOptions
  , defaultQueryOptions
  , QueryState
  , initialQueryState
  ) as Types

import Hydrogen.Query.Execution
  ( query
  , queryWith
  , prefetch
  , getQueryData
  , setQueryData
  ) as Execution

import Hydrogen.Query.Cache
  ( invalidate
  , invalidateExact
  , invalidateAll
  , removeQuery
  ) as Cache

import Hydrogen.Query.Pagination
  ( PageParam
  , PagedQueryOptions
  , PagedState
  , initialPagedState
  , queryPaged
  , fetchNextPage
  ) as Pagination

import Hydrogen.Query.Batching
  ( Batcher
  , BatchOptions
  , newBatcher
  , load
  , loadMany
  ) as Batching

import Hydrogen.Query.Helpers
  ( getData
  , getError
  , hasData
  , foldData
  , withDefaultData
  ) as Helpers

import Hydrogen.Data.RemoteData
  ( RemoteData(NotAsked, Loading, Failure, Success)
  , fromEither
  , toMaybe
  , isSuccess
  , isLoading
  , isFailure
  , isNotAsked
  , mapError
  , map2
  , map3
  , map4
  ) as Hydrogen.Data.RemoteData
