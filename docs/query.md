# Hydrogen.Query

Data fetching with caching, deduplication, and stale-while-revalidate.

Inspired by TanStack Query, designed for PureScript/Halogen applications.

## Overview

```purescript
import Hydrogen.Query as Q

-- Create a query client (once, at app startup)
client <- Q.newClient

-- Fetch data with automatic caching
result <- Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser config userId
  }

-- Render based on result
case result of
  Q.QueryIdle -> mempty
  Q.QueryLoading -> loadingSpinner
  Q.QueryRefetching user -> renderUser user <> loadingBadge
  Q.QueryError err mStale -> errorCard err (map renderUser mStale)
  Q.QuerySuccess user -> renderUser user
```

## Core Concepts

### Query Keys

Every query has a key - an array of strings that uniquely identifies it:

```purescript
["user", "123"]           -- User with ID 123
["users", "list"]         -- List of all users
["posts", "user:123"]     -- Posts for user 123
["search", "query:foo"]   -- Search results for "foo"
```

Keys are used for:
- **Caching**: Same key = same cached data
- **Deduplication**: Concurrent requests to same key share one fetch
- **Invalidation**: Invalidate by prefix (`["user"]` invalidates all user queries)

### QueryResult States

```
QueryIdle         -- No request made yet
    │
    ▼
QueryLoading      -- First fetch in progress
    │
    ├──▶ QuerySuccess a        -- Fetch succeeded
    │         │
    │         ▼
    │    QueryRefetching a     -- Refetching with stale data shown
    │         │
    │         ├──▶ QuerySuccess a    -- New data arrived
    │         │
    │         └──▶ QueryError e (Just a)  -- Failed, but have stale
    │
    └──▶ QueryError e Nothing  -- First fetch failed
```

The key insight: **QueryRefetching** and **QueryError with stale data** let you show
*something* to the user while fetching, rather than a loading spinner.

## Basic Usage

### Creating a Client

```purescript
main :: Effect Unit
main = do
  -- Default options: staleTime=0, cacheTime=5min
  client <- Q.newClient
  
  -- Or with custom options
  client <- Q.newClientWith
    { staleTime: Milliseconds 30000.0   -- Fresh for 30s
    , cacheTime: Milliseconds 600000.0  -- Keep in cache 10min
    }
  
  -- Pass client through your app (via context, props, etc.)
  runHalogenAff $ runUI (component client) ...
```

### Simple Query

```purescript
fetchUser :: Q.QueryClient -> String -> Aff (Q.QueryResult User)
fetchUser client userId = Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser config userId
  , staleTime: Nothing     -- Use client default
  , retry: 3               -- Retry 3 times on failure
  , retryDelay: Milliseconds 1000.0
  }
```

### Conditional Fetching

```purescript
-- Only fetch if we have a userId
result <- Q.queryWith client opts { enabled: userId /= "" }
```

### Prefetching

```purescript
-- Fetch in background (for hover prefetch, etc.)
Q.prefetch client
  { key: ["user", nextUserId]
  , fetch: Api.getUser config nextUserId
  , ...
  }
```

## Cache Operations

### Manual Cache Updates

```purescript
-- Optimistically update after mutation
handleSubmit newUser = do
  -- Update cache immediately
  liftEffect $ Q.setQueryData client ["user", newUser.id] newUser
  
  -- Then do the actual mutation
  result <- Api.updateUser config newUser
  
  -- If it failed, invalidate to refetch
  when (isLeft result) $
    liftEffect $ Q.invalidate client ["user", newUser.id]
```

### Invalidation

```purescript
-- Invalidate specific query
Q.invalidateExact client ["user", "123"]

-- Invalidate all queries matching prefix
Q.invalidate client ["user"]  -- All user queries
Q.invalidate client ["posts"] -- All post queries

-- Nuclear option
Q.invalidateAll client
```

### Reading Cache

```purescript
-- Check if we have cached data
mUser <- Q.getQueryData client ["user", "123"]
case mUser of
  Just user -> log $ "Cached: " <> user.name
  Nothing -> log "Not in cache"
```

## Combining Queries

QueryResult is **Applicative** (but not Monad - see [Why No Monad?](#why-no-monad)).

Use `ado` syntax to combine independent queries:

```purescript
import Prelude

renderDashboard :: Aff (Q.QueryResult DashboardData)
renderDashboard = do
  userResult <- Q.query client userOpts
  postsResult <- Q.query client postsOpts
  statsResult <- Q.query client statsOpts
  
  -- Combine with ado
  pure $ ado
    user <- userResult
    posts <- postsResult
    stats <- statsResult
    in { user, posts, stats }
```

Or with applicative operators:

```purescript
mkDashboard <$> userResult <*> postsResult <*> statsResult
  where
  mkDashboard user posts stats = { user, posts, stats }
```

### State Propagation

When combining results:

| Combined states | Result |
|-----------------|--------|
| All `Success` | `Success` |
| Any `Error` | `Error` (first one wins) |
| Any `Loading` (no errors) | `Loading` |
| Any `Idle` (no errors/loading) | `Idle` |
| Mix of `Success`/`Refetching` | `Refetching` |

## Pagination

```purescript
type Page = { items :: Array Item, nextCursor :: Maybe String }

pagedOpts :: Q.PagedQueryOptions Page
pagedOpts =
  { key: ["items", "list"]
  , fetch: \cursor -> Api.listItems config { cursor, limit: 20 }
  , getNextPageParam: _.nextCursor
  }

-- Initial fetch
result <- Q.queryPaged client pagedOpts

-- Load more
result' <- Q.fetchNextPage client pagedOpts result

-- Check if more available
case result' of
  Q.PagedSuccess { pages, hasNextPage } ->
    if hasNextPage
      then showLoadMoreButton
      else mempty
  _ -> mempty
```

## Request Batching

For DataLoader-style batching (e.g., fetch N users in one request):

```purescript
-- Create a batcher
userBatcher <- Q.newBatcher
  { batchFn: \ids -> Api.getUsersByIds config ids
  , maxBatchSize: 100
  , batchDelay: Milliseconds 10.0  -- Wait 10ms to collect requests
  }

-- Load single user (batched with concurrent requests)
result <- Q.load userBatcher "user-123"

-- Load multiple
results <- Q.loadMany userBatcher ["user-1", "user-2", "user-3"]
```

## Helper Functions

### Extracting Data

```purescript
Q.getData result       -- Maybe a (from Success, Refetching, or stale in Error)
Q.getError result      -- Maybe String
Q.withDefault [] result  -- Use default if no data
```

### Predicates

```purescript
Q.isLoading result   -- True for Loading or Refetching
Q.isSuccess result   -- True for Success only
Q.isError result     -- True for Error
```

### Pattern Matching with fold

```purescript
Q.fold
  { idle: HH.text "Click to load"
  , loading: \mStale -> case mStale of
      Nothing -> loadingSpinner
      Just data -> renderData data <> loadingBadge
  , error: \msg mStale -> 
      errorCard msg <> maybe mempty renderData mStale
  , success: renderData
  }
  result
```

## Why No Monad?

QueryResult has 5 states, not 4. The extra states (`QueryRefetching a`, `QueryError e (Maybe a)`)
carry "stale data" which enables stale-while-revalidate UX.

But this breaks the Monad laws. Specifically, right-identity:

```purescript
-- Monad law: m >>= pure ≡ m
-- But:
QueryRefetching 42 >>= pure
= pure 42
= QuerySuccess 42
≠ QueryRefetching 42  -- Law violated!
```

So we provide **Applicative only**. This is actually fine because:

1. **Applicative handles combining**: `ado` syntax works for N independent queries
2. **Dependent fetches use Aff**: If query B needs result of query A, that's `Aff` Monad, not `QueryResult`

```purescript
-- Dependent fetches happen in Aff, not QueryResult
fetchUserAndPosts :: Aff (Q.QueryResult { user :: User, posts :: Array Post })
fetchUserAndPosts = do
  userResult <- Q.query client userOpts
  case Q.getData userResult of
    Nothing -> pure userResult $> { user: _, posts: [] }  -- Can't continue
    Just user -> do
      postsResult <- Q.query client (postsOpts user.id)
      pure $ { user: _, posts: _ } <$> userResult <*> postsResult
```

## Integration with RemoteData

If you're using RemoteData elsewhere, convert at boundaries:

```purescript
-- QueryResult → RemoteData-style record
Q.toRemoteData result
-- { notAsked :: Boolean, loading :: Boolean, error :: Maybe String, data :: Maybe a }

-- Either → QueryResult
Q.fromRemoteData (Right user)  -- QuerySuccess user
Q.fromRemoteData (Left err)    -- QueryError err Nothing
```

For full RemoteData compatibility, pattern match:

```purescript
queryResultToRemoteData :: forall a. Q.QueryResult a -> RemoteData String a
queryResultToRemoteData = case _ of
  Q.QueryIdle -> NotAsked
  Q.QueryLoading -> Loading
  Q.QueryRefetching _ -> Loading  -- Loses stale data
  Q.QueryError e _ -> Failure e   -- Loses stale data
  Q.QuerySuccess a -> Success a
```

Note: Converting loses stale-while-revalidate information. Consider whether you
actually need the conversion, or if `Q.fold` is sufficient.
