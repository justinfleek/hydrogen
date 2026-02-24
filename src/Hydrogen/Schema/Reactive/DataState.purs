-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // reactive // datastate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataState - async data lifecycle states.
-- |
-- | Complements RemoteData with additional metadata for stale-while-revalidate,
-- | optimistic updates, and multi-phase loading.

module Hydrogen.Schema.Reactive.DataState
  ( -- * Fetch State
    FetchState(..)
  , isFetchIdle
  , isFetching
  , isFetchSuccess
  , isFetchError
  -- * Freshness
  , Freshness(..)
  , isFresh
  , isStale
  , isUnknown
  -- * Mutation State
  , MutationState(..)
  , isMutating
  , isSettled
  -- * Combined Data State
  , DataMeta
  , dataMeta
  , defaultMeta
  , shouldShowLoading
  , shouldShowStale
  , canRefresh
  -- * Retry State
  , RetryState
  , retryState
  , noRetries
  , shouldRetry
  , nextRetryDelay
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing))
import Hydrogen.Math.Core (pow)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // fetch state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Core data fetching lifecycle
data FetchState e a
  = Idle              -- ^ Not yet requested
  | Fetching          -- ^ Request in flight
  | Revalidating a    -- ^ Refetching with stale data available
  | Success a         -- ^ Request succeeded
  | Failure e         -- ^ Request failed

derive instance eqFetchState :: (Eq e, Eq a) => Eq (FetchState e a)

instance showFetchState :: (Show e, Show a) => Show (FetchState e a) where
  show Idle = "Idle"
  show Fetching = "Fetching"
  show (Revalidating a) = "Revalidating(" <> show a <> ")"
  show (Success a) = "Success(" <> show a <> ")"
  show (Failure e) = "Failure(" <> show e <> ")"

isFetchIdle :: forall e a. FetchState e a -> Boolean
isFetchIdle Idle = true
isFetchIdle _ = false

isFetching :: forall e a. FetchState e a -> Boolean
isFetching Fetching = true
isFetching (Revalidating _) = true
isFetching _ = false

isFetchSuccess :: forall e a. FetchState e a -> Boolean
isFetchSuccess (Success _) = true
isFetchSuccess (Revalidating _) = true
isFetchSuccess _ = false

isFetchError :: forall e a. FetchState e a -> Boolean
isFetchError (Failure _) = true
isFetchError _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // freshness
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Data freshness for cache management
data Freshness
  = Fresh           -- ^ Data is current
  | Stale           -- ^ Data may be outdated
  | FreshnessUnknown -- ^ No freshness info available

derive instance eqFreshness :: Eq Freshness
derive instance ordFreshness :: Ord Freshness

instance showFreshness :: Show Freshness where
  show Fresh = "fresh"
  show Stale = "stale"
  show FreshnessUnknown = "unknown"

isFresh :: Freshness -> Boolean
isFresh Fresh = true
isFresh _ = false

isStale :: Freshness -> Boolean
isStale Stale = true
isStale _ = false

isUnknown :: Freshness -> Boolean
isUnknown FreshnessUnknown = true
isUnknown _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // mutation state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | State for data mutations (create, update, delete)
data MutationState e
  = MutationIdle           -- ^ No mutation in progress
  | MutationPending        -- ^ Mutation submitted
  | MutationOptimistic     -- ^ Optimistic update applied
  | MutationSuccess        -- ^ Mutation confirmed
  | MutationError e        -- ^ Mutation failed
  | MutationRollingBack    -- ^ Reverting optimistic update

derive instance eqMutationState :: Eq e => Eq (MutationState e)

instance showMutationState :: Show e => Show (MutationState e) where
  show MutationIdle = "idle"
  show MutationPending = "pending"
  show MutationOptimistic = "optimistic"
  show MutationSuccess = "success"
  show (MutationError e) = "error(" <> show e <> ")"
  show MutationRollingBack = "rolling-back"

isMutating :: forall e. MutationState e -> Boolean
isMutating MutationIdle = false
isMutating MutationSuccess = false
isMutating _ = true

isSettled :: forall e. MutationState e -> Boolean
isSettled MutationIdle = true
isSettled MutationSuccess = true
isSettled (MutationError _) = true
isSettled _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // data metadata
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Metadata for data state (orthogonal to the data itself)
type DataMeta =
  { isFetching :: Boolean      -- ^ Request in flight
  , isStale :: Boolean         -- ^ Data may be outdated
  , isRefreshing :: Boolean    -- ^ Background refresh
  , lastFetchedAt :: Maybe Number  -- ^ Unix timestamp
  , errorCount :: Int          -- ^ Consecutive errors
  , retryCount :: Int          -- ^ Retry attempts
  }

-- | Create data metadata
dataMeta 
  :: Boolean 
  -> Boolean 
  -> Boolean 
  -> Maybe Number 
  -> Int 
  -> Int 
  -> DataMeta
dataMeta fetching stale refreshing lastFetched errors retries =
  { isFetching: fetching
  , isStale: stale
  , isRefreshing: refreshing
  , lastFetchedAt: lastFetched
  , errorCount: errors
  , retryCount: retries
  }

-- | Default metadata
defaultMeta :: DataMeta
defaultMeta =
  { isFetching: false
  , isStale: false
  , isRefreshing: false
  , lastFetchedAt: Nothing
  , errorCount: 0
  , retryCount: 0
  }

-- | Should show loading indicator?
shouldShowLoading :: DataMeta -> Boolean
shouldShowLoading m = m.isFetching && not m.isRefreshing

-- | Should show stale indicator?
shouldShowStale :: DataMeta -> Boolean
shouldShowStale m = m.isStale && m.isRefreshing

-- | Can trigger a refresh?
canRefresh :: DataMeta -> Boolean
canRefresh m = not m.isFetching

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // retry state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Retry state for exponential backoff
type RetryState =
  { attempt :: Int             -- ^ Current attempt (0 = first try)
  , maxAttempts :: Int         -- ^ Maximum attempts
  , baseDelayMs :: Number      -- ^ Base delay in ms
  , maxDelayMs :: Number       -- ^ Maximum delay cap
  , lastAttemptAt :: Maybe Number  -- ^ Unix timestamp of last attempt
  }

-- | Create retry state
retryState :: Int -> Number -> Number -> RetryState
retryState maxAttempts baseDelay maxDelay =
  { attempt: 0
  , maxAttempts
  , baseDelayMs: baseDelay
  , maxDelayMs: maxDelay
  , lastAttemptAt: Nothing
  }

-- | No retries configured
noRetries :: RetryState
noRetries = retryState 0 0.0 0.0

-- | Should retry?
shouldRetry :: RetryState -> Boolean
shouldRetry r = r.attempt < r.maxAttempts

-- | Calculate next retry delay (exponential backoff)
nextRetryDelay :: RetryState -> Number
nextRetryDelay r = 
  min r.maxDelayMs (r.baseDelayMs * pow 2.0 (toNumber r.attempt))
