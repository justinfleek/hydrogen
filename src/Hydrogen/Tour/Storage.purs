-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // tour // storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Persistence Operations for Product Tours — Pure ADT representation.
-- |
-- | This module generates pure ADT operations for tour state persistence.
-- | Operations are pure data that can be interpreted by a runtime.
-- |
-- | ## Design Philosophy
-- |
-- | Following Hydrogen's "UI as data" principle, storage operations are
-- | represented as algebraic data types. The runtime interprets these
-- | against the actual localStorage API. This enables:
-- | - Testability without browser dependencies
-- | - Deterministic operation sequencing
-- | - Serialization of storage intents
-- |
-- | ## Storage Keys
-- |
-- | All keys are namespaced under "hydrogen:tour:" to avoid conflicts:
-- | - "hydrogen:tour:{id}:completed" — completion timestamp
-- | - "hydrogen:tour:{id}:dismissed" — dismissal timestamp
-- | - "hydrogen:tour:{id}:snoozed-until" — snooze expiration timestamp

module Hydrogen.Tour.Storage
  ( -- * Query Operations
    TourStorageQuery(CheckCompleted, CheckDismissed, CheckSnoozed, CheckShouldShow)
  , checkCompleted
  , checkDismissed
  , checkSnoozed
  , checkShouldShow
    -- * Mutation Operations
  , TourStorageMutation(MarkCompleted, MarkDismissed, Snooze, ClearSnooze, ClearTourState)
  , markCompleted
  , markDismissed
  , snooze
  , clearSnooze
  , clearTourState
    -- * Storage Keys
  , completedKey
  , dismissedKey
  , snoozeKey
  , storagePrefix
    -- * Query Results (for runtime to construct)
  , TourQueryResult(Completed, NotCompleted, Dismissed, NotDismissed, Snoozed, NotSnoozed, ShouldShow, ShouldNotShow)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Tour.Types (Milliseconds, TourId(TourId))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // storage keys
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespace prefix for all tour storage.
storagePrefix :: String
storagePrefix = "hydrogen:tour:"

-- | Key for tour completion state.
-- |
-- | Returns: "hydrogen:tour:{id}:completed"
completedKey :: TourId -> String
completedKey (TourId id) = storagePrefix <> id <> ":completed"

-- | Key for tour dismissal state.
-- |
-- | Returns: "hydrogen:tour:{id}:dismissed"
dismissedKey :: TourId -> String
dismissedKey (TourId id) = storagePrefix <> id <> ":dismissed"

-- | Key for snooze expiration timestamp.
-- |
-- | Returns: "hydrogen:tour:{id}:snoozed-until"
snoozeKey :: TourId -> String
snoozeKey (TourId id) = storagePrefix <> id <> ":snoozed-until"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // query operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | TourStorageQuery — ADT representing read operations for tour state.
-- |
-- | These are pure data structures that the runtime interprets against
-- | localStorage. Each query specifies what information is needed.
data TourStorageQuery
  = CheckCompleted TourId      -- ^ Has tour been completed?
  | CheckDismissed TourId      -- ^ Has tour been dismissed?
  | CheckSnoozed TourId        -- ^ Is tour currently snoozed?
  | CheckShouldShow TourId     -- ^ Should tour be shown? (composite query)

derive instance eqTourStorageQuery :: Eq TourStorageQuery
derive instance ordTourStorageQuery :: Ord TourStorageQuery

instance showTourStorageQuery :: Show TourStorageQuery where
  show (CheckCompleted t) = "(CheckCompleted " <> show t <> ")"
  show (CheckDismissed t) = "(CheckDismissed " <> show t <> ")"
  show (CheckSnoozed t) = "(CheckSnoozed " <> show t <> ")"
  show (CheckShouldShow t) = "(CheckShouldShow " <> show t <> ")"

-- | Query for tour completion state.
checkCompleted :: TourId -> TourStorageQuery
checkCompleted = CheckCompleted

-- | Query for tour dismissal state.
checkDismissed :: TourId -> TourStorageQuery
checkDismissed = CheckDismissed

-- | Query for tour snooze state.
checkSnoozed :: TourId -> TourStorageQuery
checkSnoozed = CheckSnoozed

-- | Composite query: should tour be shown?
-- |
-- | Returns true if tour is not completed, not dismissed, and not snoozed.
checkShouldShow :: TourId -> TourStorageQuery
checkShouldShow = CheckShouldShow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // mutation operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | TourStorageMutation — ADT representing write operations for tour state.
-- |
-- | These are pure data structures that the runtime interprets against
-- | localStorage. Each mutation specifies what change should be made.
data TourStorageMutation
  = MarkCompleted TourId                -- ^ Mark tour as completed
  | MarkDismissed TourId                -- ^ Mark tour as dismissed
  | Snooze TourId Milliseconds          -- ^ Snooze tour for duration
  | ClearSnooze TourId                  -- ^ Clear active snooze
  | ClearTourState TourId               -- ^ Clear all state for tour

derive instance eqTourStorageMutation :: Eq TourStorageMutation
derive instance ordTourStorageMutation :: Ord TourStorageMutation

instance showTourStorageMutation :: Show TourStorageMutation where
  show (MarkCompleted t) = "(MarkCompleted " <> show t <> ")"
  show (MarkDismissed t) = "(MarkDismissed " <> show t <> ")"
  show (Snooze t ms) = "(Snooze " <> show t <> " " <> show ms <> ")"
  show (ClearSnooze t) = "(ClearSnooze " <> show t <> ")"
  show (ClearTourState t) = "(ClearTourState " <> show t <> ")"

-- | Create a MarkCompleted mutation.
-- |
-- | When interpreted, stores the current timestamp at the completed key.
markCompleted :: TourId -> TourStorageMutation
markCompleted = MarkCompleted

-- | Create a MarkDismissed mutation.
-- |
-- | When interpreted, stores the current timestamp at the dismissed key.
markDismissed :: TourId -> TourStorageMutation
markDismissed = MarkDismissed

-- | Create a Snooze mutation.
-- |
-- | When interpreted, stores (now + duration) at the snoozed-until key.
snooze :: TourId -> Milliseconds -> TourStorageMutation
snooze = Snooze

-- | Create a ClearSnooze mutation.
-- |
-- | When interpreted, removes the snoozed-until key.
clearSnooze :: TourId -> TourStorageMutation
clearSnooze = ClearSnooze

-- | Create a ClearTourState mutation.
-- |
-- | When interpreted, removes completed, dismissed, and snoozed-until keys.
clearTourState :: TourId -> TourStorageMutation
clearTourState = ClearTourState

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // query results
-- ═════════════════════════════════════════════════════════════════════════════

-- | TourQueryResult — ADT representing results of storage queries.
-- |
-- | The runtime constructs these after interpreting queries against
-- | localStorage. Application code pattern matches on results.
data TourQueryResult
  = Completed                   -- ^ Tour has been completed
  | NotCompleted                -- ^ Tour has not been completed
  | Dismissed                   -- ^ Tour has been dismissed
  | NotDismissed                -- ^ Tour has not been dismissed
  | Snoozed                     -- ^ Tour is currently snoozed
  | NotSnoozed                  -- ^ Tour is not snoozed (or snooze expired)
  | ShouldShow                  -- ^ Tour should be shown
  | ShouldNotShow               -- ^ Tour should not be shown

derive instance eqTourQueryResult :: Eq TourQueryResult
derive instance ordTourQueryResult :: Ord TourQueryResult

instance showTourQueryResult :: Show TourQueryResult where
  show Completed = "Completed"
  show NotCompleted = "NotCompleted"
  show Dismissed = "Dismissed"
  show NotDismissed = "NotDismissed"
  show Snoozed = "Snoozed"
  show NotSnoozed = "NotSnoozed"
  show ShouldShow = "ShouldShow"
  show ShouldNotShow = "ShouldNotShow"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // query key helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the localStorage key for a query operation.
-- |
-- | Used by runtime to know which key to read.
queryKey :: TourStorageQuery -> Maybe String
queryKey (CheckCompleted tid) = Just (completedKey tid)
queryKey (CheckDismissed tid) = Just (dismissedKey tid)
queryKey (CheckSnoozed tid) = Just (snoozeKey tid)
queryKey (CheckShouldShow _) = Nothing  -- Composite: needs multiple keys
