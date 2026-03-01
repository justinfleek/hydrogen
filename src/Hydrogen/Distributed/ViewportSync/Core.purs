-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // distributed // viewport-sync // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core viewport synchronization state and operations.
-- |
-- | This module defines the ViewportSync record type and basic operations
-- | for creating, updating, and querying viewport sync state.

module Hydrogen.Distributed.ViewportSync.Core
  ( -- * Viewport Sync Type
    ViewportSync
  
  -- * Construction
  , mkViewportSync
  
  -- * State Updates
  , updateSyncState
  , setFrameOffset
  , recordDrift
  , markSynchronized
  , markDisconnected
  
  -- * Queries
  , getSyncQuality
  
  -- * Helper Functions
  , clamp01
  , minInt
  , maxInt
  , absInt
  ) where

import Prelude
  ( otherwise
  , negate
  , (<)
  , (<=)
  , (>=)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  )

import Data.Number (abs)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)

import Hydrogen.Distributed.TimeAuthority 
  ( TimeAuthority
  , FrameTime
  , FrameNumber
  , getAuthorityTime
  )

import Hydrogen.Distributed.ViewportSync.Types
  ( ViewportId
  , FrameOffset
  , SyncState
      ( Synchronized
      , Drifting
      , Resynchronizing
      , Disconnected
      )
  , DriftDirection
      ( DriftingAhead
      , DriftingBehind
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // viewport sync
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport synchronization state
type ViewportSync =
  { viewportId :: ViewportId
  , authority :: TimeAuthority
  , frameOffset :: FrameOffset        -- Frames ahead (+) or behind (-) authority
  , syncState :: SyncState
  , lastSyncTime :: FrameTime         -- When last sync occurred
  , driftHistory :: Array Number      -- Recent drift measurements (for averaging)
  , maxHistorySize :: Int
  }

-- | Create new viewport sync state
mkViewportSync :: ViewportId -> TimeAuthority -> ViewportSync
mkViewportSync viewportId authority =
  { viewportId
  , authority
  , frameOffset: 0
  , syncState: Synchronized
  , lastSyncTime: getAuthorityTime authority
  , driftHistory: []
  , maxHistorySize: 10
  }

-- | Update sync state
updateSyncState :: SyncState -> ViewportSync -> ViewportSync
updateSyncState newState sync = sync { syncState = newState }

-- | Set frame offset
setFrameOffset :: FrameOffset -> ViewportSync -> ViewportSync
setFrameOffset offset sync = sync { frameOffset = offset }

-- | Record a drift measurement and update state
recordDrift :: Number -> FrameTime -> ViewportSync -> ViewportSync
recordDrift driftMs currentTime sync =
  let
    newHistory = Array.take sync.maxHistorySize 
                   (Array.cons driftMs sync.driftHistory)
    avgDrift = averageDrift newHistory
    newState = computeSyncState avgDrift sync.syncState
  in sync
    { driftHistory = newHistory
    , syncState = newState
    , lastSyncTime = currentTime
    }

-- | Mark viewport as synchronized
markSynchronized :: FrameTime -> ViewportSync -> ViewportSync
markSynchronized currentTime sync = sync
  { syncState = Synchronized
  , frameOffset = 0
  , lastSyncTime = currentTime
  , driftHistory = []
  }

-- | Mark viewport as disconnected
markDisconnected :: FrameTime -> FrameNumber -> ViewportSync -> ViewportSync
markDisconnected currentTime lastFrame sync = sync
  { syncState = Disconnected { since: currentTime, lastKnownFrame: lastFrame }
  }

-- | Get overall sync quality (0.0 = disconnected, 1.0 = perfect sync)
getSyncQuality :: ViewportSync -> Number
getSyncQuality sync = case sync.syncState of
  Synchronized -> 1.0
  Drifting r -> clamp01 (1.0 - abs r.driftMs / 100.0)
  Resynchronizing r -> r.progress * 0.5
  Disconnected _ -> 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // internal functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute sync state from average drift
-- |
-- | Note: currentState parameter reserved for hysteresis in future
-- | (e.g., require sustained drift before changing state)
computeSyncState :: Number -> SyncState -> SyncState
computeSyncState avgDrift _currentState
  | abs avgDrift < 1.0 = Synchronized
  | avgDrift > 0.0 = Drifting { driftMs: avgDrift, direction: DriftingAhead }
  | otherwise = Drifting { driftMs: abs avgDrift, direction: DriftingBehind }

-- | Compute average drift from history
averageDrift :: Array Number -> Number
averageDrift arr =
  if Array.null arr
    then 0.0
    else foldl (+) 0.0 arr / toNumber (Array.length arr)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Minimum of two integers
minInt :: Int -> Int -> Int
minInt a b = if a <= b then a else b

-- | Maximum of two integers
maxInt :: Int -> Int -> Int
maxInt a b = if a >= b then a else b

-- | Absolute value for Int
absInt :: Int -> Int
absInt n = if n < 0 then negate n else n
