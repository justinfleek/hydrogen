-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // distributed // time-authority // clock-sync
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NTP-style clock synchronization for distributed agents.
-- |
-- | ## Purpose
-- |
-- | When agents need wall-clock coordination (not just causal ordering):
-- |
-- | - Animation playback synchronized across viewports
-- | - Scheduled events at agreed-upon times
-- | - Deadline coordination in collaborative systems
-- |
-- | ## Algorithm
-- |
-- | Uses round-trip time (RTT) measurements:
-- |
-- | 1. Send request, record local send time (t1)
-- | 2. Server responds with its timestamp (t2)
-- | 3. Receive response, record local receive time (t3)
-- | 4. RTT = t3 - t1
-- | 5. Offset ≈ t2 - (t1 + RTT/2)
-- |
-- | Multiple samples averaged for stability.

module Hydrogen.Distributed.TimeAuthority.ClockSync
  ( -- * Frame Time Alias
    FrameTime
  
  -- * Clock Synchronization State
  , ClockSync
  , RttSample
  , mkClockSync
  , recordRoundTrip
  , estimateOffset
  , estimateRtt
  , syncQuality
  
  -- * Sync Quality
  , SyncQuality
      ( SyncExcellent
      , SyncGood
      , SyncFair
      , SyncPoor
      , SyncUnsynced
      )
  
  -- * Time Conversion
  , localToServer
  , serverToLocal
  
  -- * Predicates
  , syncMeetsMinimum
  , getServerTimeIfSynced
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , map
  , (<=)
  , (<)
  , (-)
  , (+)
  , (/)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Distributed.TimeAuthority.Lamport (AgentId, WallClock)

-- | Alias for frame timing values (milliseconds)
type FrameTime = Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // clock synchronization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clock synchronization state (NTP-style)
-- |
-- | Maintains history of round-trip measurements to estimate offset and quality.
type ClockSync =
  { serverId :: AgentId
  , samples :: Array RttSample
  , maxSamples :: Int
  , estimatedOffset :: FrameTime
  , estimatedRtt :: FrameTime
  , quality :: SyncQuality
  }

-- | Single RTT measurement sample
type RttSample =
  { sendTime :: WallClock      -- Local time when request sent
  , receiveTime :: WallClock   -- Local time when response received
  , serverTime :: WallClock    -- Server's timestamp in response
  }

-- | Synchronization quality level
data SyncQuality
  = SyncExcellent    -- RTT < 10ms, low variance
  | SyncGood         -- RTT < 50ms, reasonable variance
  | SyncFair         -- RTT < 200ms
  | SyncPoor         -- RTT < 1000ms
  | SyncUnsynced     -- No valid samples or RTT >= 1000ms

derive instance eqSyncQuality :: Eq SyncQuality
derive instance ordSyncQuality :: Ord SyncQuality

instance showSyncQuality :: Show SyncQuality where
  show SyncExcellent = "Excellent"
  show SyncGood = "Good"
  show SyncFair = "Fair"
  show SyncPoor = "Poor"
  show SyncUnsynced = "Unsynced"

-- | Create initial clock sync state
mkClockSync :: AgentId -> ClockSync
mkClockSync serverId =
  { serverId
  , samples: []
  , maxSamples: 8  -- Keep last 8 samples
  , estimatedOffset: 0.0
  , estimatedRtt: 0.0
  , quality: SyncUnsynced
  }

-- | Record a round-trip measurement
recordRoundTrip :: WallClock -> WallClock -> WallClock -> ClockSync -> ClockSync
recordRoundTrip sendTime receiveTime serverTime sync =
  let
    sample = { sendTime, receiveTime, serverTime }
    newSamples = Array.take sync.maxSamples (Array.cons sample sync.samples)
    newRtt = computeRtt newSamples
    newOffset = computeOffset newSamples
    newQuality = computeQuality newRtt
  in sync
    { samples = newSamples
    , estimatedRtt = newRtt
    , estimatedOffset = newOffset
    , quality = newQuality
    }

-- | Get estimated offset (server - local)
estimateOffset :: ClockSync -> FrameTime
estimateOffset sync = sync.estimatedOffset

-- | Get estimated round-trip time
estimateRtt :: ClockSync -> FrameTime
estimateRtt sync = sync.estimatedRtt

-- | Get sync quality
syncQuality :: ClockSync -> SyncQuality
syncQuality sync = sync.quality

-- | Convert local time to estimated server time
localToServer :: ClockSync -> WallClock -> WallClock
localToServer sync localTime = localTime + sync.estimatedOffset

-- | Convert server time to estimated local time
serverToLocal :: ClockSync -> WallClock -> WallClock
serverToLocal sync serverTime = serverTime - sync.estimatedOffset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if sync quality meets minimum threshold
syncMeetsMinimum :: SyncQuality -> ClockSync -> Boolean
syncMeetsMinimum minimum sync = sync.quality <= minimum

-- | Try to get server time if sync quality is acceptable
getServerTimeIfSynced :: SyncQuality -> WallClock -> ClockSync -> Maybe WallClock
getServerTimeIfSynced minQuality localTime sync =
  if sync.quality <= minQuality
    then Just (localToServer sync localTime)
    else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // helper functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute average RTT from samples
computeRtt :: Array RttSample -> FrameTime
computeRtt samples =
  if Array.null samples
    then 0.0
    else
      let rtts = map (\s -> s.receiveTime - s.sendTime) samples
          total = foldl (+) 0.0 rtts
      in total / toNumber (Array.length samples)

-- | Compute offset using NTP formula: offset = ((t2-t1) + (t3-t4)) / 2
-- | Where t1=send, t2=server receive (approx), t3=server send (approx), t4=receive
-- | Simplified: offset = serverTime - (sendTime + RTT/2)
computeOffset :: Array RttSample -> FrameTime
computeOffset samples =
  if Array.null samples
    then 0.0
    else
      let offsets = map (\s ->
            let rtt = s.receiveTime - s.sendTime
                localMidpoint = s.sendTime + rtt / 2.0
            in s.serverTime - localMidpoint
          ) samples
          total = foldl (+) 0.0 offsets
      in total / toNumber (Array.length samples)

-- | Determine quality based on RTT
computeQuality :: FrameTime -> SyncQuality
computeQuality rtt
  | rtt < 10.0 = SyncExcellent
  | rtt < 50.0 = SyncGood
  | rtt < 200.0 = SyncFair
  | rtt < 1000.0 = SyncPoor
  | otherwise = SyncUnsynced
