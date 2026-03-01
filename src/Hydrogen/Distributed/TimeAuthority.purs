-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // distributed // time-authority
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimeAuthority — Distributed time coordination for billion-agent scale.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, time synchronization becomes critical:
-- |
-- | - Agents across the globe must agree on "when" events occur
-- | - Animation frames must be deterministic across viewports
-- | - Causal ordering must be preserved for collaborative editing
-- | - Network latency must be compensated for smooth coordination
-- |
-- | ## Architecture
-- |
-- | This leader module re-exports functionality from submodules:
-- |
-- | - **Lamport**: Scalar logical clocks and logical time with agent ID
-- | - **VectorClock**: Vector clocks for detecting concurrent events
-- | - **ClockSync**: NTP-style wall-clock synchronization
-- | - **FrameSchedule**: Deterministic frame timing for animation
-- |
-- | ## Usage
-- |
-- | Import this module to get all time-related types and functions.
-- | For finer-grained imports, use the submodules directly.

module Hydrogen.Distributed.TimeAuthority
  ( -- * Re-exported Submodules
    module Hydrogen.Distributed.TimeAuthority.Lamport
  , module Hydrogen.Distributed.TimeAuthority.VectorClock
  , module Hydrogen.Distributed.TimeAuthority.ClockSync
  , module Hydrogen.Distributed.TimeAuthority.FrameSchedule
  
  -- * Time Authority (defined here)
  , TimeAuthority
      ( LocalAuthority
      , NetworkAuthority
      )
  , localAuthority
  , networkAuthority
  , isLocalAuthority
  , isNetworkAuthority
  , getAuthorityTime
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- Re-export all symbols from submodules
import Hydrogen.Distributed.TimeAuthority.Lamport
  ( AgentId
  , WallClock
  , LamportTime
  , mkLamportTime
  , lamportTick
  , lamportSend
  , lamportReceive
  , lamportCompare
  , happenedBefore
  , LogicalTime
  , mkLogicalTime
  , logicalTick
  , logicalSend
  , logicalReceive
  , logicalCompare
  , logicalHappenedBefore
  , maxInt
  )

import Hydrogen.Distributed.TimeAuthority.VectorClock
  ( VectorClock
  , mkVectorClock
  , vectorTick
  , vectorSend
  , vectorReceive
  , vectorMerge
  , vectorCompare
  , VectorOrdering
      ( VectorLT
      , VectorGT
      , VectorEQ
      , VectorConcurrent
      )
  , isConcurrent
  , isHappenedBefore
  , allHappenedBefore
  )

import Hydrogen.Distributed.TimeAuthority.ClockSync
  ( FrameTime
  , ClockSync
  , RttSample
  , mkClockSync
  , recordRoundTrip
  , estimateOffset
  , estimateRtt
  , syncQuality
  , SyncQuality
      ( SyncExcellent
      , SyncGood
      , SyncFair
      , SyncPoor
      , SyncUnsynced
      )
  , localToServer
  , serverToLocal
  , syncMeetsMinimum
  , getServerTimeIfSynced
  )

import Hydrogen.Distributed.TimeAuthority.FrameSchedule
  ( FrameNumber
  , FrameSchedule
  , mkFrameSchedule
  , frameToTime
  , timeToFrame
  , frameDuration
  , framesPerSecond
  , nextFrameTime
  , framesSince
  , FrameId
  , mkFrameId
  , frameIdFromTime
  , compareFrameIds
  , sameFrame
  , isValidSchedule
  , safeTimeToFrame
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // time authority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time authority — determines whose clock is authoritative
-- |
-- | In a distributed system, agents need to agree on a time source:
-- |
-- | - **LocalAuthority**: Single agent, no coordination needed
-- | - **NetworkAuthority**: Cluster synchronized to a server
data TimeAuthority
  = LocalAuthority
      { agentId :: AgentId
      , currentTime :: FrameTime
      }
  | NetworkAuthority
      { serverId :: AgentId
      , serverTime :: FrameTime
      , localOffset :: FrameTime   -- Server - Local
      , rtt :: FrameTime           -- Round-trip time
      , confidence :: Number       -- 0.0-1.0 sync quality
      }

derive instance eqTimeAuthority :: Eq TimeAuthority

instance showTimeAuthority :: Show TimeAuthority where
  show (LocalAuthority r) = "LocalAuthority(" <> r.agentId <> ")"
  show (NetworkAuthority r) = "NetworkAuthority(" <> r.serverId <> ", offset=" <> show r.localOffset <> "ms)"

-- | Create local authority (single agent, no sync needed)
localAuthority :: AgentId -> FrameTime -> TimeAuthority
localAuthority agentId currentTime = LocalAuthority { agentId, currentTime }

-- | Create network authority (coordinated cluster)
networkAuthority :: AgentId -> FrameTime -> FrameTime -> FrameTime -> Number -> TimeAuthority
networkAuthority serverId serverTime localOffset rtt confidence =
  NetworkAuthority { serverId, serverTime, localOffset, rtt, confidence }

-- | Check if using local authority
isLocalAuthority :: TimeAuthority -> Boolean
isLocalAuthority (LocalAuthority _) = true
isLocalAuthority _ = false

-- | Check if using network authority
isNetworkAuthority :: TimeAuthority -> Boolean
isNetworkAuthority (NetworkAuthority _) = true
isNetworkAuthority _ = false

-- | Get authoritative time
getAuthorityTime :: TimeAuthority -> FrameTime
getAuthorityTime (LocalAuthority r) = r.currentTime
getAuthorityTime (NetworkAuthority r) = r.serverTime
