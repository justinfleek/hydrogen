-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // distributed // viewport-sync // integration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Integration with TimeAuthority subsystems.
-- |
-- | This module provides functions to integrate ViewportSync with:
-- |
-- | - TimeAuthority (local vs network)
-- | - FrameSchedule (expected frame computation)
-- | - ClockSync (quality-based confidence)
-- | - VectorClock (causal ordering)

module Hydrogen.Distributed.ViewportSync.Integration
  ( -- * Time Authority Integration
    mkViewportSyncLocal
  , mkViewportSyncNetwork
  , viewportUsesNetwork
  , viewportUsesLocal
  , getViewportAuthorityTime
  
  -- * Frame Schedule Integration
  , computeExpectedFrame
  , computeNextFrameTime
  , viewportIsBehind
  , viewportIsAhead
  , getScheduleFps
  , getScheduleFrameDuration
  
  -- * Clock Sync Integration
  , mkViewportSyncWithClockSync
  , syncQualityToNumber
  , viewportMeetsSyncQuality
  , viewportLocalToServer
  , viewportServerToLocal
  
  -- * Vector Clock Integration
  , ViewportSyncWithCausality
  , mkViewportSyncWithCausality
  , tickCausality
  , receiveCausality
  , checkCausalOrder
  , areConcurrent
  ) where

import Prelude
  ( (<)
  , (>)
  , (>=)
  , (-)
  , (+)
  , ($)
  )

import Hydrogen.Distributed.TimeAuthority 
  ( TimeAuthority
      ( LocalAuthority
      , NetworkAuthority
      )
  , FrameTime
  , FrameNumber
  , AgentId
  , WallClock
  , isNetworkAuthority
  , isLocalAuthority
  , getAuthorityTime
  , localAuthority
  , networkAuthority
  , FrameSchedule
  , frameToTime
  , timeToFrame
  , frameDuration
  , framesPerSecond
  , ClockSync
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
  , LamportTime
  , mkLamportTime
  , lamportTick
  , lamportReceive
  , VectorClock
  , mkVectorClock
  , vectorTick
  , vectorReceive
  , vectorCompare
  , VectorOrdering
      ( VectorConcurrent
      )
  )

import Hydrogen.Distributed.ViewportSync.Core
  ( ViewportSync
  , mkViewportSync
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // time authority integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create viewport sync with local authority
mkViewportSyncLocal :: String -> AgentId -> WallClock -> ViewportSync
mkViewportSyncLocal viewportId agentId currentTime =
  mkViewportSync viewportId (localAuthority agentId currentTime)

-- | Create viewport sync with network authority
mkViewportSyncNetwork :: String -> AgentId -> FrameTime -> FrameTime -> FrameTime -> Number -> ViewportSync
mkViewportSyncNetwork viewportId serverId serverTime offset rtt confidence =
  mkViewportSync viewportId (networkAuthority serverId serverTime offset rtt confidence)

-- | Check if viewport is using network authority
viewportUsesNetwork :: ViewportSync -> Boolean
viewportUsesNetwork sync = isNetworkAuthority sync.authority

-- | Check if viewport is using local authority
viewportUsesLocal :: ViewportSync -> Boolean
viewportUsesLocal sync = isLocalAuthority sync.authority

-- | Get viewport's authority time
getViewportAuthorityTime :: ViewportSync -> FrameTime
getViewportAuthorityTime sync = getAuthorityTime sync.authority

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // frame schedule integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute expected frame for viewport at given time
computeExpectedFrame :: FrameSchedule -> WallClock -> ViewportSync -> FrameNumber
computeExpectedFrame schedule currentTime sync =
  timeToFrame schedule currentTime + sync.frameOffset

-- | Compute time of next frame for viewport
computeNextFrameTime :: FrameSchedule -> WallClock -> FrameTime
computeNextFrameTime schedule currentTime =
  let currentFrame = timeToFrame schedule currentTime
  in frameToTime schedule (currentFrame + 1)

-- | Check if viewport is behind schedule
viewportIsBehind :: FrameSchedule -> WallClock -> FrameNumber -> ViewportSync -> Boolean
viewportIsBehind schedule currentTime actualFrame sync =
  let expected = computeExpectedFrame schedule currentTime sync
  in actualFrame < expected

-- | Check if viewport is ahead of schedule
viewportIsAhead :: FrameSchedule -> WallClock -> FrameNumber -> ViewportSync -> Boolean
viewportIsAhead schedule currentTime actualFrame sync =
  let expected = computeExpectedFrame schedule currentTime sync
  in actualFrame > expected

-- | Get frames per second from schedule
getScheduleFps :: FrameSchedule -> Number
getScheduleFps = framesPerSecond

-- | Get frame duration from schedule
getScheduleFrameDuration :: FrameSchedule -> FrameTime
getScheduleFrameDuration = frameDuration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // clock sync integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create viewport sync with clock sync state
mkViewportSyncWithClockSync :: String -> AgentId -> ClockSync -> WallClock -> ViewportSync
mkViewportSyncWithClockSync viewportId serverId clockSync localTime =
  let quality = syncQuality clockSync
      serverTime = localToServer clockSync localTime
      offset = serverTime - localTime
      rtt = 0.0  -- Not tracked here, would come from ClockSync
      confidence = syncQualityToNumber quality
  in mkViewportSyncNetwork viewportId serverId serverTime offset rtt confidence

-- | Convert sync quality to numeric confidence
syncQualityToNumber :: SyncQuality -> Number
syncQualityToNumber q = case q of
  SyncExcellent -> 1.0
  SyncGood -> 0.8
  SyncFair -> 0.5
  SyncPoor -> 0.2
  SyncUnsynced -> 0.0

-- | Check if viewport sync quality meets minimum
viewportMeetsSyncQuality :: SyncQuality -> ViewportSync -> Boolean
viewportMeetsSyncQuality minQuality sync = case sync.authority of
  LocalAuthority _ -> true  -- Local is always "synced" with itself
  NetworkAuthority r -> r.confidence >= syncQualityToNumber minQuality

-- | Convert local time to server time for viewport
viewportLocalToServer :: ClockSync -> WallClock -> WallClock
viewportLocalToServer = localToServer

-- | Convert server time to local time for viewport  
viewportServerToLocal :: ClockSync -> WallClock -> WallClock
viewportServerToLocal = serverToLocal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // vector clock integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | ViewportSync with vector clock for causal ordering
type ViewportSyncWithCausality =
  { sync :: ViewportSync
  , vectorClock :: VectorClock
  , lamportTime :: LamportTime
  }

-- | Create viewport sync with causality tracking
mkViewportSyncWithCausality :: String -> TimeAuthority -> ViewportSyncWithCausality
mkViewportSyncWithCausality viewportId authority =
  { sync: mkViewportSync viewportId authority
  , vectorClock: mkVectorClock viewportId
  , lamportTime: mkLamportTime
  }

-- | Tick causality clocks for local event
tickCausality :: ViewportSyncWithCausality -> ViewportSyncWithCausality
tickCausality vsc = vsc
  { vectorClock = vectorTick vsc.sync.viewportId vsc.vectorClock
  , lamportTime = lamportTick vsc.lamportTime
  }

-- | Receive causality update from another viewport
receiveCausality :: VectorClock -> LamportTime -> ViewportSyncWithCausality -> ViewportSyncWithCausality
receiveCausality remoteVc remoteLt vsc = vsc
  { vectorClock = vectorReceive vsc.sync.viewportId vsc.vectorClock remoteVc
  , lamportTime = lamportReceive vsc.lamportTime remoteLt
  }

-- | Check causal ordering between two viewport states
checkCausalOrder :: ViewportSyncWithCausality -> ViewportSyncWithCausality -> VectorOrdering
checkCausalOrder a b = vectorCompare a.vectorClock b.vectorClock

-- | Are two viewport states causally concurrent?
areConcurrent :: ViewportSyncWithCausality -> ViewportSyncWithCausality -> Boolean
areConcurrent a b = case checkCausalOrder a b of
  VectorConcurrent -> true
  _ -> false
