-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // distributed // viewport-sync // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for viewport synchronization.
-- |
-- | This module defines the fundamental type aliases and ADTs used throughout
-- | the ViewportSync system: identifiers, sync states, drift directions,
-- | and effect phases.

module Hydrogen.Distributed.ViewportSync.Types
  ( -- * Core Aliases
    ViewportId
  , EffectId
  , FrameOffset
  
  -- * Sync State
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
  , isSynchronized
  , isDrifting
  , isResynchronizing
  , isDisconnected
  
  -- * Effect Phase
  , EffectPhase
      ( EffectIdle
      , EffectRunning
      , EffectComplete
      , EffectPaused
      )
  
  -- * Cluster State
  , ClusterState
      ( ClusterSynced
      , ClusterPartialSync
      , ClusterDesync
      , ClusterEmpty
      )
  
  -- * Reconciliation Strategy
  , ReconciliationStrategy
      ( NoReconciliation
      , CatchUp
      , SlowDown
      , MeetInMiddle
      , ForceResync
      )
  
  -- * Drift Compensation
  , DriftCompensation
      ( NoCompensation
      , SkipFrames
      , InterpolateFrames
      , PauseAndWait
      , HardResync
      )
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Distributed.TimeAuthority 
  ( FrameTime
  , FrameNumber
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // core aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique viewport identifier
type ViewportId = String

-- | Unique effect identifier
type EffectId = String

-- | Frame offset (positive = ahead, negative = behind)
type FrameOffset = Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // sync state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Synchronization state of a viewport relative to authority
data SyncState
  = Synchronized                      -- Within tolerance of authority
  | Drifting 
      { driftMs :: Number             -- Milliseconds drifting per frame
      , direction :: DriftDirection   -- Getting ahead or behind
      }
  | Resynchronizing
      { targetFrame :: FrameNumber    -- Frame we're trying to reach
      , progress :: Number            -- 0.0-1.0 resync progress
      }
  | Disconnected
      { since :: FrameTime            -- When disconnect was detected
      , lastKnownFrame :: FrameNumber -- Last synchronized frame
      }

derive instance eqSyncState :: Eq SyncState

instance showSyncState :: Show SyncState where
  show Synchronized = "Synchronized"
  show (Drifting r) = "Drifting(" <> show r.driftMs <> "ms/" <> show r.direction <> ")"
  show (Resynchronizing r) = "Resynchronizing(target=" <> show r.targetFrame <> ")"
  show (Disconnected r) = "Disconnected(since=" <> show r.since <> "ms)"

-- | Direction of drift
data DriftDirection
  = DriftingAhead   -- Local clock running fast
  | DriftingBehind  -- Local clock running slow

derive instance eqDriftDirection :: Eq DriftDirection

instance showDriftDirection :: Show DriftDirection where
  show DriftingAhead = "Ahead"
  show DriftingBehind = "Behind"

-- | Check if synchronized
isSynchronized :: SyncState -> Boolean
isSynchronized Synchronized = true
isSynchronized _ = false

-- | Check if drifting
isDrifting :: SyncState -> Boolean
isDrifting (Drifting _) = true
isDrifting _ = false

-- | Check if resynchronizing
isResynchronizing :: SyncState -> Boolean
isResynchronizing (Resynchronizing _) = true
isResynchronizing _ = false

-- | Check if disconnected
isDisconnected :: SyncState -> Boolean
isDisconnected (Disconnected _) = true
isDisconnected _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // effect phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effect phase (simplified animation phase)
data EffectPhase
  = EffectIdle
  | EffectRunning Number    -- Progress 0.0-1.0
  | EffectComplete
  | EffectPaused Number     -- Progress when paused

derive instance eqEffectPhase :: Eq EffectPhase

instance showEffectPhase :: Show EffectPhase where
  show EffectIdle = "Idle"
  show (EffectRunning p) = "Running(" <> show p <> ")"
  show EffectComplete = "Complete"
  show (EffectPaused p) = "Paused(" <> show p <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cluster state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overall cluster synchronization state
data ClusterState
  = ClusterSynced             -- All viewports synchronized
  | ClusterPartialSync Int    -- N viewports out of sync
  | ClusterDesync             -- Majority out of sync
  | ClusterEmpty              -- No viewports

derive instance eqClusterState :: Eq ClusterState

instance showClusterState :: Show ClusterState where
  show ClusterSynced = "Synced"
  show (ClusterPartialSync n) = "PartialSync(" <> show n <> " drifting)"
  show ClusterDesync = "Desync"
  show ClusterEmpty = "Empty"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // reconciliation strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reconciliation strategy
data ReconciliationStrategy
  = NoReconciliation            -- All in sync
  | CatchUp                     -- Slow viewports catch up
  | SlowDown                    -- Fast viewports slow down
  | MeetInMiddle                -- Both adjust
  | ForceResync                 -- All jump to authority frame

derive instance eqReconciliationStrategy :: Eq ReconciliationStrategy

instance showReconciliationStrategy :: Show ReconciliationStrategy where
  show NoReconciliation = "NoReconciliation"
  show CatchUp = "CatchUp"
  show SlowDown = "SlowDown"
  show MeetInMiddle = "MeetInMiddle"
  show ForceResync = "ForceResync"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drift compensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drift compensation action
data DriftCompensation
  = NoCompensation              -- Within tolerance
  | SkipFrames Int              -- Skip N frames to catch up
  | InterpolateFrames Number    -- Interpolate between frames
  | PauseAndWait FrameTime      -- Pause for N ms
  | HardResync FrameNumber      -- Jump to frame immediately

derive instance eqDriftCompensation :: Eq DriftCompensation

instance showDriftCompensation :: Show DriftCompensation where
  show NoCompensation = "NoCompensation"
  show (SkipFrames n) = "SkipFrames(" <> show n <> ")"
  show (InterpolateFrames t) = "InterpolateFrames(" <> show t <> ")"
  show (PauseAndWait ms) = "PauseAndWait(" <> show ms <> "ms)"
  show (HardResync frame) = "HardResync(" <> show frame <> ")"
