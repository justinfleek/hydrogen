-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // distributed // viewport-sync
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ViewportSync — Multi-viewport coordination for distributed rendering.
-- |
-- | ## Purpose
-- |
-- | When multiple viewports render the same scene (collaborative editing,
-- | multi-monitor displays, distributed rendering farms), they must:
-- |
-- | - Agree on the current frame
-- | - Compensate for drift between local clocks
-- | - Share effect state (animations, transitions)
-- | - Handle disconnection gracefully
-- |
-- | ## Architecture
-- |
-- | Each viewport has a ViewportSync state that tracks:
-- |
-- | 1. Which time authority it follows
-- | 2. How many frames ahead/behind the authority it is
-- | 3. Current sync state (synchronized, drifting, resynchronizing, disconnected)
-- | 4. Subscriptions to shared effects
-- |
-- | ## Drift Compensation
-- |
-- | Drift occurs when:
-- | - Local clock runs faster/slower than authority
-- | - Network latency varies
-- | - Frame drops cause desync
-- |
-- | Compensation strategies:
-- | - Skip frames to catch up
-- | - Interpolate to smooth transitions
-- | - Pause and wait for authority
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `ViewportSync.Types` — Core type definitions
-- | - `ViewportSync.Core` — ViewportSync record and operations
-- | - `ViewportSync.Drift` — Drift compensation
-- | - `ViewportSync.Effects` — Shared effect state
-- | - `ViewportSync.Cluster` — Multi-viewport coordination
-- | - `ViewportSync.Reconciliation` — Frame reconciliation
-- | - `ViewportSync.Integration` — TimeAuthority subsystem integration

module Hydrogen.Distributed.ViewportSync
  ( module Types
  , module Core
  , module Drift
  , module Effects
  , module Cluster
  , module Reconciliation
  , module Integration
  ) where

import Hydrogen.Distributed.ViewportSync.Types
  ( ViewportId
  , EffectId
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
  , isSynchronized
  , isDrifting
  , isResynchronizing
  , isDisconnected
  , EffectPhase
      ( EffectIdle
      , EffectRunning
      , EffectComplete
      , EffectPaused
      )
  , ClusterState
      ( ClusterSynced
      , ClusterPartialSync
      , ClusterDesync
      , ClusterEmpty
      )
  , ReconciliationStrategy
      ( NoReconciliation
      , CatchUp
      , SlowDown
      , MeetInMiddle
      , ForceResync
      )
  , DriftCompensation
      ( NoCompensation
      , SkipFrames
      , InterpolateFrames
      , PauseAndWait
      , HardResync
      )
  ) as Types

import Hydrogen.Distributed.ViewportSync.Core
  ( ViewportSync
  , mkViewportSync
  , updateSyncState
  , setFrameOffset
  , recordDrift
  , markSynchronized
  , markDisconnected
  , getSyncQuality
  , clamp01
  , minInt
  , maxInt
  , absInt
  ) as Core

import Hydrogen.Distributed.ViewportSync.Drift
  ( DriftThresholds
  , defaultDriftThresholds
  , computeCompensation
  , applyCompensation
  ) as Drift

import Hydrogen.Distributed.ViewportSync.Effects
  ( SharedEffectState
  , mkSharedEffect
  , subscribeViewport
  , unsubscribeViewport
  , updateEffectPhase
  , isEffectOwner
  , getSubscribers
  , EffectRegistry
  , mkEffectRegistry
  , registerEffect
  , unregisterEffect
  , getEffect
  , getEffectsForViewport
  , tickEffects
  ) as Effects

import Hydrogen.Distributed.ViewportSync.Cluster
  ( ViewportCluster
  , mkViewportCluster
  , addViewport
  , removeViewport
  , getViewport
  , getAllViewports
  , broadcastFrame
  , computeClusterState
  ) as Cluster

import Hydrogen.Distributed.ViewportSync.Reconciliation
  ( FrameReconciliation
  , reconcileFrames
  , applyReconciliation
  ) as Reconciliation

import Hydrogen.Distributed.ViewportSync.Integration
  ( mkViewportSyncLocal
  , mkViewportSyncNetwork
  , viewportUsesNetwork
  , viewportUsesLocal
  , getViewportAuthorityTime
  , computeExpectedFrame
  , computeNextFrameTime
  , viewportIsBehind
  , viewportIsAhead
  , getScheduleFps
  , getScheduleFrameDuration
  , mkViewportSyncWithClockSync
  , syncQualityToNumber
  , viewportMeetsSyncQuality
  , viewportLocalToServer
  , viewportServerToLocal
  , ViewportSyncWithCausality
  , mkViewportSyncWithCausality
  , tickCausality
  , receiveCausality
  , checkCausalOrder
  , areConcurrent
  ) as Integration
