-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // distributed // viewport-sync // reconciliation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frame reconciliation across viewports.
-- |
-- | When viewports have drifted apart, reconciliation determines how to
-- | bring them back together:
-- |
-- | - CatchUp: Slow viewports speed up
-- | - SlowDown: Fast viewports slow down
-- | - MeetInMiddle: Both adjust
-- | - ForceResync: All jump to authority frame

module Hydrogen.Distributed.ViewportSync.Reconciliation
  ( -- * Frame Reconciliation
    FrameReconciliation
  , reconcileFrames
  , applyReconciliation
  ) where

import Prelude
  ( map
  , (==)
  , (>)
  , (<)
  , (-)
  , (+)
  , (/=)
  , ($)
  , (#)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map

import Hydrogen.Distributed.TimeAuthority 
  ( FrameNumber
  )

import Hydrogen.Distributed.ViewportSync.Types
  ( ViewportId
  , SyncState
      ( Synchronized
      )
  , ReconciliationStrategy
      ( NoReconciliation
      , CatchUp
      , SlowDown
      , MeetInMiddle
      , ForceResync
      )
  )

import Hydrogen.Distributed.ViewportSync.Core
  ( ViewportSync
  , minInt
  , maxInt
  , absInt
  )

import Hydrogen.Distributed.ViewportSync.Cluster
  ( ViewportCluster
  , getAllViewports
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // frame reconciliation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame reconciliation result
type FrameReconciliation =
  { targetFrame :: FrameNumber
  , strategy :: ReconciliationStrategy
  , affectedViewports :: Array ViewportId
  }

-- | Reconcile frames across viewports
reconcileFrames :: ViewportCluster -> FrameReconciliation
reconcileFrames cluster =
  let
    viewports = getAllViewports cluster
    offsets = map _.frameOffset viewports
    maxOffset = foldl maxInt 0 offsets
    minOffset = foldl minInt 0 offsets
    spread = maxOffset - minOffset
    affected = Array.filter (\v -> v.frameOffset /= 0) viewports
                 # map _.viewportId
  in
    if spread == 0 then
      { targetFrame: cluster.currentFrame
      , strategy: NoReconciliation
      , affectedViewports: []
      }
    else if spread > 10 then
      { targetFrame: cluster.currentFrame
      , strategy: ForceResync
      , affectedViewports: map _.viewportId viewports
      }
    else if absInt minOffset > absInt maxOffset then
      { targetFrame: cluster.currentFrame
      , strategy: CatchUp
      , affectedViewports: affected
      }
    else if absInt maxOffset > absInt minOffset then
      { targetFrame: cluster.currentFrame
      , strategy: SlowDown
      , affectedViewports: affected
      }
    else
      { targetFrame: cluster.currentFrame
      , strategy: MeetInMiddle
      , affectedViewports: affected
      }

-- | Apply reconciliation to cluster
applyReconciliation :: FrameReconciliation -> ViewportCluster -> ViewportCluster
applyReconciliation recon cluster = case recon.strategy of
  NoReconciliation -> cluster
  ForceResync -> cluster
    { viewports = map (\v -> v { frameOffset = 0, syncState = Synchronized }) 
                      cluster.viewports 
    }
  CatchUp -> cluster
    { viewports = map (adjustViewportOffset CatchUp) cluster.viewports }
  SlowDown -> cluster
    { viewports = map (adjustViewportOffset SlowDown) cluster.viewports }
  MeetInMiddle -> cluster
    { viewports = map (adjustViewportOffset MeetInMiddle) cluster.viewports }

-- | Adjust viewport offset based on strategy
adjustViewportOffset :: ReconciliationStrategy -> ViewportSync -> ViewportSync
adjustViewportOffset strategy sync = case strategy of
  CatchUp -> 
    if sync.frameOffset < 0 
      then sync { frameOffset = sync.frameOffset + 1 }
      else sync
  SlowDown -> 
    if sync.frameOffset > 0 
      then sync { frameOffset = sync.frameOffset - 1 }
      else sync
  MeetInMiddle -> 
    if sync.frameOffset > 0 
      then sync { frameOffset = sync.frameOffset - 1 }
      else if sync.frameOffset < 0 
        then sync { frameOffset = sync.frameOffset + 1 }
        else sync
  NoReconciliation -> sync
  ForceResync -> sync
