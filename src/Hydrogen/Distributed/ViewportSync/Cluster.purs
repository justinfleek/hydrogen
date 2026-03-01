-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // distributed // viewport-sync // cluster
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Multi-viewport coordination via clusters.
-- |
-- | A ViewportCluster groups multiple viewports that should stay synchronized.
-- | This module provides:
-- |
-- | - Cluster management (add/remove viewports)
-- | - Frame broadcasting across the cluster
-- | - Overall cluster state computation

module Hydrogen.Distributed.ViewportSync.Cluster
  ( -- * Viewport Cluster
    ViewportCluster
  , mkViewportCluster
  , addViewport
  , removeViewport
  , getViewport
  , getAllViewports
  , broadcastFrame
  , computeClusterState
  ) where

import Prelude
  ( map
  , (==)
  , (>)
  , (-)
  , (/)
  , ($)
  , (#)
  )

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)

import Hydrogen.Distributed.TimeAuthority 
  ( AgentId
  , FrameTime
  , FrameNumber
  )

import Hydrogen.Distributed.ViewportSync.Types
  ( ViewportId
  , ClusterState
      ( ClusterSynced
      , ClusterPartialSync
      , ClusterDesync
      , ClusterEmpty
      )
  , isSynchronized
  )

import Hydrogen.Distributed.ViewportSync.Core
  ( ViewportSync
  )

import Hydrogen.Distributed.ViewportSync.Effects
  ( EffectRegistry
  , mkEffectRegistry
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // multi-viewport coordination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cluster of synchronized viewports
type ViewportCluster =
  { viewports :: Map ViewportId ViewportSync
  , effects :: EffectRegistry
  , authorityId :: AgentId
  , currentFrame :: FrameNumber
  }

-- | Create viewport cluster
mkViewportCluster :: AgentId -> ViewportCluster
mkViewportCluster authorityId =
  { viewports: Map.empty
  , effects: mkEffectRegistry
  , authorityId
  , currentFrame: 0
  }

-- | Add viewport to cluster
addViewport :: ViewportSync -> ViewportCluster -> ViewportCluster
addViewport sync cluster = cluster
  { viewports = Map.insert sync.viewportId sync cluster.viewports }

-- | Remove viewport from cluster
removeViewport :: ViewportId -> ViewportCluster -> ViewportCluster
removeViewport viewportId cluster = cluster
  { viewports = Map.delete viewportId cluster.viewports }

-- | Get viewport by ID
getViewport :: ViewportId -> ViewportCluster -> Maybe ViewportSync
getViewport viewportId cluster = Map.lookup viewportId cluster.viewports

-- | Get all viewports
getAllViewports :: ViewportCluster -> Array ViewportSync
getAllViewports cluster = Map.values cluster.viewports # Array.fromFoldable

-- | Broadcast frame update to all viewports
broadcastFrame :: FrameNumber -> FrameTime -> ViewportCluster -> ViewportCluster
broadcastFrame frame time cluster = cluster
  { viewports = map (updateViewportFrame time) cluster.viewports
  , currentFrame = frame
  }

-- | Update viewport with new frame time
updateViewportFrame :: FrameTime -> ViewportSync -> ViewportSync
updateViewportFrame time sync = sync { lastSyncTime = time }

-- | Compute overall cluster state
computeClusterState :: ViewportCluster -> ClusterState
computeClusterState cluster =
  let
    viewports = getAllViewports cluster
    total = Array.length viewports
    synced = Array.length $ Array.filter (\v -> isSynchronized v.syncState) viewports
    drifting = total - synced
  in
    if total == 0 then ClusterEmpty
    else if synced == total then ClusterSynced
    else if synced > total / 2 then ClusterPartialSync drifting
    else ClusterDesync
