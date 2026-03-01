-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // framestate // allocation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FrameState.Allocation — Viewport Allocation via Submodular Optimization
-- |
-- | ## Purpose
-- |
-- | This module bridges GPU FrameState infrastructure with submodular optimization,
-- | enabling intelligent allocation of rendering resources across viewport regions.
-- |
-- | ## Integration Points
-- |
-- | - ViewportState → GroundSet Region (map latent grid to optimization elements)
-- | - PerformanceState → UtilityFeedback (convert GPU timing to learning signal)
-- | - OnlineState → RegionSelection[] (output allocation decisions)
-- |
-- | ## Architecture
-- |
-- | ```
-- | ViewportTensor (latent grid)
-- |        ↓
-- | viewportToGroundSet
-- |        ↓
-- | GroundSet Region
-- |        ↓
-- | onlineStep (from Optimize.Submodular.Online)
-- |        ↓
-- | RegionSelection[]
-- |        ↓
-- | GPU Render (external)
-- |        ↓
-- | performanceToFeedback
-- |        ↓
-- | UtilityFeedback
-- |        ↓
-- | onlineStep (next frame)
-- | ```
-- |
-- | ## Council Decision (2026-02-25)
-- |
-- | This module implements P0 from the FAA Council Deliberation:
-- | "Integration before optimization" — wire existing infrastructure before
-- | adding algorithmic enhancements.
-- |
-- | ## Submodules
-- |
-- | - Types: Core type definitions (AllocationState, FAAAllocationConfig)
-- | - Regions: Region generation and spatial queries
-- | - Performance: Performance feedback and quality computation
-- | - Strategy: Frame allocation algorithms (basic and FAA-enhanced)

module Hydrogen.GPU.FrameState.Allocation
  ( module Types
  , module Regions
  , module Performance
  , module Strategy
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.GPU.FrameState.Allocation.Types as Types
import Hydrogen.GPU.FrameState.Allocation.Regions as Regions
import Hydrogen.GPU.FrameState.Allocation.Performance as Performance
import Hydrogen.GPU.FrameState.Allocation.Strategy as Strategy
