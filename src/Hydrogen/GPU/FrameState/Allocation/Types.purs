-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // gpu // allocation // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Allocation.Types — Core type definitions for viewport allocation.
-- |
-- | ## Purpose
-- |
-- | Defines the fundamental types used across the allocation system:
-- | - AllocationState: tracking state across frames
-- | - AllocationResult: output of allocation decisions
-- | - FAAAllocationConfig: configuration for FAA-enhanced allocation
-- |
-- | ## Design Notes
-- |
-- | Types are kept separate to enable clean imports and avoid circular
-- | dependencies between allocation modules.

module Hydrogen.GPU.FrameState.Allocation.Types
  ( -- * Allocation State
    AllocationState
  , mkAllocationStateRaw
  , allocationEpoch
  , allocationRegions
  , allocationGridLevel
  , updateAllocationState
  
  -- * Allocation Result
  , AllocationResult
  
  -- * FAA Configuration
  , FAAAllocationConfig(FAAAllocationConfig)
  , mkFAAAllocationConfig
  , faaTargetIterations
  , faaMaxRegions
  , faaRoundingCandidates
  , faaQualityWeight
  , faaCoverageWeight
  , faaSeed
  
  -- * Utility Types
  , RegionIndex
  , Tuple(Tuple)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- Render.Online types
import Hydrogen.Render.Online.Core
  ( GridLevel(Coarse, Medium, Fine)
  , Region
  , RegionSelection
  , EpochId(EpochId)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // allocation // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for allocation across frames.
-- |
-- | Tracks current epoch and cached region grid.
type AllocationState =
  { epoch :: EpochId
  , regions :: Array Region
  , gridLevel :: GridLevel
  }

-- | Create allocation state from raw components.
-- |
-- | This is the low-level constructor. For most use cases, use
-- | `mkAllocationState` from the Regions module which takes a ViewportState.
mkAllocationStateRaw :: EpochId -> Array Region -> GridLevel -> AllocationState
mkAllocationStateRaw epoch regions gridLevel =
  { epoch
  , regions
  , gridLevel
  }

-- | Get current epoch.
allocationEpoch :: AllocationState -> EpochId
allocationEpoch state = state.epoch

-- | Get cached regions.
allocationRegions :: AllocationState -> Array Region
allocationRegions state = state.regions

-- | Get current grid level.
allocationGridLevel :: AllocationState -> GridLevel
allocationGridLevel state = state.gridLevel

-- | Update allocation state with new values.
updateAllocationState 
  :: EpochId 
  -> Array Region 
  -> GridLevel 
  -> AllocationState 
  -> AllocationState
updateAllocationState epoch regions gridLevel _ =
  { epoch
  , regions
  , gridLevel
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // allocation // result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of allocating a frame.
type AllocationResult =
  { selections :: Array RegionSelection
  , nextState :: AllocationState
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // faa // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index type for mapping between Regions and submodular Elements.
-- |
-- | Regions are identified by position in the region array.
type RegionIndex = Int

-- | Configuration for FAA-enhanced allocation.
-- |
-- | ## Theoretical Foundation
-- |
-- | Uses FAA (Floquet Adiabatic Algorithm) for √T speedup over standard
-- | continuous greedy, then min-energy rounding for noise-resilient
-- | discretization.
-- |
-- | ## Parameters
-- |
-- | - `targetIterations`: Controls precision (actual iterations = √targetIterations)
-- | - `maxRegions`: Maximum regions to select (cardinality constraint k)
-- | - `roundingCandidates`: Number of rounding candidates for min-energy selection
-- | - `qualityWeight`: Weight for quality-based utility
-- | - `coverageWeight`: Weight for spatial coverage utility
-- |
-- | ## Proven Properties (FAA.lean, ContinuousGreedy.lean)
-- |
-- | - Achieves (1 - 1/e - O(1/√T)) approximation
-- | - In √T iterations instead of T
-- | - Min-energy rounding is deterministic and noise-resilient
newtype FAAAllocationConfig = FAAAllocationConfig
  { targetIterations :: Int      -- ^ T: precision target (actual = √T iterations)
  , maxRegions :: Int            -- ^ k: cardinality constraint
  , roundingCandidates :: Int    -- ^ Number of rounding candidates
  , qualityWeight :: Number      -- ^ Weight for quality utility
  , coverageWeight :: Number     -- ^ Weight for coverage utility
  , seed :: Number               -- ^ Random seed for reproducibility
  }

derive instance eqFAAAllocationConfig :: Eq FAAAllocationConfig

instance showFAAAllocationConfig :: Show FAAAllocationConfig where
  show (FAAAllocationConfig c) = 
    "FAAConfig{T=" <> show c.targetIterations <> 
    ",k=" <> show c.maxRegions <> "}"

-- | Create FAA allocation config with sensible defaults.
-- |
-- | ## Real-Time Defaults (60fps target)
-- |
-- | - targetIterations: 100 → √100 = 10 actual iterations
-- | - roundingCandidates: 20 → fast min-energy selection
-- | - qualityWeight: 0.7 → prioritize render quality
-- | - coverageWeight: 0.3 → secondary coverage objective
mkFAAAllocationConfig :: Int -> Int -> FAAAllocationConfig
mkFAAAllocationConfig maxRegions targetIterations = FAAAllocationConfig
  { targetIterations
  , maxRegions
  , roundingCandidates: 20
  , qualityWeight: 0.7
  , coverageWeight: 0.3
  , seed: 42.0
  }

-- | Get target iterations from config.
faaTargetIterations :: FAAAllocationConfig -> Int
faaTargetIterations (FAAAllocationConfig c) = c.targetIterations

-- | Get max regions from config.
faaMaxRegions :: FAAAllocationConfig -> Int
faaMaxRegions (FAAAllocationConfig c) = c.maxRegions

-- | Get rounding candidates from config.
faaRoundingCandidates :: FAAAllocationConfig -> Int
faaRoundingCandidates (FAAAllocationConfig c) = c.roundingCandidates

-- | Get quality weight from config.
faaQualityWeight :: FAAAllocationConfig -> Number
faaQualityWeight (FAAAllocationConfig c) = c.qualityWeight

-- | Get coverage weight from config.
faaCoverageWeight :: FAAAllocationConfig -> Number
faaCoverageWeight (FAAAllocationConfig c) = c.coverageWeight

-- | Get seed from config.
faaSeed :: FAAAllocationConfig -> Number
faaSeed (FAAAllocationConfig c) = c.seed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // utility // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tuple type for indexed mapping.
-- |
-- | Used to pair indices with values during FAA allocation.
data Tuple a b = Tuple a b
