-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // allocation // performance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Allocation.Performance — Performance feedback and quality computation.
-- |
-- | ## Purpose
-- |
-- | Converts GPU performance metrics into feedback signals for allocation:
-- | - Quality computation from budget/usage
-- | - Utility feedback for online learning
-- | - Safe constructors for Quality and Utility types
-- |
-- | ## Design Notes
-- |
-- | Quality represents rendering headroom: how much GPU budget remains.
-- | Higher quality means more capacity for additional rendering work.
-- | This feeds into the allocation system to adapt quality dynamically.

module Hydrogen.GPU.FrameState.Allocation.Performance
  ( -- * Quality Computation
    qualityFromPerformance
  
  -- * Feedback
  , performanceToFeedback
  
  -- * Safe Constructors
  , mkQuality
  , mkUtility
  
  -- * Step Construction
  , safeSteps
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( max
  , min
  , ($)
  , (-)
  , (/)
  , (>)
  )

import Data.Maybe (Maybe)

-- FrameState types
import Hydrogen.GPU.FrameState
  ( PerformanceState
  , gpuBudgetMs
  , gpuUsedMs
  )

-- Render.Online types
import Hydrogen.Render.Online.Core
  ( RegionSelection
  , DiffusionSteps
  , mkDiffusionSteps
  , Quality(Quality)
  , Utility(Utility)
  , clampToBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // quality // computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute quality metric from performance state.
-- |
-- | Quality = (budget - used) / budget, clamped to [0, 1].
-- | Higher quality means more headroom remaining.
qualityFromPerformance :: PerformanceState -> Number
qualityFromPerformance perf =
  let
    budget = gpuBudgetMs perf
    used = gpuUsedMs perf
    raw = if budget > 0.0 then (budget - used) / budget else 0.0
  in
    max 0.0 (min 1.0 raw)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert performance metrics to utility feedback for a selection.
-- |
-- | This is the learning signal for online optimization:
-- | - High quality (lots of headroom) → can allocate more
-- | - Low quality (near budget) → should allocate less
performanceToFeedback :: PerformanceState -> RegionSelection -> Number
performanceToFeedback perf _sel =
  qualityFromPerformance perf

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // safe // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Quality value from a raw number.
-- |
-- | Quality is bounded [0, 1]. Values outside this range are clamped.
mkQuality :: Number -> Quality
mkQuality n = Quality (clampToBounds 0.0 1.0 n)

-- | Create a Utility value from a raw number.
-- |
-- | Utility is bounded [0, 1e12]. Values outside this range are clamped.
mkUtility :: Number -> Utility
mkUtility n = Utility (clampToBounds 0.0 1.0e12 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // safe // step // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safely construct DiffusionSteps with validation.
-- |
-- | Returns Nothing if steps are outside [1, 50].
-- | Prefer this over raw constructor for external input.
safeSteps :: Int -> Maybe DiffusionSteps
safeSteps = mkDiffusionSteps
