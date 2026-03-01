-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // gpu // framestate // performance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Performance — Frame Budgeting and Metrics
-- |
-- | ## Purpose
-- |
-- | Tracks performance metrics for frame budgeting:
-- |
-- | - **Target FPS**: Desired frame rate (60, 120, etc.)
-- | - **Actual FPS**: Measured frame rate from delta time
-- | - **GPU Budget**: Time allocated for GPU work per frame
-- | - **GPU Used**: Actual GPU time consumed
-- | - **CPU Budget**: Time allocated for CPU work per frame
-- | - **CPU Used**: Actual CPU time consumed
-- | - **Frame Drops**: Count and timing of dropped frames
-- |
-- | ## Budget Allocation
-- |
-- | Default allocation splits the frame budget:
-- |
-- | - 80% GPU (rendering, shaders, texture uploads)
-- | - 20% CPU (state updates, event handling, garbage collection)
-- |
-- | At 60 FPS (16.67ms budget):
-- | - GPU: ~13.3ms
-- | - CPU: ~3.3ms
-- |
-- | ## Why Track Performance?
-- |
-- | At billion-agent scale, performance awareness enables:
-- |
-- | - Adaptive quality (reduce detail when behind budget)
-- | - Predictive scheduling (defer expensive work when budget is tight)
-- | - Telemetry for optimization (identify slow paths across swarm)

module Hydrogen.GPU.FrameState.Performance
  ( -- * Performance State
    PerformanceState
  , mkPerformanceState
  
  -- * Accessors
  , targetFPS
  , actualFPS
  , gpuBudgetMs
  , gpuUsedMs
  , frameDropped
  
  -- * Re-export FrameTime for budget calculations
  , module Types
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (/)
  , (*)
  , (>)
  )

import Hydrogen.GPU.FrameState.Types (FrameTime) as Types
import Hydrogen.GPU.FrameState.Types (FrameTime)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // performance state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Performance metrics for frame budgeting
-- |
-- | All times are in milliseconds. Budget is computed from target FPS.
type PerformanceState =
  { targetFPS :: Number        -- Target frame rate
  , actualFPS :: Number        -- Measured frame rate
  , gpuBudgetMs :: Number      -- GPU time budget per frame
  , gpuUsedMs :: Number        -- GPU time used this frame
  , cpuBudgetMs :: Number      -- CPU time budget per frame
  , cpuUsedMs :: Number        -- CPU time used this frame
  , droppedFrames :: Int       -- Count of dropped frames
  , lastDropTime :: FrameTime  -- Time of last frame drop
  }

-- | Create performance state from target FPS
-- |
-- | Allocates 80% of budget to GPU, 20% to CPU.
-- | Initial state assumes no time used yet.
mkPerformanceState :: Number -> PerformanceState
mkPerformanceState targetFrameRate =
  let budgetMs = 1000.0 / targetFrameRate
  in
    { targetFPS: targetFrameRate
    , actualFPS: targetFrameRate
    , gpuBudgetMs: budgetMs * 0.8
    , gpuUsedMs: 0.0
    , cpuBudgetMs: budgetMs * 0.2
    , cpuUsedMs: 0.0
    , droppedFrames: 0
    , lastDropTime: 0.0
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get target FPS
-- |
-- | The desired frame rate. Actual FPS may be lower if budget is exceeded.
targetFPS :: PerformanceState -> Number
targetFPS state = state.targetFPS

-- | Get actual measured FPS
-- |
-- | Computed from delta time. May fluctuate frame-to-frame.
actualFPS :: PerformanceState -> Number
actualFPS state = state.actualFPS

-- | Get GPU budget in milliseconds
-- |
-- | Maximum time allowed for GPU work before frame is late.
gpuBudgetMs :: PerformanceState -> Number
gpuBudgetMs state = state.gpuBudgetMs

-- | Get GPU time used in milliseconds
-- |
-- | Actual time spent on GPU work this frame.
gpuUsedMs :: PerformanceState -> Number
gpuUsedMs state = state.gpuUsedMs

-- | Check if last frame was dropped
-- |
-- | True if GPU time exceeded budget.
frameDropped :: PerformanceState -> Boolean
frameDropped state = state.gpuUsedMs > state.gpuBudgetMs
