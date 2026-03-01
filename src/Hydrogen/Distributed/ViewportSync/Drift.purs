-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // distributed // viewport-sync // drift
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Drift compensation for viewport synchronization.
-- |
-- | When viewports drift out of sync with the time authority, this module
-- | provides strategies to bring them back into alignment:
-- |
-- | - Skip frames (catch up when behind)
-- | - Interpolate (smooth out small drifts)
-- | - Pause and wait (slow down when ahead)
-- | - Hard resync (for severe drift)

module Hydrogen.Distributed.ViewportSync.Drift
  ( -- * Thresholds
    DriftThresholds
  , defaultDriftThresholds
  
  -- * Compensation
  , computeCompensation
  , applyCompensation
  ) where

import Prelude
  ( otherwise
  , negate
  , (<)
  , (>=)
  , (>)
  , (+)
  , (/)
  , ($)
  )

import Data.Number (abs)
import Data.Int (floor)

import Hydrogen.Distributed.TimeAuthority 
  ( FrameTime
  , FrameNumber
  )

import Hydrogen.Distributed.ViewportSync.Types
  ( DriftCompensation
      ( NoCompensation
      , SkipFrames
      , InterpolateFrames
      , PauseAndWait
      , HardResync
      )
  )

import Hydrogen.Distributed.ViewportSync.Core
  ( minInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // drift compensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thresholds for drift compensation decisions
type DriftThresholds =
  { toleranceMs :: Number       -- Drift below this is ignored
  , skipThresholdMs :: Number   -- Above this, skip frames
  , hardResyncMs :: Number      -- Above this, hard resync
  , maxSkipFrames :: Int        -- Maximum frames to skip at once
  }

-- | Default drift thresholds
defaultDriftThresholds :: DriftThresholds
defaultDriftThresholds =
  { toleranceMs: 5.0
  , skipThresholdMs: 50.0
  , hardResyncMs: 500.0
  , maxSkipFrames: 5
  }

-- | Compute compensation needed for current drift
computeCompensation :: DriftThresholds -> Number -> FrameTime -> DriftCompensation
computeCompensation thresholds driftMs frameDurationMs
  | abs driftMs < thresholds.toleranceMs = NoCompensation
  | abs driftMs >= thresholds.hardResyncMs = HardResync 0  -- Caller should set frame
  | driftMs > thresholds.skipThresholdMs =
      let framesToSkip = minInt thresholds.maxSkipFrames 
                           (floor (driftMs / frameDurationMs))
      in if framesToSkip > 0 then SkipFrames framesToSkip else InterpolateFrames 1.5
  | driftMs < negate thresholds.skipThresholdMs =
      PauseAndWait (abs driftMs)
  | otherwise = 
      InterpolateFrames (1.0 + driftMs / frameDurationMs / 10.0)

-- | Apply compensation to get target frame
applyCompensation :: DriftCompensation -> FrameNumber -> FrameNumber
applyCompensation comp currentFrame = case comp of
  NoCompensation -> currentFrame
  SkipFrames n -> currentFrame + n
  InterpolateFrames _ -> currentFrame  -- Interpolation doesn't change frame
  PauseAndWait _ -> currentFrame       -- Pause doesn't change frame
  HardResync frame -> frame
