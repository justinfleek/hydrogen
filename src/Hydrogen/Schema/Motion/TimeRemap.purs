-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // time-remap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimeRemap — Variable speed, time remapping, and ramps for animation.
-- |
-- | ## Design Philosophy
-- |
-- | Time remapping allows non-linear playback of animations:
-- |
-- | - **Speed curves**: Gradual acceleration/deceleration
-- | - **Time freeze**: Hold at specific frame
-- | - **Time reverse**: Play backwards
-- | - **Time stretch**: Slow motion or fast forward
-- | - **Ramps**: Gradual speed transitions
-- |
-- | This mirrors motion graphics Time Remap effect and 3D animation software's
-- | F-Curve editor with explicit time control.
-- |
-- | ## Core Concept
-- |
-- | A TimeRemap maps input time to output time:
-- |
-- | ```
-- | outputTime = remap(inputTime)
-- | ```
-- |
-- | For example:
-- | - Linear: outputTime = inputTime (normal playback)
-- | - Reverse: outputTime = totalDuration - inputTime
-- | - Slow motion: outputTime = inputTime * 0.5
-- | - Speed ramp: outputTime follows a curve
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.TimeRemap as TR
-- |
-- | -- Create slow motion (50% speed)
-- | slowMo = TR.uniformSpeed 0.5
-- |
-- | -- Create speed ramp (slow start, fast end)
-- | ramp = TR.speedRamp TR.easeIn 0.2 1.5
-- |
-- | -- Apply to animation time
-- | remappedTime = TR.apply 30.0 ramp  -- Remap frame 30
-- |
-- | -- Create freeze frame
-- | freeze = TR.freezeAt 60.0  -- Hold at frame 60
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `TimeRemap.Types` — Core types (RemapMode, SpeedKeyframe, TimeRemap)
-- | - `TimeRemap.Construction` — Constructors and speed ramps
-- | - `TimeRemap.Evaluation` — Evaluation and duration functions
-- | - `TimeRemap.Composition` — Composition, presets, analysis, sampling
-- | - `TimeRemap.Utilities` — Validation, normalization, helpers
-- | - `TimeRemap.Internal` — Internal helpers (not re-exported)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Easing (curves for speed transitions)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.TimeRemap
  ( -- * Core Types
    module Hydrogen.Schema.Motion.TimeRemap.Types
  -- * Construction
  , module Hydrogen.Schema.Motion.TimeRemap.Construction
  -- * Evaluation
  , module Hydrogen.Schema.Motion.TimeRemap.Evaluation
  -- * Composition
  , module Hydrogen.Schema.Motion.TimeRemap.Composition
  -- * Utilities
  , module Hydrogen.Schema.Motion.TimeRemap.Utilities
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Motion.TimeRemap.Types 
  ( TimeRemap(TimeRemap)
  , SpeedKeyframe(SpeedKeyframe)
  , RemapMode(LinearRemap, CurveRemap, KeyframeRemap, FreezeRemap, PingPongRemap, LoopRemap)
  )

import Hydrogen.Schema.Motion.TimeRemap.Construction
  ( identity
  , uniformSpeed
  , reverse
  , freezeAt
  , timeStretch
  , speedRamp
  , speedRampIn
  , speedRampOut
  , speedRampInOut
  , fromSpeedKeyframes
  , addSpeedKeyframe
  , removeSpeedKeyframe
  )

import Hydrogen.Schema.Motion.TimeRemap.Evaluation
  ( apply
  , applyInverse
  , applyToProgress
  , speedAt
  , derivativeAt
  , remappedDuration
  , originalDuration
  , setOriginalDuration
  )

import Hydrogen.Schema.Motion.TimeRemap.Composition
  ( compose
  , chain
  , blend
  , slowMotion
  , fastForward
  , pingPong
  , loop
  , hold
  , bounce
  , averageSpeed
  , minSpeed
  , maxSpeed
  , isConstantSpeed
  , sampleRemap
  , sampleSpeed
  )

import Hydrogen.Schema.Motion.TimeRemap.Utilities
  ( defaultSpeed
  , isValidRemap
  , normalizeRemap
  , speedKeyframe
  , combineRemaps
  , speedMagnitude
  , hasSpeedChange
  )
