-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // framestate // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Types — Foundational type aliases for FrameState
-- |
-- | ## Purpose
-- |
-- | This module defines the primitive type aliases used throughout FrameState:
-- |
-- | - **FrameTime**: Milliseconds as Number (for sub-millisecond precision)
-- | - **FrameNumber**: Integer frame counter (monotonically increasing)
-- |
-- | These are type aliases rather than newtypes for interoperability with
-- | animation/physics code that expects raw Number/Int. The semantic meaning
-- | is enforced by naming conventions and usage patterns.
-- |
-- | ## Why Aliases, Not Newtypes?
-- |
-- | At billion-agent scale, zero-cost abstractions matter:
-- |
-- | - Type aliases compile to nothing (no runtime wrapper)
-- | - Animation math uses raw arithmetic (+, -, *, /)
-- | - Newtypes would require constant unwrap/wrap cycles
-- |
-- | The tradeoff: less type safety for better ergonomics and performance.
-- | This is acceptable because FrameTime/FrameNumber usage is localized
-- | to FrameState and animation code, not scattered across the codebase.

module Hydrogen.GPU.FrameState.Types
  ( -- * Core Type Aliases
    FrameTime
  , FrameNumber
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Time in milliseconds since epoch or app start
-- |
-- | Uses Number for sub-millisecond precision (important for smooth 120Hz+).
-- | Typical values range from 0.0 (app start) to ~10^9 (days of uptime).
-- |
-- | ## Precision Notes
-- |
-- | JavaScript Number (IEEE 754 double) provides 15-17 significant digits.
-- | At 10^9 ms (≈11 days), we still have ~6 decimal places of precision,
-- | which is more than enough for sub-frame timing calculations.
type FrameTime = Number

-- | Frame counter (monotonically increasing)
-- |
-- | Starts at 0 on app init, increments by 1 each frame.
-- | At 60 FPS, Int32 overflows after ~414 days. For longer sessions,
-- | use FrameTime (elapsed milliseconds) for duration calculations.
-- |
-- | ## Usage
-- |
-- | - Animation phasing (odd/even frames)
-- | - Debug/profiling frame identification
-- | - Deterministic replay (frame N = same state)
type FrameNumber = Int
