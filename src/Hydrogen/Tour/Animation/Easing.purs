-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // tour // animation // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing Curve Functions
-- |
-- | This module provides functions for creating and converting easing curves.
-- | Easing curves control the rate of change of animations over time.
-- |
-- | ## Supported Curves
-- |
-- | - Linear: Constant velocity
-- | - Quadratic: Smooth acceleration/deceleration
-- | - Cubic: More pronounced acceleration/deceleration
-- | - Quartic: Even more pronounced
-- | - Exponential: Very sharp acceleration/deceleration
-- | - Back: Overshoot effects

module Hydrogen.Tour.Animation.Easing
  ( -- * Construction
    cubicBezier
  , easingPreset
    -- * Conversion
  , easingToCss
    -- * Re-exports
  , module Types
  ) where

import Prelude
  ( otherwise
  , show
  , (<)
  , (<>)
  , (>)
  )

import Hydrogen.Tour.Animation.Types
  ( EasingCurve(Preset, CubicBezier)
  , EasingPreset
    ( EaseLinear
    , EaseIn
    , EaseOut
    , EaseInOut
    , EaseInQuad
    , EaseOutQuad
    , EaseInOutQuad
    , EaseInCubic
    , EaseOutCubic
    , EaseInOutCubic
    , EaseInQuart
    , EaseOutQuart
    , EaseInOutQuart
    , EaseInExpo
    , EaseOutExpo
    , EaseInOutExpo
    , EaseInBack
    , EaseOutBack
    , EaseInOutBack
    )
  ) as Types

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a custom cubic-bezier easing
-- |
-- | Clamps x values to [0, 1] range. y values can exceed for overshoot.
cubicBezier :: Number -> Number -> Number -> Number -> Types.EasingCurve
cubicBezier x1 y1 x2 y2 = Types.CubicBezier (clamp01 x1) y1 (clamp01 x2) y2
  where
  clamp01 :: Number -> Number
  clamp01 n
    | n < 0.0 = 0.0
    | n > 1.0 = 1.0
    | otherwise = n

-- | Create easing from preset
easingPreset :: Types.EasingPreset -> Types.EasingCurve
easingPreset = Types.Preset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert easing to CSS timing function
easingToCss :: Types.EasingCurve -> String
easingToCss = case _ of
  Types.Preset Types.EaseLinear -> "linear"
  Types.Preset Types.EaseIn -> "ease-in"
  Types.Preset Types.EaseOut -> "ease-out"
  Types.Preset Types.EaseInOut -> "ease-in-out"
  Types.Preset Types.EaseInQuad -> "cubic-bezier(0.55, 0.085, 0.68, 0.53)"
  Types.Preset Types.EaseOutQuad -> "cubic-bezier(0.25, 0.46, 0.45, 0.94)"
  Types.Preset Types.EaseInOutQuad -> "cubic-bezier(0.455, 0.03, 0.515, 0.955)"
  Types.Preset Types.EaseInCubic -> "cubic-bezier(0.55, 0.055, 0.675, 0.19)"
  Types.Preset Types.EaseOutCubic -> "cubic-bezier(0.215, 0.61, 0.355, 1)"
  Types.Preset Types.EaseInOutCubic -> "cubic-bezier(0.645, 0.045, 0.355, 1)"
  Types.Preset Types.EaseInQuart -> "cubic-bezier(0.895, 0.03, 0.685, 0.22)"
  Types.Preset Types.EaseOutQuart -> "cubic-bezier(0.165, 0.84, 0.44, 1)"
  Types.Preset Types.EaseInOutQuart -> "cubic-bezier(0.77, 0, 0.175, 1)"
  Types.Preset Types.EaseInExpo -> "cubic-bezier(0.95, 0.05, 0.795, 0.035)"
  Types.Preset Types.EaseOutExpo -> "cubic-bezier(0.19, 1, 0.22, 1)"
  Types.Preset Types.EaseInOutExpo -> "cubic-bezier(1, 0, 0, 1)"
  Types.Preset Types.EaseInBack -> "cubic-bezier(0.6, -0.28, 0.735, 0.045)"
  Types.Preset Types.EaseOutBack -> "cubic-bezier(0.175, 0.885, 0.32, 1.275)"
  Types.Preset Types.EaseInOutBack -> "cubic-bezier(0.68, -0.55, 0.265, 1.55)"
  Types.CubicBezier x1 y1 x2 y2 ->
    "cubic-bezier(" <> show x1 <> ", " <> show y1 <> ", " <> show x2 <> ", " <> show y2 <> ")"
