-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geometry // bezier // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bezier Easing — Common animation easing curves.
-- |
-- | ## Overview
-- |
-- | This module provides pre-defined cubic Bezier curves that correspond to
-- | common CSS easing functions. These curves define how an animation
-- | progresses over time.
-- |
-- | ## CSS Compatibility
-- |
-- | Each curve includes its CSS cubic-bezier() equivalent in the documentation.
-- | The curves are defined in normalized [0,1] space where:
-- | - X axis = time (input)
-- | - Y axis = progress (output)
-- |
-- | ## Easing Families
-- |
-- | - **Linear**: No acceleration, constant speed
-- | - **Quad**: Quadratic acceleration (smooth, natural)
-- | - **Cubic**: Cubic acceleration (more pronounced than quad)
-- |
-- | ## Use Cases
-- |
-- | - UI transitions and animations
-- | - State interpolation over time
-- | - Motion design for agent interfaces

module Hydrogen.Schema.Geometry.Bezier.Easing
  ( -- * Linear
    easeLinear
    
  -- * Quadratic
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  
  -- * Cubic
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Geometry.Point (point2D)

import Hydrogen.Schema.Geometry.Bezier.Types
  ( CubicBezier
  , cubicBezier
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // linear
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear easing (no acceleration).
-- |
-- | CSS: cubic-bezier(0.0, 0.0, 1.0, 1.0)
easeLinear :: CubicBezier
easeLinear = cubicBezier 
  (point2D 0.0 0.0) 
  (point2D 0.0 0.0) 
  (point2D 1.0 1.0) 
  (point2D 1.0 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // quadratic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ease-in quadratic (slow start).
-- |
-- | CSS: cubic-bezier(0.55, 0.085, 0.68, 0.53)
easeInQuad :: CubicBezier
easeInQuad = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.55 0.085)
  (point2D 0.68 0.53)
  (point2D 1.0 1.0)

-- | Ease-out quadratic (slow end).
-- |
-- | CSS: cubic-bezier(0.25, 0.46, 0.45, 0.94)
easeOutQuad :: CubicBezier
easeOutQuad = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.25 0.46)
  (point2D 0.45 0.94)
  (point2D 1.0 1.0)

-- | Ease-in-out quadratic (slow start and end).
-- |
-- | CSS: cubic-bezier(0.455, 0.03, 0.515, 0.955)
easeInOutQuad :: CubicBezier
easeInOutQuad = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.455 0.03)
  (point2D 0.515 0.955)
  (point2D 1.0 1.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // cubic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ease-in cubic (slower start than quadratic).
-- |
-- | CSS: cubic-bezier(0.55, 0.055, 0.675, 0.19)
easeInCubic :: CubicBezier
easeInCubic = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.55 0.055)
  (point2D 0.675 0.19)
  (point2D 1.0 1.0)

-- | Ease-out cubic (slower end than quadratic).
-- |
-- | CSS: cubic-bezier(0.215, 0.61, 0.355, 1.0)
easeOutCubic :: CubicBezier
easeOutCubic = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.215 0.61)
  (point2D 0.355 1.0)
  (point2D 1.0 1.0)

-- | Ease-in-out cubic (slower start and end than quadratic).
-- |
-- | CSS: cubic-bezier(0.645, 0.045, 0.355, 1.0)
easeInOutCubic :: CubicBezier
easeInOutCubic = cubicBezier
  (point2D 0.0 0.0)
  (point2D 0.645 0.045)
  (point2D 0.355 1.0)
  (point2D 1.0 1.0)
