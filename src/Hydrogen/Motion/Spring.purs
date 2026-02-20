-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // spring
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spring physics animations
-- |
-- | Physics-based spring animation calculations.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Motion.Spring as Spring
-- |
-- | -- Create a spring config
-- | let spring = Spring.springConfig 170.0 26.0  -- stiffness, damping
-- |
-- | -- Preset springs
-- | Spring.springDefault
-- | Spring.springGentle
-- | Spring.springWobbly
-- | Spring.springStiff
-- |
-- | -- Calculate spring value at time t
-- | Spring.springValue spring 0.0 1.0 0.5  -- from, to, progress
-- | ```
module Hydrogen.Motion.Spring
  ( -- * Spring Configuration
    SpringConfig
  , springConfig
    -- * Presets
  , springDefault
  , springGentle
  , springWobbly
  , springStiff
  , springSlow
  , springMolasses
    -- * Spring Calculation
  , springValue
  , springVelocity
  , isAtRest
    -- * CSS Spring
  , springToCubicBezier
  ) where

import Prelude

import Data.Number (sqrt, exp, cos, sin, abs)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // spring configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spring configuration
-- |
-- | - stiffness: Spring constant (higher = faster)
-- | - damping: Resistance (higher = less bouncy)
-- | - mass: Inertia (higher = slower)
-- | - velocity: Initial velocity
type SpringConfig =
  { stiffness :: Number
  , damping :: Number
  , mass :: Number
  , velocity :: Number
  , precision :: Number  -- Threshold for considering spring at rest
  }

-- | Create a spring configuration
springConfig :: Number -> Number -> SpringConfig
springConfig stiffness damping =
  { stiffness
  , damping
  , mass: 1.0
  , velocity: 0.0
  , precision: 0.01
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default spring (balanced)
springDefault :: SpringConfig
springDefault = springConfig 170.0 26.0

-- | Gentle spring (smooth, no bounce)
springGentle :: SpringConfig
springGentle = springConfig 120.0 14.0

-- | Wobbly spring (bouncy)
springWobbly :: SpringConfig
springWobbly = springConfig 180.0 12.0

-- | Stiff spring (fast, minimal bounce)
springStiff :: SpringConfig
springStiff = springConfig 210.0 20.0

-- | Slow spring (gradual)
springSlow :: SpringConfig
springSlow = springConfig 280.0 60.0

-- | Molasses (very slow, heavy)
springMolasses :: SpringConfig
springMolasses = springConfig 280.0 120.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // spring calculation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate spring value at time t (0 to 1)
-- |
-- | Uses damped harmonic oscillator equation.
springValue :: SpringConfig -> Number -> Number -> Number -> Number
springValue config from to t =
  let
    delta = to - from
    dampingRatio = config.damping / (2.0 * sqrt (config.stiffness * config.mass))
    angularFreq = sqrt (config.stiffness / config.mass)
    
    -- Underdamped (bouncy) case
    dampedFreq = angularFreq * sqrt (1.0 - dampingRatio * dampingRatio)
    
    -- Exponential decay
    expDecay = exp (- dampingRatio * angularFreq * t)
    
    -- Oscillation
    oscillation = cos (dampedFreq * t) + 
                  (dampingRatio * angularFreq / dampedFreq) * sin (dampedFreq * t)
  in
    if dampingRatio >= 1.0
      -- Critically damped or overdamped
      then to - delta * expDecay * (1.0 + angularFreq * t)
      -- Underdamped (bouncy)
      else to - delta * expDecay * oscillation

-- | Calculate spring velocity at time t
springVelocity :: SpringConfig -> Number -> Number -> Number -> Number
springVelocity config from to t =
  let
    delta = to - from
    dampingRatio = config.damping / (2.0 * sqrt (config.stiffness * config.mass))
    angularFreq = sqrt (config.stiffness / config.mass)
    dampedFreq = angularFreq * sqrt (1.0 - dampingRatio * dampingRatio)
    expDecay = exp (- dampingRatio * angularFreq * t)
  in
    if dampingRatio >= 1.0
      then delta * angularFreq * angularFreq * t * expDecay
      else delta * expDecay * dampedFreq * sin (dampedFreq * t)

-- | Check if spring is at rest (within precision threshold)
isAtRest :: SpringConfig -> Number -> Number -> Number -> Boolean
isAtRest config from to t =
  let
    currentValue = springValue config from to t
    currentVelocity = springVelocity config from to t
  in
    abs (currentValue - to) < config.precision && 
    abs currentVelocity < config.precision

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // css spring
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Approximate spring as cubic-bezier for CSS transitions
-- |
-- | Note: This is an approximation - true spring physics requires JS.
springToCubicBezier :: SpringConfig -> String
springToCubicBezier config =
  let
    dampingRatio = config.damping / (2.0 * sqrt (config.stiffness * config.mass))
    -- Approximate cubic bezier values based on damping
    x1 = 0.25
    y1 = if dampingRatio < 0.5 then 0.1 else 0.25
    x2 = 0.25
    y2 = if dampingRatio < 0.5 then 1.5 else 1.0
  in
    "cubic-bezier(" <> show x1 <> ", " <> show y1 <> ", " <> show x2 <> ", " <> show y2 <> ")"
