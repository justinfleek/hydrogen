-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // temporal // easing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Easing — Compound type unifying all easing function varieties.
-- |
-- | ## Easing Function Types
-- |
-- | An easing function maps normalized time [0,1] to normalized progress [0,1].
-- | Different types of easing serve different purposes:
-- |
-- | - **Linear**: Constant velocity, no acceleration
-- | - **CubicBezier**: Smooth acceleration curves (CSS standard)
-- | - **Steps**: Discrete jumps (sprite animation, typewriter)
-- | - **Spring**: Physics-based (natural, responsive feel)
-- |
-- | ## Usage
-- |
-- | The Easing type allows any animation system to accept any easing approach,
-- | providing a unified interface for the runtime to interpret.

module Hydrogen.Schema.Temporal.Easing
  ( Easing(..)
  
  -- * Smart Constructors
  , linearEasing
  , cubicEasing
  , stepsEasing
  , springEasing
  
  -- * Standard Presets
  , ease
  , easeIn
  , easeOut
  , easeInOut
  
  -- * Category Check
  , isLinear
  , isCubicBezier
  , isSteps
  , isSpring
  
  -- * CSS Export
  , toLegacyCss
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Temporal.CubicBezierEasing 
  ( CubicBezierEasing
  , toLegacyCss
  , linear
  , ease
  , easeIn
  , easeOut
  , easeInOut
  ) as Bezier

import Hydrogen.Schema.Temporal.StepEasing 
  ( Steps
  , StepPosition
  , unwrapSteps
  , stepPositionToString
  ) as Step

import Hydrogen.Schema.Temporal.SpringConfig 
  ( SpringConfig
  ) as Spring

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // easing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unified easing function type
-- |
-- | Represents any timing function that can be used for animation.
data Easing
  = Linear
  | CubicBezier Bezier.CubicBezierEasing
  | Steps Step.Steps Step.StepPosition
  | Spring Spring.SpringConfig

derive instance eqEasing :: Eq Easing
derive instance ordEasing :: Ord Easing

instance showEasing :: Show Easing where
  show Linear = "Linear"
  show (CubicBezier cb) = "(CubicBezier " <> show cb <> ")"
  show (Steps n pos) = "(Steps " <> show n <> " " <> show pos <> ")"
  show (Spring cfg) = "(Spring " <> show cfg <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // smart constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create linear easing (constant velocity)
linearEasing :: Easing
linearEasing = Linear

-- | Create cubic bezier easing from configuration
cubicEasing :: Bezier.CubicBezierEasing -> Easing
cubicEasing = CubicBezier

-- | Create stepped easing from count and position
stepsEasing :: Step.Steps -> Step.StepPosition -> Easing
stepsEasing = Steps

-- | Create spring-based easing from configuration
springEasing :: Spring.SpringConfig -> Easing
springEasing = Spring

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // standard presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS ease: gentle acceleration and deceleration
ease :: Easing
ease = CubicBezier Bezier.ease

-- | CSS ease-in: slow start
easeIn :: Easing
easeIn = CubicBezier Bezier.easeIn

-- | CSS ease-out: slow end
easeOut :: Easing
easeOut = CubicBezier Bezier.easeOut

-- | CSS ease-in-out: slow start and end
easeInOut :: Easing
easeInOut = CubicBezier Bezier.easeInOut

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // category check
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if easing is linear
isLinear :: Easing -> Boolean
isLinear Linear = true
isLinear _ = false

-- | Check if easing is cubic bezier
isCubicBezier :: Easing -> Boolean
isCubicBezier (CubicBezier _) = true
isCubicBezier _ = false

-- | Check if easing is steps
isSteps :: Easing -> Boolean
isSteps (Steps _ _) = true
isSteps _ = false

-- | Check if easing is spring-based
isSpring :: Easing -> Boolean
isSpring (Spring _) = true
isSpring _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // css export
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Format for CSS for legacy system interop.
-- |
-- | **NOTE:** Hydrogen renders via WebGPU, NOT CSS. This function exists only
-- | for exporting to legacy systems that require CSS format.
-- |
-- | Spring easing cannot be represented in CSS — falls back to ease-out.
toLegacyCss :: Easing -> String
toLegacyCss Linear = "linear"
toLegacyCss (CubicBezier cb) = Bezier.toLegacyCss cb
toLegacyCss (Steps n pos) = 
  "steps(" <> show (Step.unwrapSteps n) <> ", " <> Step.stepPositionToString pos <> ")"
toLegacyCss (Spring _) = 
  -- Spring physics cannot be represented in CSS
  -- Fall back to ease-out as closest approximation
  "ease-out"
