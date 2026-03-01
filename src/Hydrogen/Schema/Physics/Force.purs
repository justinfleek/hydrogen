-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // physics // force
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Force — Physical force primitives for physics-based UI and animation.
-- |
-- | ## Design Philosophy
-- |
-- | Forces are the drivers of motion. In UI physics, forces create natural-feeling
-- | animations: springs pull elements to targets, drag slows motion, gravity
-- | creates weight. This module provides bounded, composable force primitives.
-- |
-- | ## Force Categories
-- |
-- | **Conservative Forces**: Path-independent, have potential energy
-- | - Gravitational: Constant downward pull
-- | - Spring/Elastic: Proportional to displacement (Hooke's law)
-- | - Electrostatic: Attraction/repulsion (UI element interactions)
-- |
-- | **Non-Conservative Forces**: Path-dependent, dissipate energy
-- | - Drag: Proportional to velocity (air resistance)
-- | - Friction: Opposes motion at contact
-- | - Damping: Viscous resistance (spring damping)
-- |
-- | ## Bounded Design
-- |
-- | Force magnitudes are bounded to prevent:
-- | - Infinite forces (division by zero in inverse-square laws)
-- | - Numerical instability in simulations
-- | - Unrealistic behavior at billion-agent scale
-- |
-- | ## Units
-- |
-- | Forces are dimensionless in UI space. The "mass" of a UI element is
-- | typically 1.0, so force equals acceleration. Physical units (Newtons)
-- | are not used; instead, forces are calibrated to produce pleasing motion.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - `Force.Types` — Core Force2D type and vector operations
-- | - `Force.Conservative` — Gravity, spring, and point forces
-- | - `Force.Dissipative` — Drag, friction, and damping forces
-- | - `Force.Fields` — Force fields and application utilities
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Number (sqrt, abs)
-- |
-- | ## Dependents
-- |
-- | - Motion.Spring (spring physics)
-- | - Component.Draggable (drag physics)
-- | - Animation.Physics (physics-based animation)

module Hydrogen.Schema.Physics.Force
  ( module Types
  , module Conservative
  , module Dissipative
  , module Fields
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // submodule re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Physics.Force.Types as Types
import Hydrogen.Schema.Physics.Force.Conservative as Conservative
import Hydrogen.Schema.Physics.Force.Dissipative as Dissipative
import Hydrogen.Schema.Physics.Force.Fields as Fields
