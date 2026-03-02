-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // physics // force // dissipative
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Dissipative forces — non-conservative forces that remove energy.
-- |
-- | ## Non-Conservative Force Categories
-- |
-- | **Drag**: Proportional to velocity (air resistance)
-- | **Friction**: Opposes motion at contact
-- | **Damping**: Viscous resistance (spring damping)
-- |
-- | Non-conservative forces are path-dependent: the work done depends on
-- | the path taken. They dissipate energy from the system, converting
-- | kinetic energy to heat or other forms.

module Hydrogen.Schema.Physics.Force.Dissipative
  ( -- * Drag Force
    DragForce(DragForce)
  , dragForce
  , dragForceLight
  , dragForceMedium
  , dragForceHeavy
  , dragForceValue
  , dragCoefficient
  
  -- * Friction Force
  , FrictionForce(FrictionForce)
  , frictionForce
  , frictionStatic
  , frictionKinetic
  , frictionIce
  , frictionRubber
  , frictionForceValue
  , staticCoefficient
  , kineticCoefficient
  
  -- * Damping Force
  , DampingForce(DampingForce)
  , dampingForce
  , dampingLight
  , dampingCritical
  , dampingHeavy
  , dampingForceValue
  , dampingCoefficient
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (*)
  , (/)
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Physics.Force.Types
  ( Force2D
  , forceMagnitude
  , forceScale
  , forceZero
  )

import Hydrogen.Schema.Physics.Force.Internal
  ( absNumber
  , clampPositive
  , clampUnit
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // drag force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drag force proportional to velocity: F = -c * v
-- |
-- | Drag opposes motion, slowing objects down. Linear drag is proportional
-- | to velocity (viscous drag). Quadratic drag (proportional to v²) is
-- | used for high-speed aerodynamic drag but linear is simpler for UI.
newtype DragForce = DragForce
  { coefficient :: Number  -- ^ Drag coefficient (bounded 0-100)
  }

derive instance eqDragForce :: Eq DragForce
derive instance ordDragForce :: Ord DragForce

instance showDragForce :: Show DragForce where
  show (DragForce d) = "DragForce(c=" <> show d.coefficient <> ")"

-- | Create drag force with coefficient
dragForce :: Number -> DragForce
dragForce c = DragForce { coefficient: clampPositive 100.0 c }

-- | Light drag (minimal resistance)
dragForceLight :: DragForce
dragForceLight = DragForce { coefficient: 0.5 }

-- | Medium drag (balanced)
dragForceMedium :: DragForce
dragForceMedium = DragForce { coefficient: 2.0 }

-- | Heavy drag (strong resistance)
dragForceHeavy :: DragForce
dragForceHeavy = DragForce { coefficient: 8.0 }

-- | Calculate drag force given velocity
dragForceValue :: DragForce -> Force2D -> Force2D
dragForceValue (DragForce d) velocity =
  forceScale (negate d.coefficient) velocity

-- | Get drag coefficient
dragCoefficient :: DragForce -> Number
dragCoefficient (DragForce d) = d.coefficient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // friction force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Friction force opposing motion at contact.
-- |
-- | Friction has two regimes:
-- | - Static: Prevents motion until threshold exceeded
-- | - Kinetic: Constant force opposing motion
newtype FrictionForce = FrictionForce
  { staticCoeff :: Number   -- ^ Static friction coefficient (bounded 0-2)
  , kineticCoeff :: Number  -- ^ Kinetic friction coefficient (bounded 0-2)
  }

derive instance eqFrictionForce :: Eq FrictionForce
derive instance ordFrictionForce :: Ord FrictionForce

instance showFrictionForce :: Show FrictionForce where
  show (FrictionForce f) = 
    "FrictionForce(μs=" <> show f.staticCoeff <> ", μk=" <> show f.kineticCoeff <> ")"

-- | Create friction force
frictionForce :: Number -> Number -> FrictionForce
frictionForce static kinetic = FrictionForce
  { staticCoeff: clampUnit 2.0 static
  , kineticCoeff: clampUnit 2.0 kinetic
  }

-- | Static friction only (no sliding)
frictionStatic :: Number -> FrictionForce
frictionStatic coeff = FrictionForce
  { staticCoeff: clampUnit 2.0 coeff
  , kineticCoeff: clampUnit 2.0 (coeff * 0.8)
  }

-- | Kinetic friction (already sliding)
frictionKinetic :: Number -> FrictionForce
frictionKinetic coeff = FrictionForce
  { staticCoeff: clampUnit 2.0 (coeff * 1.2)
  , kineticCoeff: clampUnit 2.0 coeff
  }

-- | Ice-like friction (very slippery)
frictionIce :: FrictionForce
frictionIce = FrictionForce { staticCoeff: 0.1, kineticCoeff: 0.03 }

-- | Rubber-like friction (high grip)
frictionRubber :: FrictionForce
frictionRubber = FrictionForce { staticCoeff: 1.0, kineticCoeff: 0.8 }

-- | Calculate friction force given normal force and velocity
-- |
-- | Returns kinetic friction if moving, static friction threshold if stationary
frictionForceValue :: FrictionForce -> Number -> Force2D -> Force2D
frictionForceValue (FrictionForce f) normalMag velocity =
  let 
    speed = forceMagnitude velocity
    frictionMag = f.kineticCoeff * absNumber normalMag
  in if speed < 0.0001
     then forceZero  -- stationary, static friction handles externally
     else forceScale (negate frictionMag / speed) velocity

-- | Get static friction coefficient
staticCoefficient :: FrictionForce -> Number
staticCoefficient (FrictionForce f) = f.staticCoeff

-- | Get kinetic friction coefficient
kineticCoefficient :: FrictionForce -> Number
kineticCoefficient (FrictionForce f) = f.kineticCoeff

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // damping force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Damping force for oscillation control.
-- |
-- | Damping reduces oscillation amplitude over time. Critical damping
-- | returns to equilibrium fastest without overshooting.
newtype DampingForce = DampingForce
  { coefficient :: Number  -- ^ Damping coefficient (bounded 0-1000)
  }

derive instance eqDampingForce :: Eq DampingForce
derive instance ordDampingForce :: Ord DampingForce

instance showDampingForce :: Show DampingForce where
  show (DampingForce d) = "DampingForce(c=" <> show d.coefficient <> ")"

-- | Create damping force
dampingForce :: Number -> DampingForce
dampingForce c = DampingForce { coefficient: clampPositive 1000.0 c }

-- | Light damping (underdamped, bouncy)
dampingLight :: DampingForce
dampingLight = DampingForce { coefficient: 5.0 }

-- | Critical damping (no overshoot)
dampingCritical :: DampingForce
dampingCritical = DampingForce { coefficient: 20.0 }

-- | Heavy damping (overdamped, sluggish)
dampingHeavy :: DampingForce
dampingHeavy = DampingForce { coefficient: 50.0 }

-- | Calculate damping force given velocity
dampingForceValue :: DampingForce -> Force2D -> Force2D
dampingForceValue (DampingForce d) velocity =
  forceScale (negate d.coefficient) velocity

-- | Get damping coefficient
dampingCoefficient :: DampingForce -> Number
dampingCoefficient (DampingForce d) = d.coefficient
