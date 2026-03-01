-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // physics // force // conservative
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Conservative forces — path-independent forces with potential energy.
-- |
-- | ## Conservative Force Categories
-- |
-- | **Gravitational**: Constant downward pull
-- | **Spring/Elastic**: Proportional to displacement (Hooke's law)
-- | **Point Force**: Attraction/repulsion from a point (electrostatic-like)
-- |
-- | Conservative forces are path-independent: the work done depends only on
-- | start and end positions, not the path taken. They have associated
-- | potential energy functions.

module Hydrogen.Schema.Physics.Force.Conservative
  ( -- * Gravitational Force
    Gravity(..)
  , gravity
  , gravityEarth
  , gravityMoon
  , gravityLight
  , gravityHeavy
  , gravityZero
  , gravityForce
  , gravityMagnitude
  , gravityDirection
  
  -- * Spring Force (Hooke's Law)
  , SpringForce(..)
  , springForce
  , springForceDefault
  , springForceSoft
  , springForceStiff
  , springForceValue
  , springPotentialEnergy
  , springStiffness
  , springRestLength
  
  -- * Attractive/Repulsive Force
  , PointForce(..)
  , pointForce
  , attractiveForce
  , repulsiveForce
  , pointForceValue
  , pointForceStrength
  , pointForceFalloff
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
  , (-)
  , (/)
  , (<)
  , (<>)
  )

import Hydrogen.Schema.Physics.Force.Types
  ( Force2D(..)
  , forceDown
  , forceMagnitude
  , forceNormalize
  , forceScale
  , forceZero
  )

import Hydrogen.Schema.Physics.Force.Internal
  ( absNumber
  , clampForceComponent
  , clampPositive
  , power
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gravitational force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gravitational force configuration.
-- |
-- | Gravity is a constant force in a fixed direction.
-- | In UI space, "down" is typically positive Y.
newtype Gravity = Gravity 
  { magnitude :: Number  -- ^ Acceleration due to gravity (bounded 0-1000)
  , direction :: Force2D -- ^ Unit vector direction
  }

derive instance eqGravity :: Eq Gravity
derive instance ordGravity :: Ord Gravity

instance showGravity :: Show Gravity where
  show (Gravity g) = "Gravity(" <> show g.magnitude <> ")"

-- | Create gravity with magnitude and direction
gravity :: Number -> Force2D -> Gravity
gravity mag dir = Gravity 
  { magnitude: clampPositive 1000.0 mag
  , direction: forceNormalize dir
  }

-- | Earth-like gravity (strong, for heavy UI feel)
gravityEarth :: Gravity
gravityEarth = Gravity { magnitude: 9.8, direction: forceDown }

-- | Moon-like gravity (light, floaty feel)
gravityMoon :: Gravity
gravityMoon = Gravity { magnitude: 1.62, direction: forceDown }

-- | Light gravity for subtle effects
gravityLight :: Gravity
gravityLight = Gravity { magnitude: 2.0, direction: forceDown }

-- | Heavy gravity for weighty feel
gravityHeavy :: Gravity
gravityHeavy = Gravity { magnitude: 20.0, direction: forceDown }

-- | Zero gravity
gravityZero :: Gravity
gravityZero = Gravity { magnitude: 0.0, direction: forceDown }

-- | Calculate gravitational force on a mass
gravityForce :: Gravity -> Number -> Force2D
gravityForce (Gravity g) mass = 
  forceScale (g.magnitude * clampPositive 1000.0 mass) g.direction

-- | Get gravity magnitude
gravityMagnitude :: Gravity -> Number
gravityMagnitude (Gravity g) = g.magnitude

-- | Get gravity direction
gravityDirection :: Gravity -> Force2D
gravityDirection (Gravity g) = g.direction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // spring force
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spring force following Hooke's Law: F = -k * x
-- |
-- | Springs pull toward their rest position with force proportional to
-- | displacement. This creates oscillatory motion when combined with mass.
newtype SpringForce = SpringForce
  { stiffness :: Number   -- ^ Spring constant k (bounded 0-10000)
  , restLength :: Number  -- ^ Natural length of spring (bounded 0-10000)
  }

derive instance eqSpringForce :: Eq SpringForce
derive instance ordSpringForce :: Ord SpringForce

instance showSpringForce :: Show SpringForce where
  show (SpringForce s) = "SpringForce(k=" <> show s.stiffness <> ")"

-- | Create a spring force
springForce :: Number -> Number -> SpringForce
springForce k rest = SpringForce
  { stiffness: clampPositive 10000.0 k
  , restLength: clampPositive 10000.0 rest
  }

-- | Default spring (moderate stiffness)
springForceDefault :: SpringForce
springForceDefault = SpringForce { stiffness: 100.0, restLength: 0.0 }

-- | Soft spring (low stiffness, slow oscillation)
springForceSoft :: SpringForce
springForceSoft = SpringForce { stiffness: 30.0, restLength: 0.0 }

-- | Stiff spring (high stiffness, fast oscillation)
springForceStiff :: SpringForce
springForceStiff = SpringForce { stiffness: 300.0, restLength: 0.0 }

-- | Calculate spring force given current displacement from rest
-- |
-- | Displacement is a vector from rest position to current position.
-- | Force points back toward rest position.
springForceValue :: SpringForce -> Force2D -> Force2D
springForceValue (SpringForce s) displacement =
  let 
    dist = forceMagnitude displacement
    stretch = dist - s.restLength
  in if absNumber dist < 0.0001
     then forceZero
     else forceScale (negate s.stiffness * stretch / dist) displacement

-- | Calculate potential energy stored in spring
springPotentialEnergy :: SpringForce -> Number -> Number
springPotentialEnergy (SpringForce s) displacement =
  let stretch = displacement - s.restLength
  in 0.5 * s.stiffness * stretch * stretch

-- | Get spring stiffness
springStiffness :: SpringForce -> Number
springStiffness (SpringForce s) = s.stiffness

-- | Get spring rest length
springRestLength :: SpringForce -> Number
springRestLength (SpringForce s) = s.restLength

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // attractive/repulsive
-- ═════════════════════════════════════════════════════════════════════════════

-- | Point force: attraction or repulsion from a point.
-- |
-- | Used for:
-- | - Magnetic UI elements
-- | - Particle effects
-- | - Snap-to-point behavior
newtype PointForce = PointForce
  { strength :: Number   -- ^ Force strength (positive = attractive, negative = repulsive)
  , falloff :: Number    -- ^ Distance falloff exponent (1 = linear, 2 = inverse square)
  , minDistance :: Number -- ^ Minimum distance to prevent infinite force
  }

derive instance eqPointForce :: Eq PointForce
derive instance ordPointForce :: Ord PointForce

instance showPointForce :: Show PointForce where
  show (PointForce p) = "PointForce(str=" <> show p.strength <> ")"

-- | Create a point force
pointForce :: Number -> Number -> PointForce
pointForce strength falloff = PointForce
  { strength: clampForceComponent strength
  , falloff: clampPositive 4.0 falloff
  , minDistance: 1.0
  }

-- | Attractive force (pulls toward point)
attractiveForce :: Number -> PointForce
attractiveForce strength = PointForce
  { strength: absNumber (clampForceComponent strength)
  , falloff: 2.0
  , minDistance: 1.0
  }

-- | Repulsive force (pushes away from point)
repulsiveForce :: Number -> PointForce
repulsiveForce strength = PointForce
  { strength: negate (absNumber (clampForceComponent strength))
  , falloff: 2.0
  , minDistance: 1.0
  }

-- | Calculate point force given displacement from force center
pointForceValue :: PointForce -> Force2D -> Force2D
pointForceValue (PointForce p) displacement =
  let 
    dist = forceMagnitude displacement
    effectiveDist = if dist < p.minDistance then p.minDistance else dist
    falloffFactor = power effectiveDist p.falloff
    mag = p.strength / falloffFactor
  in if dist < 0.0001
     then forceZero
     else forceScale (mag / dist) displacement

-- | Get point force strength
pointForceStrength :: PointForce -> Number
pointForceStrength (PointForce p) = p.strength

-- | Get point force falloff
pointForceFalloff :: PointForce -> Number
pointForceFalloff (PointForce p) = p.falloff
