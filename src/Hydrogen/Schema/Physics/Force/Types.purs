-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // physics // force // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core force types and vector operations.
-- |
-- | ## Design Philosophy
-- |
-- | Forces are vectors with magnitude and direction. This module provides
-- | the fundamental Force2D type and vector arithmetic operations.
-- |
-- | ## Bounded Design
-- |
-- | Force components are bounded to [-10000, 10000] to prevent numerical
-- | instability in physics simulations.

module Hydrogen.Schema.Physics.Force.Types
  ( -- * Force Vector
    Force2D(..)
  , force2D
  , forceZero
  , forceUp
  , forceDown
  , forceLeft
  , forceRight
  , forceX
  , forceY
  , forceMagnitude
  , forceDirection
  , forceNormalize
  , forceScale
  , forceNegate
  , forceAdd
  , forceSubtract
  , forceDot
  , forceClamp
  
  -- * Force Classification
  , ForceType(..)
  , isConservative
  , isNonConservative
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
  , not
  , (&&)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<<<)
  , (<>)
  , (>)
  )

import Data.Number (sqrt, atan2)

import Hydrogen.Schema.Physics.Force.Internal
  ( clampForceComponent
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // force vector
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D force vector.
-- |
-- | Forces are vectors with magnitude and direction. Components are bounded
-- | to prevent numerical instability.
newtype Force2D = Force2D { x :: Number, y :: Number }

derive instance eqForce2D :: Eq Force2D
derive instance ordForce2D :: Ord Force2D

instance showForce2D :: Show Force2D where
  show (Force2D f) = "Force2D(" <> show f.x <> ", " <> show f.y <> ")"

-- | Create a 2D force vector with bounded components
force2D :: Number -> Number -> Force2D
force2D x y = Force2D 
  { x: clampForceComponent x
  , y: clampForceComponent y
  }

-- | Zero force (no acceleration)
forceZero :: Force2D
forceZero = Force2D { x: 0.0, y: 0.0 }

-- | Unit force pointing up (negative Y in screen coordinates)
forceUp :: Force2D
forceUp = Force2D { x: 0.0, y: -1.0 }

-- | Unit force pointing down (positive Y in screen coordinates)
forceDown :: Force2D
forceDown = Force2D { x: 0.0, y: 1.0 }

-- | Unit force pointing left
forceLeft :: Force2D
forceLeft = Force2D { x: -1.0, y: 0.0 }

-- | Unit force pointing right
forceRight :: Force2D
forceRight = Force2D { x: 1.0, y: 0.0 }

-- | Get X component
forceX :: Force2D -> Number
forceX (Force2D f) = f.x

-- | Get Y component
forceY :: Force2D -> Number
forceY (Force2D f) = f.y

-- | Calculate force magnitude
forceMagnitude :: Force2D -> Number
forceMagnitude (Force2D f) = sqrt (f.x * f.x + f.y * f.y)

-- | Calculate force direction as angle in radians from positive X axis
forceDirection :: Force2D -> Number
forceDirection (Force2D f) = atan2 f.y f.x

-- | Normalize force to unit length (magnitude 1)
forceNormalize :: Force2D -> Force2D
forceNormalize f =
  let mag = forceMagnitude f
  in if mag < 0.0001 
     then forceZero
     else forceScale (1.0 / mag) f

-- | Scale force by a factor
forceScale :: Number -> Force2D -> Force2D
forceScale s (Force2D f) = force2D (f.x * s) (f.y * s)

-- | Negate force (reverse direction)
forceNegate :: Force2D -> Force2D
forceNegate (Force2D f) = Force2D { x: negate f.x, y: negate f.y }

-- | Add two forces (vector addition)
forceAdd :: Force2D -> Force2D -> Force2D
forceAdd (Force2D a) (Force2D b) = force2D (a.x + b.x) (a.y + b.y)

-- | Subtract forces (a - b)
forceSubtract :: Force2D -> Force2D -> Force2D
forceSubtract (Force2D a) (Force2D b) = force2D (a.x - b.x) (a.y - b.y)

-- | Dot product of two forces
forceDot :: Force2D -> Force2D -> Number
forceDot (Force2D a) (Force2D b) = a.x * b.x + a.y * b.y

-- | Clamp force magnitude to maximum
forceClamp :: Number -> Force2D -> Force2D
forceClamp maxMag f =
  let mag = forceMagnitude f
  in if mag > maxMag && mag > 0.0001
     then forceScale (maxMag / mag) f
     else f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // force types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classification of force types.
data ForceType
  = Conservative    -- ^ Path-independent, has potential energy
  | NonConservative -- ^ Path-dependent, dissipates energy

derive instance eqForceType :: Eq ForceType
derive instance ordForceType :: Ord ForceType

instance showForceType :: Show ForceType where
  show Conservative = "Conservative"
  show NonConservative = "NonConservative"

-- | Check if force is conservative
isConservative :: ForceType -> Boolean
isConservative Conservative = true
isConservative NonConservative = false

-- | Check if force is non-conservative
isNonConservative :: ForceType -> Boolean
isNonConservative = not <<< isConservative
