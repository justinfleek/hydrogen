-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // physics // force // fields
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Force fields and application utilities.
-- |
-- | ## Force Fields
-- |
-- | A force field represents a spatial distribution of forces. At any point
-- | in space, the field defines what force would be applied to an object.
-- |
-- | ## Force Application
-- |
-- | Utilities for applying forces to calculate acceleration and combining
-- | multiple forces into a net force.

module Hydrogen.Schema.Physics.Force.Fields
  ( -- * Force Field
    ForceField(EmptyField, UniformField, CompositeField)
  , emptyField
  , uniformField
  , addForceToField
  , fieldForceAt
  , fieldContains
  
  -- * Force Application
  , applyForce
  , netForce
  , accelerationFromForce
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (/)
  , (<)
  , (<>)
  , (>)
  )

import Data.Array (foldl, snoc)

import Hydrogen.Schema.Physics.Force.Types
  ( Force2D
  , forceAdd
  , forceScale
  , forceZero
  )

import Hydrogen.Schema.Physics.Force.Internal
  ( arrayLength
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // force field
-- ═════════════════════════════════════════════════════════════════════════════

-- | A collection of forces that can be evaluated at any point.
data ForceField
  = EmptyField
  | UniformField Force2D
  | CompositeField (Array ForceField)

derive instance eqForceField :: Eq ForceField

instance showForceField :: Show ForceField where
  show EmptyField = "EmptyField"
  show (UniformField f) = "UniformField(" <> show f <> ")"
  show (CompositeField fields) = "CompositeField[" <> show (arrayLength fields) <> "]"

-- | Empty force field (no forces)
emptyField :: ForceField
emptyField = EmptyField

-- | Uniform force field (same force everywhere)
uniformField :: Force2D -> ForceField
uniformField = UniformField

-- | Add a force to a field
addForceToField :: ForceField -> ForceField -> ForceField
addForceToField EmptyField f = f
addForceToField f EmptyField = f
addForceToField (CompositeField fs) f = CompositeField (snoc fs f)
addForceToField f1 f2 = CompositeField [f1, f2]

-- | Evaluate force field at a position (for uniform fields, position is ignored)
fieldForceAt :: ForceField -> Force2D -> Force2D
fieldForceAt EmptyField _ = forceZero
fieldForceAt (UniformField f) _ = f
fieldForceAt (CompositeField fields) pos = 
  foldl (\acc field -> forceAdd acc (fieldForceAt field pos)) forceZero fields

-- | Check if field contains any forces
fieldContains :: ForceField -> Boolean
fieldContains EmptyField = false
fieldContains (UniformField _) = true
fieldContains (CompositeField fields) = arrayLength fields > 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // force application
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a force to calculate acceleration (F = ma, so a = F/m)
applyForce :: Force2D -> Number -> Force2D
applyForce f mass =
  let m = if mass < 0.001 then 0.001 else mass
  in forceScale (1.0 / m) f

-- | Calculate net force from multiple forces
netForce :: Array Force2D -> Force2D
netForce forces = foldl forceAdd forceZero forces

-- | Calculate acceleration from force and mass
accelerationFromForce :: Force2D -> Number -> Force2D
accelerationFromForce = applyForce
