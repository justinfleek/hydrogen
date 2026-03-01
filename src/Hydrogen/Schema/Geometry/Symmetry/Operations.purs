-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // symmetry // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Symmetry Operations — Transformations that preserve symmetry.
-- |
-- | ## Design Philosophy
-- |
-- | Symmetry operations are the actual transformations that can be applied
-- | to shapes while preserving their symmetry properties. This includes:
-- | - Identity (do nothing)
-- | - Reflection (mirror across axis)
-- | - Rotation (rotate by angle)
-- | - Translation (shift by vector)
-- | - Glide (reflect + translate)
-- | - Composition (combine operations)
-- |
-- | ## Use Cases
-- |
-- | - Transform application
-- | - Operation algebra
-- | - Symmetry verification
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)
-- | - Geometry.Angle (Degrees)
-- | - Symmetry.Reflection (ReflectionAxis)

module Hydrogen.Schema.Geometry.Symmetry.Operations
  ( SymmetryOp(..)
  , identityOp
  , reflectOp
  , rotateOp
  , translateOp
  , glideOp
  , composeOp
  , inverseOp
  , opToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (<>)
  )

import Hydrogen.Schema.Geometry.Angle 
  ( Degrees
  , degrees
  , unwrapDegrees
  )

import Hydrogen.Schema.Geometry.Symmetry.Reflection (ReflectionAxis)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // symmetry operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Symmetry operations that can be applied to shapes.
data SymmetryOp
  = Identity                        -- ^ Do nothing
  | Reflect ReflectionAxis          -- ^ Reflect across axis
  | Rotate Degrees                  -- ^ Rotate by angle
  | Translate Number Number         -- ^ Translate by (dx, dy)
  | Glide ReflectionAxis Number     -- ^ Glide reflection
  | Compose SymmetryOp SymmetryOp   -- ^ Composition of operations

derive instance eqSymmetryOp :: Eq SymmetryOp

instance showSymmetryOp :: Show SymmetryOp where
  show Identity = "Identity"
  show (Reflect axis) = "(Reflect " <> show axis <> ")"
  show (Rotate angle) = "(Rotate " <> show angle <> ")"
  show (Translate dx dy) = "(Translate dx:" <> show dx <> " dy:" <> show dy <> ")"
  show (Glide axis dist) = "(Glide axis:" <> show axis <> " distance:" <> show dist <> ")"
  show (Compose a b) = "(Compose " <> show a <> " " <> show b <> ")"

-- | Identity operation (do nothing)
identityOp :: SymmetryOp
identityOp = Identity

-- | Reflection operation
reflectOp :: ReflectionAxis -> SymmetryOp
reflectOp = Reflect

-- | Rotation operation
rotateOp :: Degrees -> SymmetryOp
rotateOp = Rotate

-- | Translation operation
translateOp :: Number -> Number -> SymmetryOp
translateOp = Translate

-- | Glide reflection operation
glideOp :: ReflectionAxis -> Number -> SymmetryOp
glideOp = Glide

-- | Compose two operations (apply b first, then a)
composeOp :: SymmetryOp -> SymmetryOp -> SymmetryOp
composeOp Identity b = b
composeOp a Identity = a
composeOp a b = Compose a b

-- | Get the inverse operation
inverseOp :: SymmetryOp -> SymmetryOp
inverseOp Identity = Identity
inverseOp (Reflect axis) = Reflect axis  -- reflection is self-inverse
inverseOp (Rotate angle) = Rotate (degrees (negate (unwrapDegrees angle)))
inverseOp (Translate dx dy) = Translate (negate dx) (negate dy)
inverseOp (Glide axis dist) = Glide axis (negate dist)
inverseOp (Compose a b) = Compose (inverseOp b) (inverseOp a)

-- | Convert operation to descriptive string
opToString :: SymmetryOp -> String
opToString = show
