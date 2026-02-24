-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // scene3d // position
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Position3D and Direction3D — Foundational spatial types.
-- |
-- | ## Position3D
-- | Position in 3D space with picometer (10^-12 meter) precision.
-- | Sufficient for atomic-scale (bond lengths ~100 pm) through macro-scale
-- | (1 km = 10^15 pm, well within Number range).
-- |
-- | ## Direction3D
-- | Unit vector (length = 1) for directions. Normalized on construction.
-- |
-- | ## Proof References
-- | - Vector normalization: `proofs/Hydrogen/Math/Vec3.lean` (normalize_length)

module Hydrogen.GPU.Scene3D.Position
  ( -- * Position (Picometer Precision)
    Position3D(Position3D)
  , position3D
  , zeroPosition3D
  , getPositionX
  , getPositionY
  , getPositionZ
  , addPosition3D
  , translatePosition3D
  , positionToMeters
  
  -- * Direction (Unit Vector)
  , Direction3D(Direction3D)
  , direction3D
  , normalizeToDirection
  , directionX
  , directionY
  , directionZ
  , negativeX
  , negativeY
  , negativeZ
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (*)
  , (<>)
  )

import Hydrogen.Schema.Dimension.Physical.Atomic (Picometer, picometer, unwrapPicometer)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, normalizeVec3Safe, getX3, getY3, getZ3)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // position (picometer)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Position in 3D space with picometer (10^-12 meter) precision.
-- |
-- | ## Why Picometer?
-- | - Sufficient for atomic-scale visualization (bond lengths ~100 pm)
-- | - Sufficient for macro-scale (1 km = 10^15 pm, well within Number range)
-- | - No floating-point drift for positions that should be equal
-- | - Schema atom with defined conversion to/from Meter
-- |
-- | ## Design
-- | Position is NOT a vector — it represents "where", not "which direction".
-- | Arithmetic rules:
-- | - Position - Position = Vec3 (displacement)
-- | - Position + Vec3 = Position (translation)
-- | - Position + Position = undefined (meaningless)
newtype Position3D = Position3D
  { x :: Picometer
  , y :: Picometer
  , z :: Picometer
  }

derive instance eqPosition3D :: Eq Position3D
derive instance ordPosition3D :: Ord Position3D

instance showPosition3D :: Show Position3D where
  show (Position3D p) = 
    "Position3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Create a position from three picometer values.
position3D :: Picometer -> Picometer -> Picometer -> Position3D
position3D x y z = Position3D { x, y, z }

-- | Origin position (0, 0, 0).
zeroPosition3D :: Position3D
zeroPosition3D = Position3D 
  { x: picometer 0.0
  , y: picometer 0.0
  , z: picometer 0.0
  }

-- | Get X component.
getPositionX :: Position3D -> Picometer
getPositionX (Position3D p) = p.x

-- | Get Y component.
getPositionY :: Position3D -> Picometer
getPositionY (Position3D p) = p.y

-- | Get Z component.
getPositionZ :: Position3D -> Picometer
getPositionZ (Position3D p) = p.z

-- | Add two positions (for weighted averaging, e.g., center of mass).
-- | Note: Generally positions don't add meaningfully. Use for interpolation.
addPosition3D :: Position3D -> Position3D -> Position3D
addPosition3D (Position3D a) (Position3D b) = Position3D
  { x: picometer (unwrapPicometer a.x + unwrapPicometer b.x)
  , y: picometer (unwrapPicometer a.y + unwrapPicometer b.y)
  , z: picometer (unwrapPicometer a.z + unwrapPicometer b.z)
  }

-- | Translate a position by a displacement vector (in picometers).
translatePosition3D :: Position3D -> Vec3 Number -> Position3D
translatePosition3D (Position3D p) displacement = Position3D
  { x: picometer (unwrapPicometer p.x + getX3 displacement)
  , y: picometer (unwrapPicometer p.y + getY3 displacement)
  , z: picometer (unwrapPicometer p.z + getZ3 displacement)
  }

-- | Convert position to meters (for GPU upload where meters are standard).
positionToMeters :: Position3D -> { x :: Number, y :: Number, z :: Number }
positionToMeters (Position3D p) =
  { x: unwrapPicometer p.x * 1.0e-12
  , y: unwrapPicometer p.y * 1.0e-12
  , z: unwrapPicometer p.z * 1.0e-12
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // direction (unit vec)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction in 3D space (unit vector, length = 1).
-- |
-- | ## Invariant
-- | Direction3D always has magnitude 1.0 (within floating-point tolerance).
-- | This is enforced by construction via `normalizeToDirection`.
-- |
-- | ## Proof Reference
-- | `proofs/Hydrogen/Math/Vec3.lean` (normalize_length = 1)
newtype Direction3D = Direction3D (Vec3 Number)

derive instance eqDirection3D :: Eq Direction3D

instance showDirection3D :: Show Direction3D where
  show (Direction3D v) = "Direction3D(" <> show v <> ")"

-- | Create a direction from raw components (normalized automatically).
direction3D :: Number -> Number -> Number -> Direction3D
direction3D x y z = Direction3D (normalizeVec3Safe (vec3 x y z))

-- | Normalize any Vec3 to a Direction3D.
normalizeToDirection :: Vec3 Number -> Direction3D
normalizeToDirection v = Direction3D (normalizeVec3Safe v)

-- | Positive X axis direction (1, 0, 0).
directionX :: Direction3D
directionX = Direction3D (vec3 1.0 0.0 0.0)

-- | Positive Y axis direction (0, 1, 0).
directionY :: Direction3D
directionY = Direction3D (vec3 0.0 1.0 0.0)

-- | Positive Z axis direction (0, 0, 1).
directionZ :: Direction3D
directionZ = Direction3D (vec3 0.0 0.0 1.0)

-- | Negative X axis direction (-1, 0, 0).
negativeX :: Direction3D
negativeX = Direction3D (vec3 (-1.0) 0.0 0.0)

-- | Negative Y axis direction (0, -1, 0).
negativeY :: Direction3D
negativeY = Direction3D (vec3 0.0 (-1.0) 0.0)

-- | Negative Z axis direction (0, 0, -1).
negativeZ :: Direction3D
negativeZ = Direction3D (vec3 0.0 0.0 (-1.0))
