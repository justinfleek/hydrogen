-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // geometry // symmetry // reflection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Reflection Symmetry — Mirror axes for bilateral symmetry.
-- |
-- | ## Design Philosophy
-- |
-- | A reflection axis defines a line across which a shape can be mirrored.
-- | The axis is characterized by its angle from horizontal:
-- | - 0° = horizontal axis (reflects top-bottom)
-- | - 90° = vertical axis (reflects left-right)
-- | - 45° = diagonal axis
-- | - 135° = anti-diagonal axis
-- |
-- | ## Use Cases
-- |
-- | - UI layouts with bilateral symmetry
-- | - Logo and icon design
-- | - Mirror transformations
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Geometry.Angle (Degrees)

module Hydrogen.Schema.Geometry.Symmetry.Reflection
  ( ReflectionAxis(..)
  , reflectionAxis
  , horizontalAxis
  , verticalAxis
  , diagonalAxis
  , antiDiagonalAxis
  , axisAngle
  , isHorizontalAxis
  , isVerticalAxis
  , isDiagonalAxis
  , perpendicularAxis
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (&&)
  , (||)
  , (<>)
  , (<)
  , (>)
  )

import Hydrogen.Schema.Geometry.Angle 
  ( Degrees
  , degrees
  , unwrapDegrees
  , addAngle
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // reflection symmetry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis of reflection symmetry.
-- |
-- | A reflection axis is defined by its angle from horizontal.
-- | - 0° = horizontal axis (reflects top-bottom)
-- | - 90° = vertical axis (reflects left-right)
-- | - 45° = diagonal axis
-- | - 135° = anti-diagonal axis
newtype ReflectionAxis = ReflectionAxis { angle :: Degrees }

derive instance eqReflectionAxis :: Eq ReflectionAxis
derive instance ordReflectionAxis :: Ord ReflectionAxis

instance showReflectionAxis :: Show ReflectionAxis where
  show (ReflectionAxis r) = "(ReflectionAxis angle:" <> show r.angle <> ")"

-- | Create a reflection axis at the given angle
reflectionAxis :: Degrees -> ReflectionAxis
reflectionAxis angle = ReflectionAxis { angle }

-- | Horizontal reflection axis (mirrors top-bottom)
horizontalAxis :: ReflectionAxis
horizontalAxis = ReflectionAxis { angle: degrees 0.0 }

-- | Vertical reflection axis (mirrors left-right)
verticalAxis :: ReflectionAxis
verticalAxis = ReflectionAxis { angle: degrees 90.0 }

-- | Diagonal reflection axis (45°, mirrors across main diagonal)
diagonalAxis :: ReflectionAxis
diagonalAxis = ReflectionAxis { angle: degrees 45.0 }

-- | Anti-diagonal reflection axis (135°, mirrors across anti-diagonal)
antiDiagonalAxis :: ReflectionAxis
antiDiagonalAxis = ReflectionAxis { angle: degrees 135.0 }

-- | Get the angle of a reflection axis
axisAngle :: ReflectionAxis -> Degrees
axisAngle (ReflectionAxis r) = r.angle

-- | Check if axis is horizontal (within tolerance)
isHorizontalAxis :: ReflectionAxis -> Boolean
isHorizontalAxis (ReflectionAxis r) = 
  let a = unwrapDegrees r.angle
  in a < 0.001 || a > 359.999

-- | Check if axis is vertical (within tolerance)
isVerticalAxis :: ReflectionAxis -> Boolean
isVerticalAxis (ReflectionAxis r) =
  let a = unwrapDegrees r.angle
  in a > 89.999 && a < 90.001

-- | Check if axis is diagonal (45° or 135°)
isDiagonalAxis :: ReflectionAxis -> Boolean
isDiagonalAxis (ReflectionAxis r) =
  let a = unwrapDegrees r.angle
  in (a > 44.999 && a < 45.001) || (a > 134.999 && a < 135.001)

-- | Get the perpendicular axis
perpendicularAxis :: ReflectionAxis -> ReflectionAxis
perpendicularAxis (ReflectionAxis r) = 
  ReflectionAxis { angle: addAngle r.angle (degrees 90.0) }
