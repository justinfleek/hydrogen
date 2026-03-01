-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // dimension // distance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Distance — Bounded distance and length types for spatial measurements.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides bounded distance types that enforce positive values
-- | at construction time. Unlike raw Number, these types make invalid states
-- | unrepresentable:
-- |
-- | - `PositiveLength`: Strictly positive (> 0), for distances that must exist
-- | - `NonNegativeLength`: Zero or positive (>= 0), for offsets and deltas
-- |
-- | ## Use Cases
-- |
-- | - Camera distance from target (must be positive)
-- | - Field of view angles (must be positive)
-- | - Object dimensions (must be positive)
-- | - Z-depth values (can be zero or positive)
-- |
-- | ## Bounds
-- |
-- | Default bounds are practical maxima for GPU rendering:
-- | - PositiveLength: (0, 1e9] — from epsilon to billion units
-- | - NonNegativeLength: [0, 1e9] — from zero to billion units
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)
-- | - Hydrogen.Schema.Bounded (bounds documentation)
-- |
-- | ## Dependents
-- |
-- | - Hydrogen.Element.Core.Media (Model3DCamera distance)
-- | - Hydrogen.GPU.Scene3D.Camera (camera positioning)

module Hydrogen.Schema.Dimension.Distance
  ( -- * Positive Length
    PositiveLength(PositiveLength)
  , positiveLength
  , unwrapPositiveLength
  , positiveLengthBounds
  , defaultPositiveLength
  
  -- * Non-Negative Length
  , NonNegativeLength(NonNegativeLength)
  , nonNegativeLength
  , unwrapNonNegativeLength
  , nonNegativeLengthBounds
  , zeroLength
  
  -- * Operations
  , addLengths
  , subtractToNonNegative
  , scaleLengthBy
  , maxLength
  , minLength
  
  -- * Conversion
  , positiveToNonNegative
  , nonNegativeToPositive
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Bounded
  ( NumberBounds
  , numberBounds
  , BoundsBehavior(Clamps)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // positive length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Strictly positive length value.
-- |
-- | Enforces value > 0 at construction. Used for distances that must exist,
-- | such as camera distance from target, field of view, object dimensions.
-- |
-- | Invalid values (zero or negative) are clamped to a small epsilon.
newtype PositiveLength = PositiveLength Number

derive instance eqPositiveLength :: Eq PositiveLength
derive instance ordPositiveLength :: Ord PositiveLength

instance showPositiveLength :: Show PositiveLength where
  show (PositiveLength n) = "PositiveLength " <> show n

-- | Minimum positive value (epsilon to avoid divide-by-zero)
epsilon :: Number
epsilon = 1.0e-10

-- | Maximum practical length for GPU rendering
maxValue :: Number
maxValue = 1.0e9

-- | Create a positive length, clamping to valid range.
-- |
-- | Values <= 0 are clamped to epsilon.
-- | Values > maxValue are clamped to maxValue.
positiveLength :: Number -> PositiveLength
positiveLength n
  | n < epsilon = PositiveLength epsilon
  | n > maxValue = PositiveLength maxValue
  | otherwise = PositiveLength n

-- | Extract the raw Number value.
unwrapPositiveLength :: PositiveLength -> Number
unwrapPositiveLength (PositiveLength n) = n

-- | Default positive length (1.0 unit).
defaultPositiveLength :: PositiveLength
defaultPositiveLength = PositiveLength 1.0

-- | Bounds documentation for PositiveLength.
positiveLengthBounds :: NumberBounds
positiveLengthBounds = numberBounds epsilon maxValue Clamps 
  "positiveLength" 
  "Strictly positive length (epsilon to 1e9)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // non-negative length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Non-negative length value (zero or positive).
-- |
-- | Enforces value >= 0 at construction. Used for offsets, deltas, and
-- | values where zero is meaningful (e.g., z-depth, padding).
-- |
-- | Negative values are clamped to zero.
newtype NonNegativeLength = NonNegativeLength Number

derive instance eqNonNegativeLength :: Eq NonNegativeLength
derive instance ordNonNegativeLength :: Ord NonNegativeLength

instance showNonNegativeLength :: Show NonNegativeLength where
  show (NonNegativeLength n) = "NonNegativeLength " <> show n

-- | Create a non-negative length, clamping negatives to zero.
nonNegativeLength :: Number -> NonNegativeLength
nonNegativeLength n
  | n < 0.0 = NonNegativeLength 0.0
  | n > maxValue = NonNegativeLength maxValue
  | otherwise = NonNegativeLength n

-- | Extract the raw Number value.
unwrapNonNegativeLength :: NonNegativeLength -> Number
unwrapNonNegativeLength (NonNegativeLength n) = n

-- | Zero length.
zeroLength :: NonNegativeLength
zeroLength = NonNegativeLength 0.0

-- | Bounds documentation for NonNegativeLength.
nonNegativeLengthBounds :: NumberBounds
nonNegativeLengthBounds = numberBounds 0.0 maxValue Clamps 
  "nonNegativeLength" 
  "Non-negative length (0 to 1e9)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two positive lengths.
addLengths :: PositiveLength -> PositiveLength -> PositiveLength
addLengths (PositiveLength a) (PositiveLength b) = positiveLength (a + b)

-- | Subtract lengths, clamping to zero if result would be negative.
subtractToNonNegative :: NonNegativeLength -> NonNegativeLength -> NonNegativeLength
subtractToNonNegative (NonNegativeLength a) (NonNegativeLength b) = 
  nonNegativeLength (a - b)

-- | Scale a length by a factor.
-- |
-- | Negative factors are treated as zero (resulting in clamped length).
scaleLengthBy :: Number -> PositiveLength -> PositiveLength
scaleLengthBy factor (PositiveLength n) = positiveLength (factor * n)

-- | Maximum of two lengths.
maxLength :: PositiveLength -> PositiveLength -> PositiveLength
maxLength a@(PositiveLength an) b@(PositiveLength bn)
  | an >= bn = a
  | otherwise = b

-- | Minimum of two lengths.
minLength :: PositiveLength -> PositiveLength -> PositiveLength
minLength a@(PositiveLength an) b@(PositiveLength bn)
  | an < bn = a
  | otherwise = b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert positive length to non-negative (always succeeds).
positiveToNonNegative :: PositiveLength -> NonNegativeLength
positiveToNonNegative (PositiveLength n) = NonNegativeLength n

-- | Try to convert non-negative to positive.
-- |
-- | Returns Nothing if the value is zero (since positive requires > 0).
nonNegativeToPositive :: NonNegativeLength -> Maybe PositiveLength
nonNegativeToPositive (NonNegativeLength n)
  | n > 0.0 = Just (PositiveLength n)
  | otherwise = Nothing
