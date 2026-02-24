-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // schema // bounded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bounded numeric primitives - the foundation of the ontology.
-- |
-- | Every value in the design system has semantic meaning AND valid bounds.
-- | A hue is 0-359. A saturation is 0-100. A channel is 0-255. These are
-- | not interchangeable, and the type system enforces this.
-- |
-- | ## Design Philosophy
-- |
-- | We do NOT use phantom types or type-level naturals here. Instead:
-- | - Each domain gets its own newtype (Hue, Saturation, Channel, etc.)
-- | - Smart constructors clamp or validate at construction time
-- | - The `Bounds` record documents valid ranges for serialization/UI
-- |
-- | This keeps the types simple, serializable, and comprehensible to both
-- | humans and AI agents consuming the schema.

module Hydrogen.Schema.Bounded
  ( -- * Bounds Documentation
    Bounds
  , IntBounds
  , NumberBounds
  , bounds
  , intBounds
  , numberBounds
  
  -- * Clamping Functions
  , clampInt
  , clampNumber
  , clampNumberMin
  , clampNumberMax
  
  -- * Finite Number Handling
  , ensureFinite
  , isFiniteNumber
  
  -- * Validation
  , inBoundsInt
  , inBoundsNumber
  
  -- * Common Bounds
  , percent
  , unit
  , byte
  , degrees
  , normalized
  ) where

import Prelude
  ( otherwise
  , not
  , negate
  , (&&)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (/=)
  , (/)
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // bounds documentation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Documentation of valid bounds for a numeric type.
-- |
-- | This is metadata - it describes what values are valid, for use in:
-- | - UI generation (sliders, input validation)
-- | - JSON schema generation
-- | - Documentation
-- | - Agent understanding
type Bounds a =
  { min :: a
  , max :: a
  , name :: String
  , description :: String
  }

-- | Integer bounds
type IntBounds = Bounds Int

-- | Number bounds
type NumberBounds = Bounds Number

-- | Create bounds documentation
bounds :: forall a. a -> a -> String -> String -> Bounds a
bounds min' max' name' desc =
  { min: min'
  , max: max'
  , name: name'
  , description: desc
  }

-- | Create integer bounds
intBounds :: Int -> Int -> String -> String -> IntBounds
intBounds = bounds

-- | Create number bounds
numberBounds :: Number -> Number -> String -> String -> NumberBounds
numberBounds = bounds

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // clamping
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clamp an integer to bounds
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp a number to bounds
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp a number to minimum only (no upper bound)
clampNumberMin :: Number -> Number -> Number
clampNumberMin minVal n
  | n < minVal = minVal
  | otherwise = n

-- | Clamp a number to maximum only (no lower bound)
clampNumberMax :: Number -> Number -> Number
clampNumberMax maxVal n
  | n > maxVal = maxVal
  | otherwise = n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // validation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if an integer is within bounds
inBoundsInt :: Int -> Int -> Int -> Boolean
inBoundsInt minVal maxVal n = n >= minVal && n <= maxVal

-- | Check if a number is within bounds
inBoundsNumber :: Number -> Number -> Number -> Boolean
inBoundsNumber minVal maxVal n = n >= minVal && n <= maxVal

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // finite number handling
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a number is finite (not Infinity, -Infinity, or NaN)
-- |
-- | Uses the pattern that NaN /= NaN and comparison with Infinity.
isFiniteNumber :: Number -> Boolean
isFiniteNumber n = not (n /= n) && n /= (1.0 / 0.0) && n /= (-1.0 / 0.0)

-- | Ensure a number is finite, returning fallback if not
-- |
-- | Protects against Infinity and NaN propagating through calculations:
-- | ```purescript
-- | ensureFinite (1.0 / 0.0) 0.0  -- 0.0 (Infinity replaced with fallback)
-- | ensureFinite (0.0 / 0.0) 0.0  -- 0.0 (NaN replaced with fallback)
-- | ensureFinite 42.0 0.0         -- 42.0 (finite, unchanged)
-- | ```
ensureFinite :: Number -> Number -> Number
ensureFinite n fallback
  | isFiniteNumber n = n
  | otherwise = fallback

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // common bounds
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Percentage bounds (0-100)
percent :: IntBounds
percent = intBounds 0 100 "percent" "Integer percentage from 0 to 100"

-- | Unit interval bounds (0.0-1.0)
unit :: NumberBounds
unit = numberBounds 0.0 1.0 "unit" "Normalized value from 0.0 to 1.0"

-- | Byte bounds (0-255)
byte :: IntBounds
byte = intBounds 0 255 "byte" "8-bit unsigned integer from 0 to 255"

-- | Degree bounds (0-359)
-- | Note: 360 wraps to 0, so valid range is 0-359
degrees :: IntBounds
degrees = intBounds 0 359 "degrees" "Angle in degrees from 0 to 359"

-- | Normalized bounds (0.0-1.0)
-- | Alias for unit, more descriptive in some contexts
normalized :: NumberBounds
normalized = numberBounds 0.0 1.0 "normalized" "Normalized value from 0.0 to 1.0"
