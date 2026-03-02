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
  ( -- * Bounds Behavior
    BoundsBehavior(Clamps, Wraps, Finite)
  
  -- * Bounds Documentation
  , Bounds
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
  
  -- * Wrapping Functions
  , wrapInt
  , wrapNumber
  
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
  
  -- * UnitInterval Type
  , UnitInterval
  , unitInterval
  , unitIntervalUnsafe
  , clampUnit
  , unwrapUnit
  , unitZero
  , unitOne
  , unitHalf
  , addUnit
  , scaleUnit
  , lerpUnit
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , negate
  , mod
  , (+)
  , (-)
  , (*)
  , (&&)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (/=)
  , (/)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (floor) as Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // bounds // behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | How a bounded value behaves at its limits.
-- |
-- | ## Behaviors
-- |
-- | - `Clamps`: Values outside bounds are clamped to min/max.
-- |   Example: percent 150 → 100, percent -10 → 0
-- |
-- | - `Wraps`: Values wrap around using modular arithmetic.
-- |   Example: degrees 370 → 10, degrees -10 → 350
-- |
-- | - `Finite`: Values must be within bounds; out-of-bounds is invalid.
-- |   Used when clamping/wrapping would lose semantic meaning.
-- |   Example: array index must be valid, no "clamping" to last element
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Agents MUST know the behavior to correctly handle edge cases.
-- | Without this, an agent cannot know if 361° should become 1° or 359°.
data BoundsBehavior
  = Clamps   -- ^ Values outside bounds are clamped to min/max
  | Wraps    -- ^ Values wrap around (modular arithmetic)
  | Finite   -- ^ Values must be within bounds; out-of-bounds is invalid

derive instance eqBoundsBehavior :: Eq BoundsBehavior
derive instance ordBoundsBehavior :: Ord BoundsBehavior

instance showBoundsBehavior :: Show BoundsBehavior where
  show Clamps = "Clamps"
  show Wraps = "Wraps"
  show Finite = "Finite"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // bounds documentation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Documentation of valid bounds for a numeric type.
-- |
-- | This is metadata - it describes what values are valid, for use in:
-- | - UI generation (sliders, input validation)
-- | - JSON schema generation
-- | - Documentation
-- | - Agent understanding
-- |
-- | ## Fields
-- |
-- | - `min`: Minimum valid value (inclusive)
-- | - `max`: Maximum valid value (inclusive for Clamps/Finite, exclusive for Wraps)
-- | - `behavior`: How values outside bounds are handled
-- | - `name`: Short identifier for UI labels
-- | - `description`: Human-readable description for tooltips
type Bounds a =
  { min :: a
  , max :: a
  , behavior :: BoundsBehavior
  , name :: String
  , description :: String
  }

-- | Integer bounds
type IntBounds = Bounds Int

-- | Number bounds
type NumberBounds = Bounds Number

-- | Create bounds documentation with explicit behavior.
bounds :: forall a. a -> a -> BoundsBehavior -> String -> String -> Bounds a
bounds min' max' behavior' name' desc =
  { min: min'
  , max: max'
  , behavior: behavior'
  , name: name'
  , description: desc
  }

-- | Create integer bounds with explicit behavior.
intBounds :: Int -> Int -> BoundsBehavior -> String -> String -> IntBounds
intBounds = bounds

-- | Create number bounds with explicit behavior.
numberBounds :: Number -> Number -> BoundsBehavior -> String -> String -> NumberBounds
numberBounds = bounds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // clamping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp an integer to bounds
clampInt :: Int -> Int -> Int -> Int
clampInt minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | otherwise = n

-- | Clamp a number to bounds (NaN/Infinity-safe).
-- |
-- | If the input is NaN or Infinity, returns minVal (safe fallback).
-- | This prevents non-finite values from propagating through the system.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | NaN is the escape hatch for all bounds checks. A malicious actor
-- | could craft `0.0 / 0.0` to bypass validation. This function closes
-- | that vector by treating non-finite values as out-of-bounds.
clampNumber :: Number -> Number -> Number -> Number
clampNumber minVal maxVal n
  | not (isFiniteNumber n) = minVal  -- NaN/Infinity → safe fallback
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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // wrapping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wrap an integer to bounds using modular arithmetic.
-- |
-- | The range is [min, max), meaning max wraps to min.
-- |
-- | ```purescript
-- | wrapInt 0 360 370   -- 10
-- | wrapInt 0 360 (-10) -- 350
-- | wrapInt 0 360 360   -- 0
-- | ```
-- |
-- | ## Mathematical Definition
-- |
-- | wrapInt min max n = min + ((n - min) `mod` (max - min))
-- |
-- | This handles negative values correctly via PureScript's mod behavior.
wrapInt :: Int -> Int -> Int -> Int
wrapInt minVal maxVal n =
  let
    range = maxVal - minVal
    offset = n - minVal
    wrapped = mod ((mod offset range) + range) range
  in
    minVal + wrapped

-- | Wrap a number to bounds using modular arithmetic (NaN/Infinity-safe).
-- |
-- | The range is [min, max), meaning max wraps to min.
-- | If input is NaN or Infinity, returns minVal (safe fallback).
-- |
-- | ```purescript
-- | wrapNumber 0.0 360.0 370.0   -- 10.0
-- | wrapNumber 0.0 360.0 (-10.0) -- 350.0
-- | wrapNumber 0.0 1.0 1.5       -- 0.5
-- | wrapNumber 0.0 360.0 Infinity -- 0.0 (safe fallback)
-- | ```
-- |
-- | ## At Billion-Agent Scale
-- |
-- | `Infinity / range` produces Infinity, and `Infinity - Infinity` produces NaN.
-- | Without this guard, Infinity input becomes NaN output, poisoning the system.
wrapNumber :: Number -> Number -> Number -> Number
wrapNumber minVal maxVal n
  | not (isFiniteNumber n) = minVal  -- NaN/Infinity → safe fallback
  | otherwise =
      let
        range = maxVal - minVal
        offset = n - minVal
        -- Use floor-based modulo for Numbers
        wrapped = offset - range * Number.floor (offset / range)
      in
        minVal + wrapped

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if an integer is within bounds
inBoundsInt :: Int -> Int -> Int -> Boolean
inBoundsInt minVal maxVal n = n >= minVal && n <= maxVal

-- | Check if a number is within bounds
inBoundsNumber :: Number -> Number -> Number -> Boolean
inBoundsNumber minVal maxVal n = n >= minVal && n <= maxVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // finite number handling
-- ═════════════════════════════════════════════════════════════════════════════

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Percentage bounds (0-100), clamps at limits.
-- |
-- | 150% becomes 100%, -10% becomes 0%.
percent :: IntBounds
percent = intBounds 0 100 Clamps "percent" "Integer percentage from 0 to 100"

-- | Unit interval bounds (0.0-1.0), clamps at limits.
-- |
-- | 1.5 becomes 1.0, -0.5 becomes 0.0.
unit :: NumberBounds
unit = numberBounds 0.0 1.0 Clamps "unit" "Normalized value from 0.0 to 1.0"

-- | Byte bounds (0-255), clamps at limits.
-- |
-- | 300 becomes 255, -10 becomes 0.
byte :: IntBounds
byte = intBounds 0 255 Clamps "byte" "8-bit unsigned integer from 0 to 255"

-- | Degree bounds (0-360), WRAPS at limits.
-- |
-- | 370° becomes 10°, -10° becomes 350°.
-- | Range is [0, 360) — 360 wraps to 0.
degrees :: IntBounds
degrees = intBounds 0 360 Wraps "degrees" "Angle in degrees, wraps at 360"

-- | Normalized bounds (0.0-1.0), clamps at limits.
-- |
-- | Alias for unit, more descriptive in some contexts.
normalized :: NumberBounds
normalized = numberBounds 0.0 1.0 Clamps "normalized" "Normalized value from 0.0 to 1.0"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // unit // interval
-- ═════════════════════════════════════════════════════════════════════════════

-- | A number constrained to [0.0, 1.0].
-- |
-- | This is the fundamental bounded numeric type for:
-- | - Probabilities and fractional selections
-- | - Opacity/alpha values
-- | - Interpolation parameters (t)
-- | - Normalized coordinates
-- |
-- | ## Invariant
-- |
-- | The wrapped value is ALWAYS in [0.0, 1.0]. This is enforced by:
-- | - Smart constructor `unitInterval` returns Maybe
-- | - Clamping constructor `clampUnit` always succeeds
-- | - All operations preserve the invariant
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents communicate fractional solutions, using `UnitInterval`
-- | guarantees the receiving agent will never see invalid values.
-- | No defensive clamping needed — the type system enforces validity.
newtype UnitInterval = UnitInterval Number

derive instance eqUnitInterval :: Eq UnitInterval
derive instance ordUnitInterval :: Ord UnitInterval

instance showUnitInterval :: Show UnitInterval where
  show (UnitInterval n) = "UnitInterval(" <> show n <> ")"

-- | Create a UnitInterval with validation.
-- |
-- | Returns Nothing if value is outside [0.0, 1.0].
unitInterval :: Number -> Maybe UnitInterval
unitInterval n
  | n >= 0.0 && n <= 1.0 = Just (UnitInterval n)
  | otherwise = Nothing

-- | Create a UnitInterval without validation.
-- |
-- | ONLY use this when you have already validated the value is in [0.0, 1.0].
-- | Prefer `unitInterval` or `clampUnit` for external input.
unitIntervalUnsafe :: Number -> UnitInterval
unitIntervalUnsafe = UnitInterval

-- | Create a UnitInterval by clamping.
-- |
-- | Values below 0.0 become 0.0, values above 1.0 become 1.0.
-- | This always succeeds.
clampUnit :: Number -> UnitInterval
clampUnit n = UnitInterval (clampNumber 0.0 1.0 n)

-- | Extract the underlying Number.
unwrapUnit :: UnitInterval -> Number
unwrapUnit (UnitInterval n) = n

-- | Zero (0.0)
unitZero :: UnitInterval
unitZero = UnitInterval 0.0

-- | One (1.0)
unitOne :: UnitInterval
unitOne = UnitInterval 1.0

-- | Half (0.5)
unitHalf :: UnitInterval
unitHalf = UnitInterval 0.5

-- | Add two UnitIntervals, clamping the result.
-- |
-- | Useful for accumulating probabilities (with saturation).
addUnit :: UnitInterval -> UnitInterval -> UnitInterval
addUnit (UnitInterval a) (UnitInterval b) = clampUnit (a + b)

-- | Scale a UnitInterval by a factor, clamping the result.
-- |
-- | Negative factors are clamped to 0.
scaleUnit :: Number -> UnitInterval -> UnitInterval
scaleUnit factor (UnitInterval n) = clampUnit (factor * n)

-- | Linear interpolation between two UnitIntervals.
-- |
-- | lerpUnit t a b = a + t * (b - a)
-- |
-- | When t = 0, returns a. When t = 1, returns b.
lerpUnit :: UnitInterval -> UnitInterval -> UnitInterval -> UnitInterval
lerpUnit (UnitInterval t) (UnitInterval a) (UnitInterval b) =
  clampUnit (a + t * (b - a))
