-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // medical // infusion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | InfusionRate — Bounded type for IV infusion rates.
-- |
-- | ## Safety-Critical Design
-- |
-- | Medical infusion pumps deliver fluids at controlled rates. An unbounded
-- | value could cause:
-- | - Fluid overload (too fast)
-- | - Inadequate therapy (too slow)
-- | - System crashes from NaN/Infinity
-- |
-- | This type guarantees:
-- | - Non-negative values (cannot infuse negative fluid)
-- | - Maximum safe rate (configurable, default 999 mL/hr)
-- | - Integer precision (discrete steps, no fractional mL/hr)
-- | - NaN/Infinity rejection
-- |
-- | ## Bounds
-- |
-- | - Min: 0 mL/hr (pump stopped)
-- | - Max: 999 mL/hr (typical IV pump maximum)
-- | - Step: 1 mL/hr (integer precision)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents compose medical dashboards, they MUST NOT be able to
-- | inject `Infinity` or `NaN` into rate fields. This type makes
-- | invalid states unrepresentable by construction.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded (bounded type foundations)
-- |
-- | ## Dependents
-- |
-- | - Hydrogen.Schema.Element.Knob.State (medical knob value)
-- | - Medical dashboard UI components

module Hydrogen.Schema.Medical.Infusion
  ( -- * InfusionRate Type
    InfusionRate(InfusionRate)
  
  -- * Constructors
  , infusionRate
  , safeInfusionRate
  , infusionRateFromNumber
  
  -- * Accessors
  , unwrapInfusionRate
  , toNumber
  
  -- * Predefined Values
  , rateZero
  , rateLow
  , rateMedium
  , rateHigh
  , rateMax
  
  -- * Safety Zone Classification
  , SafetyZone(ZoneSafe, ZoneCaution, ZoneDanger)
  , classifyRate
  , isSafeRate
  , requiresConfirmation
  , safeThreshold
  , cautionThreshold
  
  -- * Operations
  , incrementRate
  , decrementRate
  , setRateClamped
  
  -- * Bounds
  , infusionRateBounds
  , minRate
  , maxRate
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
  , (+)
  , (-)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (<>)
  )

import Prim (Boolean, Int, Number)
import Data.Int (toNumber, round) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // infusion rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | InfusionRate — IV infusion rate in mL/hr.
-- |
-- | Bounded to [0, 999] with integer precision.
-- | This is the atomic type for medical infusion pump controls.
-- |
-- | ## Invariant
-- |
-- | The wrapped Int is ALWAYS in [0, 999]. This is enforced by:
-- | - Smart constructor `infusionRate` clamps at construction
-- | - Safe constructor `safeInfusionRate` returns Maybe
-- | - All operations preserve the invariant
newtype InfusionRate = InfusionRate Int

derive instance eqInfusionRate :: Eq InfusionRate
derive instance ordInfusionRate :: Ord InfusionRate

instance showInfusionRate :: Show InfusionRate where
  show (InfusionRate n) = show n <> " mL/hr"

-- | Create an InfusionRate, clamping to [0, 999].
-- |
-- | ```purescript
-- | infusionRate 120   -- InfusionRate 120
-- | infusionRate 1500  -- InfusionRate 999 (clamped)
-- | infusionRate (-10) -- InfusionRate 0 (clamped)
-- | ```
infusionRate :: Int -> InfusionRate
infusionRate n
  | n < 0 = InfusionRate 0
  | n > 999 = InfusionRate 999
  | otherwise = InfusionRate n

-- | Create an InfusionRate with validation, rejecting out-of-bounds values.
-- |
-- | Returns Nothing for values outside [0, 999].
-- | This is the **secure** constructor — use it at system boundaries.
-- |
-- | ```purescript
-- | safeInfusionRate 120  -- Just (InfusionRate 120)
-- | safeInfusionRate 1500 -- Nothing (exceeds max)
-- | safeInfusionRate (-5) -- Nothing (negative)
-- | ```
safeInfusionRate :: Int -> Maybe InfusionRate
safeInfusionRate n
  | n < 0 = Nothing
  | n > 999 = Nothing
  | otherwise = Just (InfusionRate n)

-- | Create an InfusionRate from a Number, rounding and clamping.
-- |
-- | Handles NaN and Infinity by returning 0 (pump stopped — safe default).
-- |
-- | ```purescript
-- | infusionRateFromNumber 120.5      -- InfusionRate 121 (rounded)
-- | infusionRateFromNumber (1.0/0.0)  -- InfusionRate 0 (Infinity → safe)
-- | infusionRateFromNumber (0.0/0.0)  -- InfusionRate 0 (NaN → safe)
-- | ```
infusionRateFromNumber :: Number -> InfusionRate
infusionRateFromNumber n
  | Bounded.isFiniteNumber n = infusionRate (Int.round n)
  | otherwise = InfusionRate 0  -- NaN/Infinity → pump stopped (safe)

-- | Extract the raw Int value.
unwrapInfusionRate :: InfusionRate -> Int
unwrapInfusionRate (InfusionRate n) = n

-- | Convert to Number for calculations.
toNumber :: InfusionRate -> Number
toNumber (InfusionRate n) = Int.toNumber n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // predefined values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pump stopped (0 mL/hr)
rateZero :: InfusionRate
rateZero = InfusionRate 0

-- | Low infusion rate (50 mL/hr) — maintenance fluids
rateLow :: InfusionRate
rateLow = InfusionRate 50

-- | Medium infusion rate (125 mL/hr) — typical IV fluids
rateMedium :: InfusionRate
rateMedium = InfusionRate 125

-- | High infusion rate (250 mL/hr) — rapid hydration
rateHigh :: InfusionRate
rateHigh = InfusionRate 250

-- | Maximum infusion rate (999 mL/hr)
rateMax :: InfusionRate
rateMax = InfusionRate 999

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // safety zones
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safety zone classification for infusion rates.
-- |
-- | Medical devices must provide clear visual feedback about rate safety:
-- | - Safe: Normal operating range (green indicator)
-- | - Caution: Elevated rate, monitor closely (yellow indicator)
-- | - Danger: High rate, requires confirmation (red indicator)
data SafetyZone
  = ZoneSafe      -- ^ Normal operating range
  | ZoneCaution   -- ^ Elevated, requires monitoring
  | ZoneDanger    -- ^ High rate, requires confirmation

derive instance eqSafetyZone :: Eq SafetyZone
derive instance ordSafetyZone :: Ord SafetyZone

instance showSafetyZone :: Show SafetyZone where
  show ZoneSafe = "safe"
  show ZoneCaution = "caution"
  show ZoneDanger = "danger"

-- | Threshold between safe and caution zones (300 mL/hr).
safeThreshold :: Int
safeThreshold = 300

-- | Threshold between caution and danger zones (600 mL/hr).
cautionThreshold :: Int
cautionThreshold = 600

-- | Classify an infusion rate into its safety zone.
-- |
-- | - 0-300 mL/hr: Safe
-- | - 301-600 mL/hr: Caution
-- | - 601-999 mL/hr: Danger
classifyRate :: InfusionRate -> SafetyZone
classifyRate (InfusionRate n)
  | n <= safeThreshold = ZoneSafe
  | n <= cautionThreshold = ZoneCaution
  | otherwise = ZoneDanger

-- | Is the rate in the safe zone?
isSafeRate :: InfusionRate -> Boolean
isSafeRate rate = case classifyRate rate of
  ZoneSafe -> true
  _ -> false

-- | Does this rate require user confirmation before applying?
-- |
-- | Rates in the danger zone (>600 mL/hr) require explicit confirmation
-- | to prevent accidental high-rate settings.
requiresConfirmation :: InfusionRate -> Boolean
requiresConfirmation rate = case classifyRate rate of
  ZoneDanger -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Increment rate by 1 mL/hr, clamping at maximum.
incrementRate :: InfusionRate -> InfusionRate
incrementRate (InfusionRate n) = infusionRate (n + 1)

-- | Decrement rate by 1 mL/hr, clamping at zero.
decrementRate :: InfusionRate -> InfusionRate
decrementRate (InfusionRate n) = infusionRate (n - 1)

-- | Set rate to a new value, clamping to bounds.
setRateClamped :: Int -> InfusionRate -> InfusionRate
setRateClamped newRate _ = infusionRate newRate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum infusion rate (0 mL/hr — pump stopped).
minRate :: Int
minRate = 0

-- | Maximum infusion rate (999 mL/hr).
maxRate :: Int
maxRate = 999

-- | Bounds documentation for InfusionRate.
-- |
-- | Used for UI generation, JSON schema, and agent understanding.
infusionRateBounds :: Bounded.IntBounds
infusionRateBounds = Bounded.intBounds 0 999 Bounded.Clamps "infusionRate"
  "IV infusion rate in mL/hr (0 = stopped, 999 = maximum)"
