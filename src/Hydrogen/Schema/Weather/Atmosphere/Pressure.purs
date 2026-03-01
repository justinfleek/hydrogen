-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // weather // atmosphere // pressure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Barometric pressure primitives for atmospheric measurement.
-- |
-- | ## Physical Bounds
-- |
-- | Pressure (sea level):
-- | - Record low: ~870 hPa (typhoon center)
-- | - Record high: ~1085 hPa (Siberian high)
-- | - Standard: 1013.25 hPa
-- | - Practical range: 300-1100 hPa (includes high altitude)
-- |
-- | hPa (hectopascal) = mbar (millibar) — interchangeable.

module Hydrogen.Schema.Weather.Atmosphere.Pressure
  ( -- * Pressure Type
    Pressure
  , pressure
  , pressureUnsafe
  , unwrapPressure
  , pressureBounds
  
  -- * Unit Conversions
  , hectopascals
  , millibars
  , atmospheres
  , inchesOfMercury
  , mmOfMercury
  
  -- * Constants
  , pressureStandard
  , pressureRecordLow
  , pressureRecordHigh
  , pressureEverest
  , pressureDeadSea
  
  -- * Operations
  , pressureAltitude
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Number (pow) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pressure
-- ═════════════════════════════════════════════════════════════════════════════

-- | Atmospheric pressure in hPa [300, 1100].
-- |
-- | ## Bounds Rationale
-- |
-- | - Minimum 300 hPa: ~9000m altitude, above Everest summit
-- | - Maximum 1100 hPa: Above highest recorded sea-level pressure
-- |
-- | hPa (hectopascal) = mbar (millibar) — interchangeable.
newtype Pressure = Pressure Number

derive instance eqPressure :: Eq Pressure
derive instance ordPressure :: Ord Pressure

instance showPressure :: Show Pressure where
  show (Pressure n) = "Pressure " <> show n <> " hPa"

-- | Safe constructor with clamping.
pressure :: Number -> Pressure
pressure n = Pressure (Bounded.clampNumber 300.0 1100.0 n)

-- | Unsafe constructor for known-valid values.
pressureUnsafe :: Number -> Pressure
pressureUnsafe = Pressure

-- | Extract raw value.
unwrapPressure :: Pressure -> Number
unwrapPressure (Pressure n) = n

-- | Valid bounds documentation.
pressureBounds :: Bounded.NumberBounds
pressureBounds = Bounded.numberBounds 300.0 1100.0 Bounded.Clamps "pressure" "Atmospheric pressure in hPa"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // unit // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get pressure in hectopascals (identity).
hectopascals :: Pressure -> Number
hectopascals = unwrapPressure

-- | Get pressure in millibars (same as hPa).
millibars :: Pressure -> Number
millibars = unwrapPressure

-- | Convert to atmospheres.
atmospheres :: Pressure -> Number
atmospheres (Pressure p) = p / 1013.25

-- | Convert to inches of mercury.
inchesOfMercury :: Pressure -> Number
inchesOfMercury (Pressure p) = p * 0.02953

-- | Convert to mm of mercury.
mmOfMercury :: Pressure -> Number
mmOfMercury (Pressure p) = p * 0.75006

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard sea-level pressure (1013.25 hPa).
pressureStandard :: Pressure
pressureStandard = Pressure 1013.25

-- | Record low (typhoon center, ~870 hPa).
pressureRecordLow :: Pressure
pressureRecordLow = Pressure 870.0

-- | Record high (Siberian anticyclone, ~1085 hPa).
pressureRecordHigh :: Pressure
pressureRecordHigh = Pressure 1085.0

-- | Mt. Everest summit (~337 hPa).
pressureEverest :: Pressure
pressureEverest = Pressure 337.0

-- | Dead Sea (below sea level, ~1065 hPa).
pressureDeadSea :: Pressure
pressureDeadSea = Pressure 1065.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate pressure altitude in meters.
-- |
-- | h = 44330 × (1 - (P / P₀)^0.1903)
pressureAltitude :: Pressure -> Number
pressureAltitude (Pressure p) =
  44330.0 * (1.0 - Number.pow (p / 1013.25) 0.1903)
