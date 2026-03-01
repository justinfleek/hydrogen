-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brush // pressure // atoms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pressure Atoms — Bounded numeric parameters for pressure dynamics.
-- |
-- | ## Design Philosophy
-- |
-- | Pressure values are normalized to [0.0, 1.0] for device independence.
-- | PressureMin and PressureMax define the effective pressure range, allowing
-- | users to customize sensitivity without raw device calibration.
-- |
-- | ## Key Properties
-- |
-- | - **Pressure**: Normalized pressure value (0.0-1.0)
-- | - **PressureMin**: Minimum effective pressure threshold (0.0-1.0)
-- | - **PressureMax**: Maximum effective pressure threshold (0.0-1.0)
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Bounded

module Hydrogen.Schema.Brush.Pressure.Atoms
  ( -- * Pressure (0.0-1.0)
    Pressure(..)
  , pressure
  , pressureBounds
  , unwrapPressure
  , noPressure
  , halfPressure
  , fullPressure
  , pressureDebugInfo
  
  -- * PressureMin (0.0-1.0)
  , PressureMin(..)
  , pressureMin
  , pressureMinBounds
  , unwrapPressureMin
  , defaultPressureMin
  , pressureMinDebugInfo
  
  -- * PressureMax (0.0-1.0)
  , PressureMax(..)
  , pressureMax
  , pressureMaxBounds
  , unwrapPressureMax
  , defaultPressureMax
  , pressureMaxDebugInfo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // pressure
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized pressure value (0.0-1.0).
-- | 0.0 = no pressure (pen lifted or barely touching)
-- | 1.0 = maximum pressure (full force applied)
newtype Pressure = Pressure Number

derive instance eqPressure :: Eq Pressure
derive instance ordPressure :: Ord Pressure

instance showPressure :: Show Pressure where
  show (Pressure p) = "(Pressure " <> show p <> ")"

-- | Bounded specification for pressure.
pressureBounds :: Bounded.NumberBounds
pressureBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "pressure" "Normalized pressure value (0.0-1.0)"

-- | Create a pressure value (clamped to 0.0-1.0).
pressure :: Number -> Pressure
pressure n = Pressure (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw pressure value.
unwrapPressure :: Pressure -> Number
unwrapPressure (Pressure p) = p

-- | No pressure (0.0).
noPressure :: Pressure
noPressure = Pressure 0.0

-- | Half pressure (0.5).
halfPressure :: Pressure
halfPressure = Pressure 0.5

-- | Full pressure (1.0).
fullPressure :: Pressure
fullPressure = Pressure 1.0

-- | Debug info string for pressure.
pressureDebugInfo :: Pressure -> String
pressureDebugInfo p = show p <> " raw:" <> show (unwrapPressure p)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pressure min
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum effective pressure threshold (0.0-1.0).
-- | Pressure values below this are treated as zero.
-- | Useful for filtering out unintentional light touches.
newtype PressureMin = PressureMin Number

derive instance eqPressureMin :: Eq PressureMin
derive instance ordPressureMin :: Ord PressureMin

instance showPressureMin :: Show PressureMin where
  show (PressureMin p) = "(PressureMin " <> show p <> ")"

-- | Bounded specification for pressure minimum.
pressureMinBounds :: Bounded.NumberBounds
pressureMinBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "pressureMin" "Minimum effective pressure threshold (0.0-1.0)"

-- | Create a pressure minimum value (clamped to 0.0-1.0).
pressureMin :: Number -> PressureMin
pressureMin n = PressureMin (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw pressure minimum value.
unwrapPressureMin :: PressureMin -> Number
unwrapPressureMin (PressureMin p) = p

-- | Default pressure minimum (0.0 = no threshold).
defaultPressureMin :: PressureMin
defaultPressureMin = PressureMin 0.0

-- | Debug info string for pressure minimum.
pressureMinDebugInfo :: PressureMin -> String
pressureMinDebugInfo p = show p <> " threshold:" <> show (unwrapPressureMin p)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // pressure max
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum effective pressure threshold (0.0-1.0).
-- | Pressure values above this are treated as maximum.
-- | Useful for limiting required force on sensitive styluses.
newtype PressureMax = PressureMax Number

derive instance eqPressureMax :: Eq PressureMax
derive instance ordPressureMax :: Ord PressureMax

instance showPressureMax :: Show PressureMax where
  show (PressureMax p) = "(PressureMax " <> show p <> ")"

-- | Bounded specification for pressure maximum.
pressureMaxBounds :: Bounded.NumberBounds
pressureMaxBounds = Bounded.numberBounds 0.0 1.0 Bounded.Clamps
  "pressureMax" "Maximum effective pressure threshold (0.0-1.0)"

-- | Create a pressure maximum value (clamped to 0.0-1.0).
pressureMax :: Number -> PressureMax
pressureMax n = PressureMax (Bounded.clampNumber 0.0 1.0 n)

-- | Extract the raw pressure maximum value.
unwrapPressureMax :: PressureMax -> Number
unwrapPressureMax (PressureMax p) = p

-- | Default pressure maximum (1.0 = no limit).
defaultPressureMax :: PressureMax
defaultPressureMax = PressureMax 1.0

-- | Debug info string for pressure maximum.
pressureMaxDebugInfo :: PressureMax -> String
pressureMaxDebugInfo p = show p <> " limit:" <> show (unwrapPressureMax p)
