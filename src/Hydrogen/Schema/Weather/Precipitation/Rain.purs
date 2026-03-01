-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // weather // precipitation // rain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rain droplet primitives.
-- |
-- | ## Physical Bounds
-- |
-- | Raindrop diameter in mm [0.1, 8.0]:
-- | - Minimum 0.1: Below this is mist/fog (suspended, not falling)
-- | - Maximum 8.0: Drops break up above ~6mm due to drag; 8mm is theoretical max
-- |
-- | Marshall-Palmer distribution describes typical drop size distributions.

module Hydrogen.Schema.Weather.Precipitation.Rain
  ( -- * Droplet Diameter
    DropletDiameter
  , dropletDiameter
  , dropletDiameterUnsafe
  , unwrapDroplet
  , dropletBounds
  , millimeters
  
  -- * Constants
  , dropletMist
  , dropletDrizzle
  , dropletLight
  , dropletModerate
  , dropletHeavy
  
  -- * Operations
  , terminalVelocity
  , impactEnergy
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (/)
  , (<>)
  )

import Data.Number (sqrt) as Number
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // droplet // diameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raindrop diameter in mm [0.1, 8.0].
newtype DropletDiameter = DropletDiameter Number

derive instance eqDropletDiameter :: Eq DropletDiameter
derive instance ordDropletDiameter :: Ord DropletDiameter

instance showDropletDiameter :: Show DropletDiameter where
  show (DropletDiameter n) = "DropletDiameter " <> show n <> " mm"

-- | Safe constructor with clamping.
dropletDiameter :: Number -> DropletDiameter
dropletDiameter n = DropletDiameter (Bounded.clampNumber 0.1 8.0 n)

-- | Unsafe constructor for known-valid values.
dropletDiameterUnsafe :: Number -> DropletDiameter
dropletDiameterUnsafe = DropletDiameter

-- | Extract raw value.
unwrapDroplet :: DropletDiameter -> Number
unwrapDroplet (DropletDiameter n) = n

-- | Valid bounds documentation.
dropletBounds :: Bounded.NumberBounds
dropletBounds = Bounded.numberBounds 0.1 8.0 Bounded.Clamps "dropletDiameter" "Raindrop diameter in mm"

-- | Get diameter in millimeters (identity).
millimeters :: DropletDiameter -> Number
millimeters = unwrapDroplet

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mist droplet (0.15 mm).
dropletMist :: DropletDiameter
dropletMist = DropletDiameter 0.15

-- | Drizzle droplet (0.4 mm).
dropletDrizzle :: DropletDiameter
dropletDrizzle = DropletDiameter 0.4

-- | Light rain droplet (1.0 mm).
dropletLight :: DropletDiameter
dropletLight = DropletDiameter 1.0

-- | Moderate rain droplet (2.5 mm).
dropletModerate :: DropletDiameter
dropletModerate = DropletDiameter 2.5

-- | Heavy rain droplet (4.0 mm).
dropletHeavy :: DropletDiameter
dropletHeavy = DropletDiameter 4.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimate terminal velocity in m/s for a raindrop.
-- |
-- | Uses simplified formula: v ≈ 4.5 × sqrt(d)
-- | where d is diameter in mm.
-- |
-- | Valid for d in [0.5, 6] mm, returns ~2-9 m/s.
terminalVelocity :: DropletDiameter -> Number
terminalVelocity (DropletDiameter d) =
  let v = 4.5 * Number.sqrt d
  in Bounded.clampNumber 0.5 10.0 v

-- | Estimate impact energy in millijoules for a raindrop.
-- |
-- | E = 0.5 × m × v²
-- | m = (4/3) × π × r³ × ρ_water
impactEnergy :: DropletDiameter -> Number
impactEnergy (DropletDiameter d) =
  let r = d / 2000.0  -- radius in meters
      volume = 4.0 / 3.0 * 3.14159 * r * r * r  -- m³
      mass = volume * 1000.0  -- kg (water density)
      v = terminalVelocity (DropletDiameter d)
  in 0.5 * mass * v * v * 1000.0  -- Convert J to mJ
