-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--      // hydrogen // schema // physical // mechanical // density // operations
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Operations on Density values.
-- |
-- | Provides comparison, interpolation, and physical queries.

module Hydrogen.Schema.Physical.Mechanical.Density.Operations
  ( isLighterThan
  , floatsIn
  , relativeToWater
  , lerp
  ) where

import Prelude
  ( (-)
  , (*)
  , (/)
  , (<)
  , (+)
  )

import Hydrogen.Schema.Physical.Mechanical.Density.Types 
  ( Density
  , unwrap
  , densityUnsafe
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if material A is lighter than material B.
isLighterThan :: Density -> Density -> Boolean
isLighterThan a b = unwrap a < unwrap b

-- | Check if a solid would float in a given liquid.
-- |
-- | An object floats if its density is less than the liquid's density.
floatsIn :: Density -> Density -> Boolean
floatsIn solid liquid = isLighterThan solid liquid

-- | Get density relative to water (specific gravity).
-- |
-- | Water = 1.0, iron ≈ 7.87, air ≈ 0.0012
relativeToWater :: Density -> Number
relativeToWater d = unwrap d / 1000.0

-- | Linear interpolation between two density values.
lerp :: Number -> Density -> Density -> Density
lerp t a b =
  densityUnsafe (unwrap a + t * (unwrap b - unwrap a))
