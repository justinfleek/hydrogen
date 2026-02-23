-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // spatial // ior
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | IOR - Index of Refraction for transparent materials.
-- |
-- | Range: 1.0 to 3.0 (clamps)
-- | - **1.0**: No refraction (vacuum, air ≈ 1.0003)
-- | - **1.33**: Water
-- | - **1.5**: Glass (common soda-lime)
-- | - **1.52**: Acrylic
-- | - **2.4**: Diamond
-- | - **3.0**: High-index materials
-- |
-- | Controls how much light bends when entering/exiting a transparent surface.
-- | Used for glass, water, crystals, lenses. Critical for ray tracing.

module Hydrogen.Schema.Spatial.IOR
  ( IOR
  , ior
  , unwrap
  , toNumber
  , bounds
  , air
  , water
  , glass
  , diamond
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ior
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Index of Refraction (1.0 to 3.0)
-- |
-- | Physical property determining light refraction through transparent materials.
newtype IOR = IOR Number

derive instance eqIOR :: Eq IOR
derive instance ordIOR :: Ord IOR

instance showIOR :: Show IOR where
  show (IOR i) = "IOR=" <> show i

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create an IOR value, clamping to 1.0-3.0
ior :: Number -> IOR
ior n = IOR (Bounded.clampNumber 1.0 3.0 n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Air (no refraction)
air :: IOR
air = IOR 1.0

-- | Water
water :: IOR
water = IOR 1.33

-- | Glass (soda-lime)
glass :: IOR
glass = IOR 1.5

-- | Diamond
diamond :: IOR
diamond = IOR 2.42

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: IOR -> Number
unwrap (IOR i) = i

-- | Convert to Number (passthrough for this type)
toNumber :: IOR -> Number
toNumber (IOR i) = i

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 1.0 3.0 "ior" "Index of refraction for transparent materials"
