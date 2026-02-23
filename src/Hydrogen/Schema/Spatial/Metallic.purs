-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // spatial // metallic
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Metallic - metallic factor for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Dielectric (non-metal: plastic, wood, fabric, skin)
-- | - **0.5**: Partial (oxidized metal, hybrid materials)
-- | - **1.0**: Pure metal (gold, steel, aluminum)
-- |
-- | Controls whether a surface follows metal or dielectric BRDF in PBR shading.
-- | Metals have no diffuse reflection and colored specular (Fresnel F0 from albedo).
-- | Dielectrics have diffuse+specular with achromatic reflections (F0 ≈ 0.04).

module Hydrogen.Schema.Spatial.Metallic
  ( Metallic
  , metallic
  , unwrap
  , toNumber
  , bounds
  , dielectric
  , partial
  , metal
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // metallic
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Metallic factor for PBR (0.0 to 1.0)
-- |
-- | 0 = dielectric (non-metal), 1 = pure metal. Affects Fresnel and energy conservation.
newtype Metallic = Metallic Number

derive instance eqMetallic :: Eq Metallic
derive instance ordMetallic :: Ord Metallic

instance showMetallic :: Show Metallic where
  show (Metallic m) = show m

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a metallic value, clamping to 0.0-1.0
metallic :: Number -> Metallic
metallic n = Metallic (Bounded.clampNumber 0.0 1.0 n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dielectric (non-metal)
dielectric :: Metallic
dielectric = Metallic 0.0

-- | Partial metallic (oxidized, hybrid)
partial :: Metallic
partial = Metallic 0.5

-- | Pure metal
metal :: Metallic
metal = Metallic 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Metallic -> Number
unwrap (Metallic m) = m

-- | Convert to Number (passthrough for this type)
toNumber :: Metallic -> Number
toNumber (Metallic m) = m

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "metallic" "PBR metallic factor (dielectric to metal)"
