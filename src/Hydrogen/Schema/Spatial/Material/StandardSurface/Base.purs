-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // base
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Base diffuse layer for MaterialX Standard Surface.
-- |
-- | The base layer provides the primary diffuse reflection using Oren-Nayar
-- | microfacet model. It also controls the metalness blend between dielectric
-- | and conductor behavior.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - base: [0.0, 1.0] default 0.8 — weight/intensity multiplier
-- | - base_color: RGB [0,0,0]-[1,1,1] default (1,1,1) — diffuse albedo
-- | - diffuse_roughness: [0.0, 1.0] default 0.0 — Oren-Nayar roughness
-- | - metalness: [0.0, 1.0] default 0.0 — dielectric (0) to conductor (1)

module Hydrogen.Schema.Spatial.Material.StandardSurface.Base
  ( -- * Base Layer Type
    Base
  , base
  
  -- * Bounded Primitives
  , BaseWeight
  , BaseColor
  , DiffuseRoughness
  , Metalness
  , baseWeight
  , baseColor
  , diffuseRoughness
  , metalness
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Spatial.Material.StandardSurface.Core
  ( ColorChannel
  , colorChannel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bounded // weights
-- ═════════════════════════════════════════════════════════════════════════════

-- | Base weight [0.0, 1.0] — controls base layer contribution.
-- |
-- | At 0.0, the base layer contributes nothing to the final material.
-- | At 1.0, the base layer contributes at full intensity.
newtype BaseWeight = BaseWeight Number

derive instance eqBaseWeight :: Eq BaseWeight
derive instance ordBaseWeight :: Ord BaseWeight

instance showBaseWeight :: Show BaseWeight where
  show (BaseWeight n) = "BaseWeight(" <> show n <> ")"

-- | Construct a base weight, clamping to [0.0, 1.0].
baseWeight :: Number -> BaseWeight
baseWeight n = BaseWeight (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // base // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for the base diffuse layer.
type BaseColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct a base color from RGB values [0.0, 1.0].
baseColor :: Number -> Number -> Number -> BaseColor
baseColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // diffuse // roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Diffuse roughness [0.0, 1.0] — Oren-Nayar microfacet roughness.
-- |
-- | At 0.0, the surface is perfectly Lambertian (uniform scattering).
-- | At 1.0, the surface exhibits strong retroreflection like the moon.
newtype DiffuseRoughness = DiffuseRoughness Number

derive instance eqDiffuseRoughness :: Eq DiffuseRoughness
derive instance ordDiffuseRoughness :: Ord DiffuseRoughness

instance showDiffuseRoughness :: Show DiffuseRoughness where
  show (DiffuseRoughness n) = "DiffuseRoughness(" <> show n <> ")"

-- | Construct diffuse roughness, clamping to [0.0, 1.0].
diffuseRoughness :: Number -> DiffuseRoughness
diffuseRoughness n = DiffuseRoughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // metalness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metalness [0.0, 1.0] — dielectric to conductor blend.
-- |
-- | At 0.0, the material is a dielectric (plastic, glass, skin).
-- | At 1.0, the material is a conductor (gold, copper, aluminum).
-- |
-- | Metalness affects how the base color is interpreted:
-- | - Dielectric: base_color is diffuse albedo
-- | - Conductor: base_color is specular reflectance (F0)
newtype Metalness = Metalness Number

derive instance eqMetalness :: Eq Metalness
derive instance ordMetalness :: Ord Metalness

instance showMetalness :: Show Metalness where
  show (Metalness n) = "Metalness(" <> show n <> ")"

-- | Construct metalness, clamping to [0.0, 1.0].
metalness :: Number -> Metalness
metalness n = Metalness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // base // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete base layer configuration.
-- |
-- | The base layer is always present and provides the foundation for the
-- | material. Other layers (specular, coat, sheen, etc.) are applied on top.
type Base =
  { weight :: BaseWeight
  , color :: BaseColor
  , diffuseRoughness :: DiffuseRoughness
  , metalness :: Metalness
  }

-- | Construct a base layer with all parameters.
base :: Number -> BaseColor -> Number -> Number -> Base
base w c dr m =
  { weight: baseWeight w
  , color: c
  , diffuseRoughness: diffuseRoughness dr
  , metalness: metalness m
  }
