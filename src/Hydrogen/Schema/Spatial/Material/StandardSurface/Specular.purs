-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // specular
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Specular reflection layer for MaterialX Standard Surface.
-- |
-- | The specular layer provides glossy reflection using GGX microfacet
-- | distribution with Fresnel reflectance based on IOR.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - specular: [0.0, 1.0] default 1.0 — intensity multiplier
-- | - specular_color: RGB default (1,1,1) — tint for dielectrics
-- | - specular_roughness: [0.0, 1.0] default 0.2 — GGX roughness
-- | - specular_IOR: [1.0, 3.0] soft default 1.5 — Fresnel index of refraction
-- | - specular_anisotropy: [0.0, 1.0] default 0.0 — anisotropic stretch
-- | - specular_rotation: [0.0, 1.0] default 0.0 — anisotropy rotation angle

module Hydrogen.Schema.Spatial.Material.StandardSurface.Specular
  ( -- * Specular Layer Type
    Specular
  , specular
  
  -- * Bounded Primitives
  , SpecularWeight
  , SpecularColor
  , SpecularRoughness
  , SpecularIOR
  , SpecularAnisotropy
  , SpecularRotation
  , specularWeight
  , specularColor
  , specularRoughness
  , specularIOR
  , specularAnisotropy
  , specularRotation
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
--                                                     // specular // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specular weight [0.0, 1.0] — controls specular layer contribution.
newtype SpecularWeight = SpecularWeight Number

derive instance eqSpecularWeight :: Eq SpecularWeight
derive instance ordSpecularWeight :: Ord SpecularWeight

instance showSpecularWeight :: Show SpecularWeight where
  show (SpecularWeight n) = "SpecularWeight(" <> show n <> ")"

-- | Construct specular weight, clamping to [0.0, 1.0].
specularWeight :: Number -> SpecularWeight
specularWeight n = SpecularWeight (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // specular // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for specular tinting.
-- |
-- | For dielectrics, this tints the specular reflection.
-- | For conductors, the base_color is used as F0 instead.
type SpecularColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct specular color from RGB values [0.0, 1.0].
specularColor :: Number -> Number -> Number -> SpecularColor
specularColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // specular // roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specular roughness [0.0, 1.0] — GGX microfacet roughness.
-- |
-- | At 0.0, the surface is a perfect mirror.
-- | At 1.0, the reflection is completely diffused.
newtype SpecularRoughness = SpecularRoughness Number

derive instance eqSpecularRoughness :: Eq SpecularRoughness
derive instance ordSpecularRoughness :: Ord SpecularRoughness

instance showSpecularRoughness :: Show SpecularRoughness where
  show (SpecularRoughness n) = "SpecularRoughness(" <> show n <> ")"

-- | Construct specular roughness, clamping to [0.0, 1.0].
specularRoughness :: Number -> SpecularRoughness
specularRoughness n = SpecularRoughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // specular // ior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specular IOR [1.0, 4.0] — Fresnel index of refraction.
-- |
-- | MaterialX soft range is [1.0, 3.0] with default 1.5 (glass).
-- | We allow up to 4.0 for exotic materials like diamond (2.42) with margin.
-- |
-- | Common values:
-- | - Water: 1.33
-- | - Glass: 1.5
-- | - Diamond: 2.42
-- | - Silicon: 3.5
newtype SpecularIOR = SpecularIOR Number

derive instance eqSpecularIOR :: Eq SpecularIOR
derive instance ordSpecularIOR :: Ord SpecularIOR

instance showSpecularIOR :: Show SpecularIOR where
  show (SpecularIOR n) = "SpecularIOR(" <> show n <> ")"

-- | Construct specular IOR, clamping to [1.0, 4.0].
specularIOR :: Number -> SpecularIOR
specularIOR n = SpecularIOR (Bounded.clampNumber 1.0 4.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // specular // anisotropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specular anisotropy [0.0, 1.0] — anisotropic highlight stretch.
-- |
-- | At 0.0, the highlight is isotropic (circular).
-- | At 1.0, the highlight is maximally stretched in one direction.
-- |
-- | Used for brushed metal, hair, and other directional surfaces.
newtype SpecularAnisotropy = SpecularAnisotropy Number

derive instance eqSpecularAnisotropy :: Eq SpecularAnisotropy
derive instance ordSpecularAnisotropy :: Ord SpecularAnisotropy

instance showSpecularAnisotropy :: Show SpecularAnisotropy where
  show (SpecularAnisotropy n) = "SpecularAnisotropy(" <> show n <> ")"

-- | Construct specular anisotropy, clamping to [0.0, 1.0].
specularAnisotropy :: Number -> SpecularAnisotropy
specularAnisotropy n = SpecularAnisotropy (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // specular // rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specular rotation [0.0, 1.0] — anisotropy orientation.
-- |
-- | Rotates the anisotropic highlight direction.
-- | 0.0 = 0 degrees, 0.5 = 90 degrees, 1.0 = 180 degrees (wraps).
newtype SpecularRotation = SpecularRotation Number

derive instance eqSpecularRotation :: Eq SpecularRotation
derive instance ordSpecularRotation :: Ord SpecularRotation

instance showSpecularRotation :: Show SpecularRotation where
  show (SpecularRotation n) = "SpecularRotation(" <> show n <> ")"

-- | Construct specular rotation, clamping to [0.0, 1.0].
specularRotation :: Number -> SpecularRotation
specularRotation n = SpecularRotation (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // specular // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete specular layer configuration.
-- |
-- | The specular layer provides glossy reflection on top of the base layer.
-- | It uses GGX distribution with Smith geometry and Fresnel based on IOR.
type Specular =
  { weight :: SpecularWeight
  , color :: SpecularColor
  , roughness :: SpecularRoughness
  , ior :: SpecularIOR
  , anisotropy :: SpecularAnisotropy
  , rotation :: SpecularRotation
  }

-- | Construct a specular layer with all parameters.
specular :: Number -> SpecularColor -> Number -> Number -> Number -> Number -> Specular
specular w c r i a rot =
  { weight: specularWeight w
  , color: c
  , roughness: specularRoughness r
  , ior: specularIOR i
  , anisotropy: specularAnisotropy a
  , rotation: specularRotation rot
  }
