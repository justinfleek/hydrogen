-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // subsurface
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Subsurface scattering layer for MaterialX Standard Surface.
-- |
-- | The subsurface layer provides volumetric light scattering for translucent
-- | materials like skin, wax, marble, and milk. Light enters the surface,
-- | scatters internally, and exits at a different point.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - subsurface: [0.0, 1.0] default 0.0 — SSS weight (blend with diffuse)
-- | - subsurface_color: RGB default (1,1,1) — scattering color
-- | - subsurface_radius: RGB default (1,1,1) — mean free path per channel
-- | - subsurface_scale: [0.0, inf) default 1.0 — radius multiplier
-- | - subsurface_anisotropy: [-1.0, 1.0] default 0.0 — scattering direction

module Hydrogen.Schema.Spatial.Material.StandardSurface.Subsurface
  ( -- * Subsurface Layer Type
    Subsurface
  , subsurface
  
  -- * Bounded Primitives
  , SubsurfaceWeight
  , SubsurfaceColor
  , SubsurfaceRadius
  , SubsurfaceScale
  , SubsurfaceAnisotropy
  , subsurfaceWeight
  , subsurfaceColor
  , subsurfaceRadius
  , subsurfaceScale
  , subsurfaceAnisotropy
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Spatial.Material.StandardSurface.Core
  ( ColorChannel
  , colorChannel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // subsurface // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subsurface weight [0.0, 1.0] — blend between diffuse and SSS.
-- |
-- | At 0.0, the base layer uses pure diffuse reflection.
-- | At 1.0, the base layer uses pure subsurface scattering.
newtype SubsurfaceWeight = SubsurfaceWeight Number

derive instance eqSubsurfaceWeight :: Eq SubsurfaceWeight
derive instance ordSubsurfaceWeight :: Ord SubsurfaceWeight

instance showSubsurfaceWeight :: Show SubsurfaceWeight where
  show (SubsurfaceWeight n) = "SubsurfaceWeight(" <> show n <> ")"

-- | Construct subsurface weight, clamping to [0.0, 1.0].
subsurfaceWeight :: Number -> SubsurfaceWeight
subsurfaceWeight n = SubsurfaceWeight (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // subsurface // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for subsurface scattering.
-- |
-- | This is the color of light that scatters through the material.
-- | For skin, this is typically warm red/orange tones.
type SubsurfaceColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct subsurface color from RGB values [0.0, 1.0].
subsurfaceColor :: Number -> Number -> Number -> SubsurfaceColor
subsurfaceColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // subsurface // radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subsurface radius per channel — mean free path in normalized units.
-- |
-- | Each channel (R, G, B) has its own scattering distance. For skin:
-- | - Red scatters furthest (blood carries light deep)
-- | - Green scatters medium distance
-- | - Blue scatters shortest (absorbed quickly)
-- |
-- | Typical skin values: (1.0, 0.35, 0.15) — red travels 3x further than blue.
type SubsurfaceRadius = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct subsurface radius from RGB values [0.0, 1.0].
subsurfaceRadius :: Number -> Number -> Number -> SubsurfaceRadius
subsurfaceRadius r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // subsurface // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subsurface scale [0.0, 100.0] — radius multiplier.
-- |
-- | Scales all radius values by this factor. Useful for adapting materials
-- | to different scene scales without changing the relative channel ratios.
-- |
-- | We clamp to 100.0 as a reasonable maximum for scene-scale materials.
newtype SubsurfaceScale = SubsurfaceScale Number

derive instance eqSubsurfaceScale :: Eq SubsurfaceScale
derive instance ordSubsurfaceScale :: Ord SubsurfaceScale

instance showSubsurfaceScale :: Show SubsurfaceScale where
  show (SubsurfaceScale n) = "SubsurfaceScale(" <> show n <> ")"

-- | Construct subsurface scale, clamping to [0.0, 100.0].
subsurfaceScale :: Number -> SubsurfaceScale
subsurfaceScale n = SubsurfaceScale (Bounded.clampNumber 0.0 100.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // subsurface // anisotropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subsurface anisotropy [-1.0, 1.0] — scattering direction bias.
-- |
-- | Controls the Henyey-Greenstein phase function:
-- | - -1.0: Strongly backward scattering
-- |   0.0: Isotropic scattering (equal in all directions)
-- |   1.0: Strongly forward scattering
-- |
-- | Most organic materials are slightly forward-scattering (0.0 to 0.3).
newtype SubsurfaceAnisotropy = SubsurfaceAnisotropy Number

derive instance eqSubsurfaceAnisotropy :: Eq SubsurfaceAnisotropy
derive instance ordSubsurfaceAnisotropy :: Ord SubsurfaceAnisotropy

instance showSubsurfaceAnisotropy :: Show SubsurfaceAnisotropy where
  show (SubsurfaceAnisotropy n) = "SubsurfaceAnisotropy(" <> show n <> ")"

-- | Construct subsurface anisotropy, clamping to [-1.0, 1.0].
subsurfaceAnisotropy :: Number -> SubsurfaceAnisotropy
subsurfaceAnisotropy n = SubsurfaceAnisotropy (Bounded.clampNumber (negate 1.0) 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // subsurface // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete subsurface scattering layer configuration.
-- |
-- | For skin, wax, marble, jade, milk, and other translucent materials.
-- | The subsurface layer modifies the base diffuse to include volumetric
-- | scattering effects.
type Subsurface =
  { weight :: SubsurfaceWeight
  , color :: SubsurfaceColor
  , radius :: SubsurfaceRadius
  , scale :: SubsurfaceScale
  , anisotropy :: SubsurfaceAnisotropy
  }

-- | Construct a subsurface layer with all parameters.
subsurface :: Number -> SubsurfaceColor -> SubsurfaceRadius -> Number -> Number -> Subsurface
subsurface w c rad sc a =
  { weight: subsurfaceWeight w
  , color: c
  , radius: rad
  , scale: subsurfaceScale sc
  , anisotropy: subsurfaceAnisotropy a
  }
