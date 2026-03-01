-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete MaterialX Standard Surface type composition.
-- |
-- | This module combines all layer types into the complete StandardSurface
-- | material definition, along with constructors and the default surface.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents generate materials, they compose from these bounded primitives.
-- | Same parameters = same rendered pixels, guaranteed. No ambiguity about
-- | what "metalness 0.8" means — it's the same across every renderer.

module Hydrogen.Schema.Spatial.Material.StandardSurface.Types
  ( -- * Complete Material Type
    StandardSurface
  , standardSurface
  , defaultSurface
  ) where

import Hydrogen.Schema.Spatial.Material.StandardSurface.Base
  ( Base
  , base
  , baseColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Specular
  ( Specular
  , specular
  , specularColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Transmission
  ( Transmission
  , transmission
  , transmissionColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Subsurface
  ( Subsurface
  , subsurface
  , subsurfaceColor
  , subsurfaceRadius
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Sheen
  ( Sheen
  , sheen
  , sheenColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Coat
  ( Coat
  , coat
  , coatColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.ThinFilm
  ( ThinFilm
  , thinFilm
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Emission
  ( Emission
  , emission
  , emissionColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Geometry
  ( Geometry
  , geometry
  , opacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // standard surface // complete
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete MaterialX Standard Surface material.
-- |
-- | This is the full PBR material definition matching MaterialX 1.39 spec.
-- | All parameters have physically plausible bounds enforced at construction.
-- |
-- | ## Layer Composition
-- |
-- | The layers are evaluated in this order (bottom to top):
-- | 1. Base (diffuse/metallic)
-- | 2. Subsurface (modifies base)
-- | 3. Specular (on top of base)
-- | 4. Transmission (replaces diffuse for glass)
-- | 5. Sheen (additive at grazing angles)
-- | 6. Coat (secondary specular layer)
-- | 7. Thin Film (modifies specular)
-- | 8. Emission (additive glow)
-- | 9. Geometry (opacity mask)
type StandardSurface =
  { base :: Base
  , specular :: Specular
  , transmission :: Transmission
  , subsurface :: Subsurface
  , sheen :: Sheen
  , coat :: Coat
  , thinFilm :: ThinFilm
  , emission :: Emission
  , geometry :: Geometry
  }

-- | Create a custom StandardSurface with all parameters.
-- |
-- | For common materials, prefer the preset functions (plastic, metal, glass,
-- | skin, fabric, carPaint) which configure sensible defaults.
standardSurface
  :: Base
  -> Specular
  -> Transmission
  -> Subsurface
  -> Sheen
  -> Coat
  -> ThinFilm
  -> Emission
  -> Geometry
  -> StandardSurface
standardSurface b sp tr ss sh co tf em ge =
  { base: b
  , specular: sp
  , transmission: tr
  , subsurface: ss
  , sheen: sh
  , coat: co
  , thinFilm: tf
  , emission: em
  , geometry: ge
  }

-- | Default surface — matte white plastic.
-- |
-- | MaterialX default values:
-- | - base: 0.8, color: (1,1,1), diffuse_roughness: 0
-- | - metalness: 0
-- | - specular: 1.0, color: (1,1,1), roughness: 0.2, IOR: 1.5
-- | - All other layers: weight 0 (disabled)
-- |
-- | This is the canonical starting point for material authoring.
defaultSurface :: StandardSurface
defaultSurface =
  { base: base 0.8 (baseColor 1.0 1.0 1.0) 0.0 0.0
  , specular: specular 1.0 (specularColor 1.0 1.0 1.0) 0.2 1.5 0.0 0.0
  , transmission: transmission 0.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.0 (subsurfaceColor 1.0 1.0 1.0) (subsurfaceRadius 1.0 1.0 1.0) 1.0 0.0
  , sheen: sheen 0.0 (sheenColor 1.0 1.0 1.0) 0.3
  , coat: coat 0.0 (coatColor 1.0 1.0 1.0) 0.1 0.0 0.0 1.5 0.0 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }
