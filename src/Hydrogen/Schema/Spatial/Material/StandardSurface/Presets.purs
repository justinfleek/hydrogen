-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Preset materials for common surface types.
-- |
-- | These presets provide physically-accurate starting points for common
-- | material categories. Each preset configures the Standard Surface layers
-- | with values derived from real-world material measurements.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Red plastic
-- | redPlastic = plastic (baseColor 0.8 0.1 0.1)
-- |
-- | -- Brushed gold
-- | brushedGold = metal (baseColor 1.0 0.76 0.33) 0.3
-- |
-- | -- Clear glass
-- | clearGlass = glass 1.5 0.0
-- | ```

module Hydrogen.Schema.Spatial.Material.StandardSurface.Presets
  ( -- * Material Presets
    plastic
  , metal
  , glass
  , skin
  , fabric
  , carPaint
  ) where

import Hydrogen.Schema.Spatial.Material.StandardSurface.Types
  ( StandardSurface
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Base
  ( BaseColor
  , base
  , baseColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Specular
  ( specular
  , specularColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Transmission
  ( transmission
  , transmissionColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Subsurface
  ( SubsurfaceColor
  , subsurface
  , subsurfaceColor
  , subsurfaceRadius
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Sheen
  ( SheenColor
  , sheen
  , sheenColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Coat
  ( CoatColor
  , coat
  , coatColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.ThinFilm
  ( thinFilm
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Emission
  ( emission
  , emissionColor
  )
import Hydrogen.Schema.Spatial.Material.StandardSurface.Geometry
  ( geometry
  , opacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // plastic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Plastic — smooth dielectric with moderate specular.
-- |
-- | A general-purpose plastic material with:
-- | - Full diffuse contribution (base 0.8)
-- | - Moderate specular (0.5 weight, IOR 1.5)
-- | - Slight roughness (0.35) for realistic appearance
-- |
-- | Suitable for: toys, consumer electronics, kitchenware, furniture.
plastic :: BaseColor -> StandardSurface
plastic color =
  { base: base 0.8 color 0.0 0.0
  , specular: specular 0.5 (specularColor 1.0 1.0 1.0) 0.35 1.5 0.0 0.0
  , transmission: transmission 0.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.0 (subsurfaceColor 1.0 1.0 1.0) (subsurfaceRadius 1.0 1.0 1.0) 1.0 0.0
  , sheen: sheen 0.0 (sheenColor 1.0 1.0 1.0) 0.3
  , coat: coat 0.0 (coatColor 1.0 1.0 1.0) 0.1 0.0 0.0 1.5 0.0 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // metal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metal — fully metallic with base color as reflectance.
-- |
-- | A conductor material where:
-- | - Base color defines the specular reflectance (F0)
-- | - Full metalness (1.0)
-- | - Configurable roughness for polish vs brushed finish
-- |
-- | Common base colors:
-- | - Gold: (1.0, 0.76, 0.33)
-- | - Copper: (0.95, 0.64, 0.54)
-- | - Aluminum: (0.91, 0.92, 0.92)
-- | - Iron: (0.56, 0.57, 0.58)
metal :: BaseColor -> Number -> StandardSurface
metal color roughnessVal =
  { base: base 1.0 color 0.0 1.0
  , specular: specular 1.0 (specularColor 1.0 1.0 1.0) roughnessVal 1.5 0.0 0.0
  , transmission: transmission 0.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.0 (subsurfaceColor 1.0 1.0 1.0) (subsurfaceRadius 1.0 1.0 1.0) 1.0 0.0
  , sheen: sheen 0.0 (sheenColor 1.0 1.0 1.0) 0.3
  , coat: coat 0.0 (coatColor 1.0 1.0 1.0) 0.1 0.0 0.0 1.5 0.0 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // glass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glass — transparent dielectric with high transmission.
-- |
-- | A refractive material where:
-- | - No diffuse contribution (base 0.0)
-- | - Full transmission (1.0)
-- | - Configurable IOR and roughness
-- |
-- | Common IOR values:
-- | - Water: 1.33
-- | - Glass: 1.5
-- | - Crystal: 1.8
-- | - Diamond: 2.42
glass :: Number -> Number -> StandardSurface
glass iorVal roughnessVal =
  { base: base 0.0 (baseColor 1.0 1.0 1.0) 0.0 0.0
  , specular: specular 1.0 (specularColor 1.0 1.0 1.0) roughnessVal iorVal 0.0 0.0
  , transmission: transmission 1.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.0 (subsurfaceColor 1.0 1.0 1.0) (subsurfaceRadius 1.0 1.0 1.0) 1.0 0.0
  , sheen: sheen 0.0 (sheenColor 1.0 1.0 1.0) 0.3
  , coat: coat 0.0 (coatColor 1.0 1.0 1.0) 0.1 0.0 0.0 1.5 0.0 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // skin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Skin — subsurface scattering for realistic human skin.
-- |
-- | A translucent organic material with:
-- | - Moderate SSS (0.6 weight)
-- | - Wavelength-dependent scattering (red > green > blue)
-- | - Subtle specular (0.3) with low IOR (1.4)
-- |
-- | The subsurface radius (1.0, 0.35, 0.15) models how:
-- | - Red light (blood) scatters deep into tissue
-- | - Green light scatters medium distance
-- | - Blue light is absorbed quickly
skin :: BaseColor -> SubsurfaceColor -> StandardSurface
skin baseCol sssCol =
  { base: base 0.8 baseCol 0.0 0.0
  , specular: specular 0.3 (specularColor 1.0 1.0 1.0) 0.4 1.4 0.0 0.0
  , transmission: transmission 0.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.6 sssCol (subsurfaceRadius 1.0 0.35 0.15) 1.0 0.0
  , sheen: sheen 0.0 (sheenColor 1.0 1.0 1.0) 0.3
  , coat: coat 0.0 (coatColor 1.0 1.0 1.0) 0.1 0.0 0.0 1.5 0.0 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // fabric
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fabric — sheen layer for velvet, silk, satin.
-- |
-- | A cloth material with:
-- | - Roughened diffuse (0.5) for microfiber scattering
-- | - No specular (handled by sheen)
-- | - Configurable sheen amount and color
-- |
-- | Suitable for: velvet, silk, satin, cotton, wool.
fabric :: BaseColor -> SheenColor -> Number -> StandardSurface
fabric baseCol sheenCol sheenAmount =
  { base: base 0.8 baseCol 0.5 0.0
  , specular: specular 0.0 (specularColor 1.0 1.0 1.0) 0.5 1.5 0.0 0.0
  , transmission: transmission 0.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.0 (subsurfaceColor 1.0 1.0 1.0) (subsurfaceRadius 1.0 1.0 1.0) 1.0 0.0
  , sheen: sheen sheenAmount sheenCol 0.3
  , coat: coat 0.0 (coatColor 1.0 1.0 1.0) 0.1 0.0 0.0 1.5 0.0 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // car paint
-- ═════════════════════════════════════════════════════════════════════════════

-- | Car paint — metallic base with clear coat.
-- |
-- | An automotive finish with:
-- | - Metallic flake base (0.7 metalness)
-- | - Full clear coat (1.0 weight)
-- | - Very smooth coat (0.05 roughness)
-- | - Coat affects underlying color (0.5)
-- |
-- | Suitable for: cars, motorcycles, appliances, high-gloss products.
carPaint :: BaseColor -> CoatColor -> StandardSurface
carPaint baseCol coatCol =
  { base: base 0.6 baseCol 0.0 0.7
  , specular: specular 1.0 (specularColor 1.0 1.0 1.0) 0.3 1.5 0.0 0.0
  , transmission: transmission 0.0 (transmissionColor 1.0 1.0 1.0) 0.0 0.0
  , subsurface: subsurface 0.0 (subsurfaceColor 1.0 1.0 1.0) (subsurfaceRadius 1.0 1.0 1.0) 1.0 0.0
  , sheen: sheen 0.0 (sheenColor 1.0 1.0 1.0) 0.3
  , coat: coat 1.0 coatCol 0.05 0.0 0.0 1.5 0.5 0.0
  , thinFilm: thinFilm 0.0 1.5
  , emission: emission 0.0 (emissionColor 1.0 1.0 1.0)
  , geometry: geometry (opacity 1.0 1.0 1.0) false
  }
