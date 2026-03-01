-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // emission
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Emission layer for MaterialX Standard Surface.
-- |
-- | The emission layer provides self-illumination for glowing materials
-- | like screens, fire, neon lights, and radioactive substances.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - emission: [0.0, inf) default 0.0 — emission intensity
-- | - emission_color: RGB default (1,1,1) — emission color

module Hydrogen.Schema.Spatial.Material.StandardSurface.Emission
  ( -- * Emission Layer Type
    Emission
  , emission
  
  -- * Bounded Primitives
  , EmissionWeight
  , EmissionColor
  , emissionWeight
  , emissionColor
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
--                                                     // emission // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Emission weight [0.0, 1000.0] — emission intensity multiplier.
-- |
-- | At 0.0, no emission (material only reflects/transmits light).
-- | Values > 1.0 create HDR emission for bloom effects.
-- |
-- | We clamp to 1000.0 as a reasonable maximum for real-time rendering.
-- | For offline rendering, higher values might be needed but can be
-- | achieved through exposure/gain in the render settings.
newtype EmissionWeight = EmissionWeight Number

derive instance eqEmissionWeight :: Eq EmissionWeight
derive instance ordEmissionWeight :: Ord EmissionWeight

instance showEmissionWeight :: Show EmissionWeight where
  show (EmissionWeight n) = "EmissionWeight(" <> show n <> ")"

-- | Construct emission weight, clamping to [0.0, 1000.0].
emissionWeight :: Number -> EmissionWeight
emissionWeight n = EmissionWeight (Bounded.clampNumber 0.0 1000.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // emission // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for emission.
-- |
-- | The color of emitted light. Combined with emission weight to produce
-- | the final emitted radiance.
type EmissionColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct emission color from RGB values [0.0, 1.0].
emissionColor :: Number -> Number -> Number -> EmissionColor
emissionColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // emission // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete emission layer configuration.
-- |
-- | For glowing materials, screens, fire, neon lights, and luminous surfaces.
-- | Emission is added on top of all other lighting contributions.
type Emission =
  { weight :: EmissionWeight
  , color :: EmissionColor
  }

-- | Construct an emission layer with all parameters.
emission :: Number -> EmissionColor -> Emission
emission w c =
  { weight: emissionWeight w
  , color: c
  }
