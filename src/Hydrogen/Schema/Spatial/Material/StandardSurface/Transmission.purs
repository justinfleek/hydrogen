-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // transmission
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Transmission layer for MaterialX Standard Surface.
-- |
-- | The transmission layer provides refractive transparency for glass, water,
-- | and other see-through materials. It uses Beer's law for depth-based
-- | absorption and supports chromatic dispersion.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - transmission: [0.0, 1.0] default 0.0 — transmission weight
-- | - transmission_color: RGB default (1,1,1) — absorption color
-- | - transmission_depth: [0.0, inf) default 0.0 — absorption distance
-- | - transmission_dispersion: [0.0, inf) default 0.0 — chromatic dispersion

module Hydrogen.Schema.Spatial.Material.StandardSurface.Transmission
  ( -- * Transmission Layer Type
    Transmission
  , transmission
  
  -- * Bounded Primitives
  , TransmissionWeight
  , TransmissionColor
  , TransmissionDepth
  , TransmissionDispersion
  , transmissionWeight
  , transmissionColor
  , transmissionDepth
  , transmissionDispersion
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
--                                                  // transmission // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transmission weight [0.0, 1.0] — controls transparency amount.
-- |
-- | At 0.0, the material is opaque (no transmission).
-- | At 1.0, the material is fully transparent.
newtype TransmissionWeight = TransmissionWeight Number

derive instance eqTransmissionWeight :: Eq TransmissionWeight
derive instance ordTransmissionWeight :: Ord TransmissionWeight

instance showTransmissionWeight :: Show TransmissionWeight where
  show (TransmissionWeight n) = "TransmissionWeight(" <> show n <> ")"

-- | Construct transmission weight, clamping to [0.0, 1.0].
transmissionWeight :: Number -> TransmissionWeight
transmissionWeight n = TransmissionWeight (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // transmission // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for transmission absorption.
-- |
-- | This is NOT the color you see through the material. It's the absorption
-- | color used in Beer's law: light passing through the material is
-- | attenuated by this color over the transmission_depth distance.
type TransmissionColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct transmission color from RGB values [0.0, 1.0].
transmissionColor :: Number -> Number -> Number -> TransmissionColor
transmissionColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // transmission // depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transmission depth [0.0, 1000.0] — Beer's law absorption distance.
-- |
-- | The distance (in scene units) at which the transmission_color fully
-- | absorbs light. Larger values = less absorption per unit distance.
-- |
-- | We clamp to 1000.0 as a reasonable maximum for scene-scale materials.
newtype TransmissionDepth = TransmissionDepth Number

derive instance eqTransmissionDepth :: Eq TransmissionDepth
derive instance ordTransmissionDepth :: Ord TransmissionDepth

instance showTransmissionDepth :: Show TransmissionDepth where
  show (TransmissionDepth n) = "TransmissionDepth(" <> show n <> ")"

-- | Construct transmission depth, clamping to [0.0, 1000.0].
transmissionDepth :: Number -> TransmissionDepth
transmissionDepth n = TransmissionDepth (Bounded.clampNumber 0.0 1000.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // transmission // dispersion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transmission dispersion [0.0, 100.0] — chromatic dispersion amount.
-- |
-- | Controls the wavelength-dependent refraction that creates rainbow effects
-- | in materials like diamond and glass prisms.
-- |
-- | At 0.0, refraction is identical for all wavelengths.
-- | Higher values increase the color separation.
newtype TransmissionDispersion = TransmissionDispersion Number

derive instance eqTransmissionDispersion :: Eq TransmissionDispersion
derive instance ordTransmissionDispersion :: Ord TransmissionDispersion

instance showTransmissionDispersion :: Show TransmissionDispersion where
  show (TransmissionDispersion n) = "TransmissionDispersion(" <> show n <> ")"

-- | Construct transmission dispersion, clamping to [0.0, 100.0].
transmissionDispersion :: Number -> TransmissionDispersion
transmissionDispersion n = TransmissionDispersion (Bounded.clampNumber 0.0 100.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // transmission // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete transmission layer configuration.
-- |
-- | For glass, water, and other transparent materials. The transmission
-- | layer replaces diffuse reflection with refractive transparency.
type Transmission =
  { weight :: TransmissionWeight
  , color :: TransmissionColor
  , depth :: TransmissionDepth
  , dispersion :: TransmissionDispersion
  }

-- | Construct a transmission layer with all parameters.
transmission :: Number -> TransmissionColor -> Number -> Number -> Transmission
transmission w c d disp =
  { weight: transmissionWeight w
  , color: c
  , depth: transmissionDepth d
  , dispersion: transmissionDispersion disp
  }
