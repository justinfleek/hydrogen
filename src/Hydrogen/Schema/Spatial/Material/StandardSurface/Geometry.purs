-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geometry properties for MaterialX Standard Surface.
-- |
-- | Controls how the material interacts with geometry — opacity for
-- | transparency and thin-walled flag for single-sided refraction.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - opacity: RGB [0,0,0]-[1,1,1] default (1,1,1) — per-channel opacity
-- | - thin_walled: boolean default false — treat as infinitely thin shell

module Hydrogen.Schema.Spatial.Material.StandardSurface.Geometry
  ( -- * Geometry Type
    Geometry
  , geometry
  
  -- * Bounded Primitives
  , Opacity
  , ThinWalled(ThinWalledTrue, ThinWalledFalse)
  , opacity
  , thinWalled
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Hydrogen.Schema.Spatial.Material.StandardSurface.Core
  ( ColorChannel
  , colorChannel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-channel opacity [0.0, 1.0].
-- |
-- | Each channel (R, G, B) can have independent opacity for effects like
-- | colored glass or spectrally-selective transparency.
-- |
-- | At (0, 0, 0), the material is fully transparent.
-- | At (1, 1, 1), the material is fully opaque.
type Opacity = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct opacity from RGB values [0.0, 1.0].
opacity :: Number -> Number -> Number -> Opacity
opacity r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // thin walled
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thin-walled geometry flag.
-- |
-- | Controls how refraction is calculated:
-- | - ThinWalledFalse: Material has volume (normal refraction)
-- | - ThinWalledTrue: Material is infinitely thin (no refraction offset)
-- |
-- | Used for leaves, paper, cloth, and other single-layer surfaces.
data ThinWalled = ThinWalledTrue | ThinWalledFalse

derive instance eqThinWalled :: Eq ThinWalled
derive instance ordThinWalled :: Ord ThinWalled

instance showThinWalled :: Show ThinWalled where
  show ThinWalledTrue = "ThinWalled(true)"
  show ThinWalledFalse = "ThinWalled(false)"

-- | Construct thin-walled flag from boolean.
thinWalled :: Boolean -> ThinWalled
thinWalled true = ThinWalledTrue
thinWalled false = ThinWalledFalse

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // geometry // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete geometry properties configuration.
-- |
-- | Controls opacity and thin-walled behavior for the material.
type Geometry =
  { opacity :: Opacity
  , thinWalled :: ThinWalled
  }

-- | Construct geometry properties with all parameters.
geometry :: Opacity -> Boolean -> Geometry
geometry o tw =
  { opacity: o
  , thinWalled: thinWalled tw
  }
