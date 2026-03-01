-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // sheen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sheen layer for MaterialX Standard Surface.
-- |
-- | The sheen layer provides soft, fuzzy reflections at grazing angles.
-- | Used for velvet, fabric, microfiber, and other cloth-like surfaces.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - sheen: [0.0, 1.0] default 0.0 — sheen intensity
-- | - sheen_color: RGB default (1,1,1) — sheen tint
-- | - sheen_roughness: [0.0, 1.0] default 0.3 — sheen falloff

module Hydrogen.Schema.Spatial.Material.StandardSurface.Sheen
  ( -- * Sheen Layer Type
    Sheen
  , sheen
  
  -- * Bounded Primitives
  , SheenWeight
  , SheenColor
  , SheenRoughness
  , sheenWeight
  , sheenColor
  , sheenRoughness
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
--                                                        // sheen // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheen weight [0.0, 1.0] — controls sheen layer visibility.
-- |
-- | At 0.0, no sheen effect.
-- | At 1.0, maximum sheen at grazing angles.
newtype SheenWeight = SheenWeight Number

derive instance eqSheenWeight :: Eq SheenWeight
derive instance ordSheenWeight :: Ord SheenWeight

instance showSheenWeight :: Show SheenWeight where
  show (SheenWeight n) = "SheenWeight(" <> show n <> ")"

-- | Construct sheen weight, clamping to [0.0, 1.0].
sheenWeight :: Number -> SheenWeight
sheenWeight n = SheenWeight (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // sheen // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for sheen reflection.
-- |
-- | Tints the sheen reflection. For most fabrics, this is the same as or
-- | similar to the base color, but can differ for materials like velvet.
type SheenColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct sheen color from RGB values [0.0, 1.0].
sheenColor :: Number -> Number -> Number -> SheenColor
sheenColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // sheen // roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheen roughness [0.0, 1.0] — controls sheen falloff width.
-- |
-- | Lower values create a sharper, more concentrated sheen effect.
-- | Higher values spread the sheen over a wider angular range.
newtype SheenRoughness = SheenRoughness Number

derive instance eqSheenRoughness :: Eq SheenRoughness
derive instance ordSheenRoughness :: Ord SheenRoughness

instance showSheenRoughness :: Show SheenRoughness where
  show (SheenRoughness n) = "SheenRoughness(" <> show n <> ")"

-- | Construct sheen roughness, clamping to [0.0, 1.0].
sheenRoughness :: Number -> SheenRoughness
sheenRoughness n = SheenRoughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // sheen // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete sheen layer configuration.
-- |
-- | For velvet, fabric, microfiber, and other soft, fuzzy surfaces.
-- | The sheen effect is most visible at grazing angles.
type Sheen =
  { weight :: SheenWeight
  , color :: SheenColor
  , roughness :: SheenRoughness
  }

-- | Construct a sheen layer with all parameters.
sheen :: Number -> SheenColor -> Number -> Sheen
sheen w c r =
  { weight: sheenWeight w
  , color: c
  , roughness: sheenRoughness r
  }
