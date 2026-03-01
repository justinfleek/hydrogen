-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // standard surface // coat
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Clear coat layer for MaterialX Standard Surface.
-- |
-- | The coat layer provides a secondary specular layer on top of the base
-- | material. Used for car paint, lacquer, varnish, and other coated surfaces.
-- |
-- | ## MaterialX Parameters (from standard_surface.mtlx)
-- |
-- | - coat: [0.0, 1.0] default 0.0 — coat intensity
-- | - coat_color: RGB default (1,1,1) — absorption color
-- | - coat_roughness: [0.0, 1.0] default 0.1 — GGX roughness
-- | - coat_anisotropy: [0.0, 1.0] default 0.0 — anisotropic stretch
-- | - coat_rotation: [0.0, 1.0] default 0.0 — anisotropy rotation
-- | - coat_IOR: [1.0, 3.0] default 1.5 — Fresnel IOR
-- | - coat_affect_color: [0.0, 1.0] default 0.0 — tint underlying layers
-- | - coat_affect_roughness: [0.0, 1.0] default 0.0 — blur underlying layers

module Hydrogen.Schema.Spatial.Material.StandardSurface.Coat
  ( -- * Coat Layer Type
    Coat
  , coat
  
  -- * Bounded Primitives
  , CoatWeight
  , CoatColor
  , CoatRoughness
  , CoatAnisotropy
  , CoatRotation
  , CoatIOR
  , CoatAffectColor
  , CoatAffectRoughness
  , coatWeight
  , coatColor
  , coatRoughness
  , coatAnisotropy
  , coatRotation
  , coatIOR
  , coatAffectColor
  , coatAffectRoughness
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
--                                                         // coat // weight
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat weight [0.0, 1.0] — controls clear coat visibility.
-- |
-- | At 0.0, no coat layer.
-- | At 1.0, full clear coat coverage.
newtype CoatWeight = CoatWeight Number

derive instance eqCoatWeight :: Eq CoatWeight
derive instance ordCoatWeight :: Ord CoatWeight

instance showCoatWeight :: Show CoatWeight where
  show (CoatWeight n) = "CoatWeight(" <> show n <> ")"

-- | Construct coat weight, clamping to [0.0, 1.0].
coatWeight :: Number -> CoatWeight
coatWeight n = CoatWeight (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // coat // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB color for coat absorption.
-- |
-- | Light passing through the coat layer is tinted by this color.
-- | For clear coat, this is typically white (1, 1, 1).
-- | For tinted lacquers, this provides the color shift.
type CoatColor = { r :: ColorChannel, g :: ColorChannel, b :: ColorChannel }

-- | Construct coat color from RGB values [0.0, 1.0].
coatColor :: Number -> Number -> Number -> CoatColor
coatColor r g b =
  { r: colorChannel r
  , g: colorChannel g
  , b: colorChannel b
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // coat // roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat roughness [0.0, 1.0] — GGX microfacet roughness.
-- |
-- | At 0.0, the coat is a perfect mirror (wet look).
-- | At 1.0, the coat is completely matte.
-- |
-- | Typical values for clear coat are 0.0 to 0.2.
newtype CoatRoughness = CoatRoughness Number

derive instance eqCoatRoughness :: Eq CoatRoughness
derive instance ordCoatRoughness :: Ord CoatRoughness

instance showCoatRoughness :: Show CoatRoughness where
  show (CoatRoughness n) = "CoatRoughness(" <> show n <> ")"

-- | Construct coat roughness, clamping to [0.0, 1.0].
coatRoughness :: Number -> CoatRoughness
coatRoughness n = CoatRoughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // coat // anisotropy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat anisotropy [0.0, 1.0] — anisotropic highlight stretch.
-- |
-- | Similar to specular anisotropy but for the coat layer.
newtype CoatAnisotropy = CoatAnisotropy Number

derive instance eqCoatAnisotropy :: Eq CoatAnisotropy
derive instance ordCoatAnisotropy :: Ord CoatAnisotropy

instance showCoatAnisotropy :: Show CoatAnisotropy where
  show (CoatAnisotropy n) = "CoatAnisotropy(" <> show n <> ")"

-- | Construct coat anisotropy, clamping to [0.0, 1.0].
coatAnisotropy :: Number -> CoatAnisotropy
coatAnisotropy n = CoatAnisotropy (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // coat // rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat rotation [0.0, 1.0] — anisotropy orientation.
-- |
-- | Rotates the coat anisotropy direction independently from specular.
newtype CoatRotation = CoatRotation Number

derive instance eqCoatRotation :: Eq CoatRotation
derive instance ordCoatRotation :: Ord CoatRotation

instance showCoatRotation :: Show CoatRotation where
  show (CoatRotation n) = "CoatRotation(" <> show n <> ")"

-- | Construct coat rotation, clamping to [0.0, 1.0].
coatRotation :: Number -> CoatRotation
coatRotation n = CoatRotation (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // coat // ior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat IOR [1.0, 3.0] — Fresnel index of refraction for coat layer.
-- |
-- | Controls the strength of the coat reflection. Typical clear coats
-- | have IOR around 1.5 (similar to glass).
newtype CoatIOR = CoatIOR Number

derive instance eqCoatIOR :: Eq CoatIOR
derive instance ordCoatIOR :: Ord CoatIOR

instance showCoatIOR :: Show CoatIOR where
  show (CoatIOR n) = "CoatIOR(" <> show n <> ")"

-- | Construct coat IOR, clamping to [1.0, 3.0].
coatIOR :: Number -> CoatIOR
coatIOR n = CoatIOR (Bounded.clampNumber 1.0 3.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // coat // affect color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat affect color [0.0, 1.0] — tint underlying layers by coat color.
-- |
-- | At 0.0, the coat color only affects the coat layer itself.
-- | At 1.0, the coat color fully tints the underlying base/specular layers.
newtype CoatAffectColor = CoatAffectColor Number

derive instance eqCoatAffectColor :: Eq CoatAffectColor
derive instance ordCoatAffectColor :: Ord CoatAffectColor

instance showCoatAffectColor :: Show CoatAffectColor where
  show (CoatAffectColor n) = "CoatAffectColor(" <> show n <> ")"

-- | Construct coat affect color, clamping to [0.0, 1.0].
coatAffectColor :: Number -> CoatAffectColor
coatAffectColor n = CoatAffectColor (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // coat // affect roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coat affect roughness [0.0, 1.0] — blur underlying layers through coat.
-- |
-- | At 0.0, underlying layers appear sharp through the coat.
-- | At 1.0, the coat roughness fully applies to underlying layers too.
-- |
-- | Simulates how rough coatings can blur the appearance of what's beneath.
newtype CoatAffectRoughness = CoatAffectRoughness Number

derive instance eqCoatAffectRoughness :: Eq CoatAffectRoughness
derive instance ordCoatAffectRoughness :: Ord CoatAffectRoughness

instance showCoatAffectRoughness :: Show CoatAffectRoughness where
  show (CoatAffectRoughness n) = "CoatAffectRoughness(" <> show n <> ")"

-- | Construct coat affect roughness, clamping to [0.0, 1.0].
coatAffectRoughness :: Number -> CoatAffectRoughness
coatAffectRoughness n = CoatAffectRoughness (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // coat // layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete clear coat layer configuration.
-- |
-- | For car paint, lacquer, varnish, and other coated surfaces.
-- | The coat layer adds a secondary specular reflection on top of all
-- | other layers.
type Coat =
  { weight :: CoatWeight
  , color :: CoatColor
  , roughness :: CoatRoughness
  , anisotropy :: CoatAnisotropy
  , rotation :: CoatRotation
  , ior :: CoatIOR
  , affectColor :: CoatAffectColor
  , affectRoughness :: CoatAffectRoughness
  }

-- | Construct a coat layer with all parameters.
coat :: Number -> CoatColor -> Number -> Number -> Number -> Number -> Number -> Number -> Coat
coat w c r a rot i ac ar =
  { weight: coatWeight w
  , color: c
  , roughness: coatRoughness r
  , anisotropy: coatAnisotropy a
  , rotation: coatRotation rot
  , ior: coatIOR i
  , affectColor: coatAffectColor ac
  , affectRoughness: coatAffectRoughness ar
  }
