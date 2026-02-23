-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // spatial // roughness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Roughness - surface roughness for PBR materials.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: Perfectly smooth (mirror-like reflections)
-- | - **0.3**: Glossy (polished metal, wet surfaces)
-- | - **0.7**: Rough (concrete, fabric)
-- | - **1.0**: Completely diffuse (matte, no specular)
-- |
-- | Controls microfacet distribution in PBR shading models (GGX, Beckmann).
-- | Used in Unreal, Unity, Cinema4D, Blender, Arnold, etc.

module Hydrogen.Schema.Spatial.Roughness
  ( Roughness
  , roughness
  , unwrap
  , toNumber
  , bounds
  , mirror
  , glossy
  , semiRough
  , matte
  ) where

import Prelude

import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // roughness
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Surface roughness for PBR (0.0 to 1.0)
-- |
-- | Controls how rough a surface appears. Smooth surfaces have sharp reflections,
-- | rough surfaces have diffuse, blurred reflections.
newtype Roughness = Roughness Number

derive instance eqRoughness :: Eq Roughness
derive instance ordRoughness :: Ord Roughness

instance showRoughness :: Show Roughness where
  show (Roughness r) = show r

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a roughness value, clamping to 0.0-1.0
roughness :: Number -> Roughness
roughness n = Roughness (Bounded.clampNumber 0.0 1.0 n)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Mirror smooth (perfect reflections)
mirror :: Roughness
mirror = Roughness 0.0

-- | Glossy (polished metal, wet surfaces)
glossy :: Roughness
glossy = Roughness 0.2

-- | Semi-rough (plastic, wood)
semiRough :: Roughness
semiRough = Roughness 0.6

-- | Matte (fabric, paper, diffuse)
matte :: Roughness
matte = Roughness 1.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: Roughness -> Number
unwrap (Roughness r) = r

-- | Convert to Number (passthrough for this type)
toNumber :: Roughness -> Number
toNumber (Roughness r) = r

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "roughness" "PBR surface roughness (smooth to diffuse)"
