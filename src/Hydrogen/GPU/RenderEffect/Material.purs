-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // render-effect/material
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material effects for the RenderEffect system.
-- |
-- | Provides four material variants for surface treatments:
-- | - **Glass**: Transparent with refraction/reflection
-- | - **Frosted**: Blurred background with texture (iOS/macOS)
-- | - **Noise**: Procedural noise overlay (texture)
-- | - **Grain**: Film grain for cinematic aesthetic

module Hydrogen.GPU.RenderEffect.Material
  ( -- * Material Effect Type
    MaterialEffect(..)
  
  -- * Material Variants
  , GlassEffect(..)
  , FrostedGlass(..)
  , NoiseOverlay(..)
  , GrainEffect(..)
  
  -- * Material Configuration
  , NoiseType(..)
  
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.GPU.RenderEffect.Types (GlowColor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // material effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material effect variants
-- |
-- | Materials simulate physical surface properties. They typically require
-- | reading the background (for glass/frosted) or generating procedural
-- | textures (for noise/grain).
data MaterialEffect
  = MaterialGlass GlassEffect
  | MaterialFrosted FrostedGlass
  | MaterialNoise NoiseOverlay
  | MaterialGrain GrainEffect

derive instance eqMaterialEffect :: Eq MaterialEffect

instance showMaterialEffect :: Show MaterialEffect where
  show (MaterialGlass m) = "(MaterialGlass " <> show m <> ")"
  show (MaterialFrosted m) = "(MaterialFrosted " <> show m <> ")"
  show (MaterialNoise m) = "(MaterialNoise " <> show m <> ")"
  show (MaterialGrain m) = "(MaterialGrain " <> show m <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // material variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glass effect — transparent with refraction
-- |
-- | Simulates transparent glass with optional refraction (distortion),
-- | reflection, and fresnel edge enhancement.
newtype GlassEffect = GlassEffect
  { tint :: GlowColor        -- Glass tint color
  , opacity :: Number        -- Background visibility (0.0-1.0)
  , refraction :: Number     -- Refraction strength (0.0-1.0)
  , reflection :: Number     -- Reflection amount (0.0-1.0)
  , fresnel :: Boolean       -- Edge reflection enhancement
  }

derive instance eqGlassEffect :: Eq GlassEffect

instance showGlassEffect :: Show GlassEffect where
  show (GlassEffect m) = "(GlassEffect opacity:" <> show m.opacity <> ")"

-- | Frosted glass — blurred background with texture
-- |
-- | The signature iOS/macOS effect: blurred background with optional
-- | saturation/brightness adjustments and subtle noise texture.
newtype FrostedGlass = FrostedGlass
  { blur :: Number           -- Background blur amount
  , saturation :: Number     -- Color saturation (0.0-2.0)
  , brightness :: Number     -- Brightness adjustment (0.0-2.0)
  , noiseAmount :: Number    -- Frosted texture noise (0.0-0.1)
  , tint :: GlowColor        -- Optional color tint
  }

derive instance eqFrostedGlass :: Eq FrostedGlass

instance showFrostedGlass :: Show FrostedGlass where
  show (FrostedGlass m) = "(FrostedGlass blur:" <> show m.blur <> ")"

-- | Noise overlay — procedural noise texture
-- |
-- | Generates procedural noise and overlays it on the element.
-- | Various noise types support different aesthetic needs.
newtype NoiseOverlay = NoiseOverlay
  { noiseType :: NoiseType
  , scale :: Number          -- Noise scale (1.0 = 1:1 pixels)
  , intensity :: Number      -- Noise visibility (0.0-1.0)
  , animated :: Boolean      -- Animate noise
  , speed :: Number          -- Animation speed
  }

derive instance eqNoiseOverlay :: Eq NoiseOverlay

instance showNoiseOverlay :: Show NoiseOverlay where
  show (NoiseOverlay m) = "(NoiseOverlay intensity:" <> show m.intensity <> ")"

-- | Film grain effect
-- |
-- | Simulates photographic film grain for cinematic aesthetic.
-- | Animated grain varies per-frame for authenticity.
newtype GrainEffect = GrainEffect
  { amount :: Number         -- Grain intensity (0.0-1.0)
  , size :: Number           -- Grain size (0.5-2.0)
  , colorful :: Boolean      -- Color vs monochrome grain
  , animated :: Boolean      -- Per-frame variation
  }

derive instance eqGrainEffect :: Eq GrainEffect

instance showGrainEffect :: Show GrainEffect where
  show (GrainEffect m) = "(GrainEffect amount:" <> show m.amount <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // material configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise types
-- |
-- | Each noise type has distinct visual characteristics:
-- | - **Perlin**: Smooth, organic gradients
-- | - **Simplex**: Similar to Perlin, computationally cheaper
-- | - **Worley**: Cellular/voronoi patterns
-- | - **White**: Pure random noise
-- | - **FBM**: Fractal Brownian Motion (layered Perlin)
data NoiseType
  = NoisePerlin
  | NoiseSimplex
  | NoiseWorley
  | NoiseWhite
  | NoiseFBM                 -- Fractal Brownian Motion

derive instance eqNoiseType :: Eq NoiseType
