-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // compute-kernel/noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ComputeKernel/Noise — GPU Noise Generation Kernel Types
-- |
-- | Procedural noise generation for textures and effects:
-- | - Perlin: Classic gradient noise
-- | - Simplex: Faster gradient noise with fewer artifacts
-- | - FBM: Fractal Brownian Motion for natural textures
-- | - Worley: Cellular/Voronoi noise

module Hydrogen.GPU.ComputeKernel.Noise
  ( -- * Noise Types
    NoiseKernel(..)
  , WorleyDistance(..)
  
  -- * Specific Kernels
  , PerlinNoiseKernel(..)
  , SimplexNoiseKernel(..)
  , FBMNoiseKernel(..)
  , WorleyNoiseKernel(..)
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

import Hydrogen.GPU.ComputeKernel.Core
  ( KernelConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // noise kernels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise kernel variants
-- |
-- | Each variant maps to a WebGPU compute shader with workgroup 8x8x8
-- | (for 3D noise with octaves).
data NoiseKernel
  = NoisePerlin PerlinNoiseKernel
  | NoiseSimplex SimplexNoiseKernel
  | NoiseFBM FBMNoiseKernel
  | NoiseWorley WorleyNoiseKernel

derive instance eqNoiseKernel :: Eq NoiseKernel

instance showNoiseKernel :: Show NoiseKernel where
  show (NoisePerlin k) = "(NoisePerlin " <> show k <> ")"
  show (NoiseSimplex k) = "(NoiseSimplex " <> show k <> ")"
  show (NoiseFBM k) = "(NoiseFBM " <> show k <> ")"
  show (NoiseWorley k) = "(NoiseWorley " <> show k <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // perlin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perlin noise kernel
-- |
-- | Classic gradient noise with octave support.
newtype PerlinNoiseKernel = PerlinNoiseKernel
  { scale :: Number            -- Noise scale (frequency)
  , seed :: Int                -- Random seed for determinism
  , octaves :: Int             -- Number of octaves
  , persistence :: Number      -- Amplitude decay per octave
  , lacunarity :: Number       -- Frequency growth per octave
  , time :: Number             -- Time for animation
  , config :: KernelConfig
  }

derive instance eqPerlinNoiseKernel :: Eq PerlinNoiseKernel

instance showPerlinNoiseKernel :: Show PerlinNoiseKernel where
  show (PerlinNoiseKernel k) = "(PerlinNoiseKernel scale:" <> show k.scale <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // simplex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simplex noise kernel
-- |
-- | Faster than Perlin with fewer directional artifacts.
newtype SimplexNoiseKernel = SimplexNoiseKernel
  { scale :: Number
  , seed :: Int
  , time :: Number
  , config :: KernelConfig
  }

derive instance eqSimplexNoiseKernel :: Eq SimplexNoiseKernel

instance showSimplexNoiseKernel :: Show SimplexNoiseKernel where
  show (SimplexNoiseKernel k) = "(SimplexNoiseKernel scale:" <> show k.scale <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // fbm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fractal Brownian Motion noise kernel
-- |
-- | Layered noise for natural-looking textures.
-- | Each octave adds detail at higher frequencies.
newtype FBMNoiseKernel = FBMNoiseKernel
  { scale :: Number
  , seed :: Int
  , octaves :: Int             -- Number of noise layers
  , persistence :: Number      -- Amplitude decay (0.0-1.0)
  , lacunarity :: Number       -- Frequency multiplier (typically 2.0)
  , time :: Number
  , turbulent :: Boolean       -- Use absolute value (turbulence)
  , config :: KernelConfig
  }

derive instance eqFBMNoiseKernel :: Eq FBMNoiseKernel

instance showFBMNoiseKernel :: Show FBMNoiseKernel where
  show (FBMNoiseKernel k) = "(FBMNoiseKernel octaves:" <> show k.octaves <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // worley
-- ═════════════════════════════════════════════════════════════════════════════

-- | Worley (cellular) noise kernel
-- |
-- | Creates cell-like patterns based on distance to random points.
newtype WorleyNoiseKernel = WorleyNoiseKernel
  { scale :: Number
  , seed :: Int
  , cellCount :: Int           -- Number of cells
  , distanceType :: WorleyDistance
  , time :: Number
  , config :: KernelConfig
  }

derive instance eqWorleyNoiseKernel :: Eq WorleyNoiseKernel

instance showWorleyNoiseKernel :: Show WorleyNoiseKernel where
  show (WorleyNoiseKernel k) = "(WorleyNoiseKernel cells:" <> show k.cellCount <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // worley distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Worley noise distance metric
-- |
-- | Determines how distance to cell centers is calculated:
-- | - Euclidean: Standard straight-line distance (round cells)
-- | - Manhattan: Axis-aligned distance (diamond cells)
-- | - Chebyshev: Maximum axis distance (square cells)
data WorleyDistance
  = WorleyEuclidean
  | WorleyManhattan
  | WorleyChebyshev

derive instance eqWorleyDistance :: Eq WorleyDistance
