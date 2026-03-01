-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // composition // effect // noise
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Noise/Grain Effects — Noise overlay and film grain simulation.
-- |
-- | Noise effects add random variation to images for texture or
-- | vintage aesthetics. All parameters are bounded.

module Hydrogen.Composition.Effect.Noise
  ( NoiseOverlaySpec
  , NoiseBlendMode(..)
  , GrainSpec
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // noise overlay
-- ═══════════════════════════════════════════════════════════════════════════════

data NoiseBlendMode = NoiseAdd | NoiseMultiply | NoiseScreen | NoiseOverlay

derive instance eqNoiseBlendMode :: Eq NoiseBlendMode

instance showNoiseBlendMode :: Show NoiseBlendMode where
  show NoiseAdd = "add"
  show NoiseMultiply = "multiply"
  show NoiseScreen = "screen"
  show NoiseOverlay = "overlay"

type NoiseOverlaySpec =
  { amount :: Number      -- 0-100%
  , blendMode :: NoiseBlendMode
  , monochrome :: Boolean
  , animated :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // grain
-- ═══════════════════════════════════════════════════════════════════════════════

type GrainSpec =
  { intensity :: Number   -- 0-100
  , size :: Number        -- 0.1-10
  , softness :: Number    -- 0-100
  , monochrome :: Boolean
  }
