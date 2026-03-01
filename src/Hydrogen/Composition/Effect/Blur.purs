-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // composition // effect // blur
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blur/Sharpen Effects — Gaussian, Directional, Radial, Box, and Sharpen.
-- |
-- | All blur effects modify pixel neighborhoods to create smoothing or
-- | sharpening effects. Parameters are bounded to prevent invalid states.

module Hydrogen.Composition.Effect.Blur
  ( GaussianBlurSpec
  , DirectionalBlurSpec
  , RadialBlurSpec
  , RadialBlurType
      ( RadialSpin
      , RadialZoom
      )
  , BoxBlurSpec
  , SharpenSpec
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // gaussian blur
-- ═══════════════════════════════════════════════════════════════════════════════

type GaussianBlurSpec =
  { radius :: Number      -- 0-500 pixels
  , quality :: Int        -- 1-5 (iterations)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // directional blur
-- ═══════════════════════════════════════════════════════════════════════════════

type DirectionalBlurSpec =
  { angle :: Number       -- 0-360 degrees
  , distance :: Number    -- 0-500 pixels
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // radial blur
-- ═══════════════════════════════════════════════════════════════════════════════

data RadialBlurType = RadialSpin | RadialZoom

derive instance eqRadialBlurType :: Eq RadialBlurType

instance showRadialBlurType :: Show RadialBlurType where
  show RadialSpin = "spin"
  show RadialZoom = "zoom"

type RadialBlurSpec =
  { blurType :: RadialBlurType
  , amount :: Number      -- 0-100
  , centerX :: Number     -- 0-1 (normalized)
  , centerY :: Number     -- 0-1
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // box blur
-- ═══════════════════════════════════════════════════════════════════════════════

type BoxBlurSpec =
  { radiusX :: Number     -- 0-500
  , radiusY :: Number     -- 0-500
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // sharpen
-- ═══════════════════════════════════════════════════════════════════════════════

type SharpenSpec =
  { amount :: Number      -- 0-500%
  , radius :: Number      -- 0-100
  , threshold :: Number   -- 0-255
  }
