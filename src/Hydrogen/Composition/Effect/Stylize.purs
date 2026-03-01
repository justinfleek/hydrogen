-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // composition // effect // stylize
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Stylize Effects — Glow, Shadow, Emboss, Edge Detection, Posterize.
-- |
-- | Stylize effects create visual treatments that modify both color and
-- | spatial characteristics. All parameters are bounded.

module Hydrogen.Composition.Effect.Stylize
  ( GlowSpec
  , DropShadowSpec
  , InnerShadowSpec
  , EmbossSpec
  , EdgeDetectSpec
  , EdgeDetectType
      ( EdgeCanny
      , EdgeSobel
      , EdgePrewitt
      , EdgeLaplacian
      )
  , PosterizeSpec
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Color.RGB (RGB)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // glow
-- ═══════════════════════════════════════════════════════════════════════════════

type GlowSpec =
  { radius :: Number      -- 0-500
  , intensity :: Number   -- 0-500%
  , threshold :: Number   -- 0-100%
  , color :: RGB
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // drop shadow
-- ═══════════════════════════════════════════════════════════════════════════════

type DropShadowSpec =
  { offsetX :: Number     -- -1000 to 1000
  , offsetY :: Number
  , blur :: Number        -- 0-500
  , spread :: Number      -- -100 to 100
  , color :: RGB
  , opacity :: Number     -- 0-100%
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // inner shadow
-- ═══════════════════════════════════════════════════════════════════════════════

type InnerShadowSpec =
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , color :: RGB
  , opacity :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // emboss
-- ═══════════════════════════════════════════════════════════════════════════════

type EmbossSpec =
  { angle :: Number       -- 0-360
  , height :: Number      -- 1-10
  , amount :: Number      -- 0-500%
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // edge detect
-- ═══════════════════════════════════════════════════════════════════════════════

data EdgeDetectType = EdgeCanny | EdgeSobel | EdgePrewitt | EdgeLaplacian

derive instance eqEdgeDetectType :: Eq EdgeDetectType

instance showEdgeDetectType :: Show EdgeDetectType where
  show EdgeCanny = "canny"
  show EdgeSobel = "sobel"
  show EdgePrewitt = "prewitt"
  show EdgeLaplacian = "laplacian"

type EdgeDetectSpec =
  { edgeType :: EdgeDetectType
  , threshold :: Number   -- 0-255
  , invert :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // posterize
-- ═══════════════════════════════════════════════════════════════════════════════

type PosterizeSpec =
  { levels :: Int         -- 2-256
  }
