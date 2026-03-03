-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // scraper // types // gradient
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Gradient extraction types for 1:1 visual parity.
-- |
-- | Captures CSS gradient backgrounds:
-- | - Linear gradients with angle and color stops
-- | - Radial gradients with shape and position
-- | - Conic gradients with rotation
-- | - Multiple layered backgrounds

module Hydrogen.Scraper.Types.Gradient
  ( -- * Types
    ExtractedGradient(..)
  , ExtractedBackground
  , BackgroundLayer(..)
  
  -- * Constructors
  , emptyBackground
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.Gradient (Gradient)
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Device (Pixel)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // extracted gradient
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted gradient using Schema Gradient type
-- |
-- | Wraps the Schema gradient with extraction metadata.
newtype ExtractedGradient = ExtractedGradient
  { gradient :: Gradient
  , cssOriginal :: String  -- ^ Original CSS for debugging
  }

derive instance eqExtractedGradient :: Eq ExtractedGradient

instance showExtractedGradient :: Show ExtractedGradient where
  show (ExtractedGradient g) = "ExtractedGradient"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // background layer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A single background layer
-- |
-- | CSS backgrounds can have multiple layers stacked.
data BackgroundLayer
  = SolidColor OKLCH
  | GradientLayer ExtractedGradient
  | ImageLayer
      { url :: String
      , size :: { width :: Maybe Pixel, height :: Maybe Pixel }
      , position :: { x :: Pixel, y :: Pixel }
      , repeat :: String  -- ^ "repeat", "no-repeat", "repeat-x", "repeat-y"
      }

derive instance eqBackgroundLayer :: Eq BackgroundLayer

instance showBackgroundLayer :: Show BackgroundLayer where
  show (SolidColor _) = "SolidColor"
  show (GradientLayer _) = "GradientLayer"
  show (ImageLayer _) = "ImageLayer"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // extracted background
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete background extraction
-- |
-- | Supports multiple layers as CSS does.
type ExtractedBackground =
  { layers :: Array BackgroundLayer
  , blendMode :: String  -- ^ "normal", "multiply", "screen", etc.
  , attachment :: String -- ^ "scroll", "fixed", "local"
  , clip :: String       -- ^ "border-box", "padding-box", "content-box"
  , origin :: String     -- ^ "border-box", "padding-box", "content-box"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty background (transparent)
emptyBackground :: ExtractedBackground
emptyBackground =
  { layers: []
  , blendMode: "normal"
  , attachment: "scroll"
  , clip: "border-box"
  , origin: "padding-box"
  }
