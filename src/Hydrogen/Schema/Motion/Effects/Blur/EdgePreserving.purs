-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // motion // blur // edgepreserving
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Edge-Preserving Blur Effects — Bilateral and Smart blur.
-- |
-- | These blurs selectively soften areas while preserving sharp edges,
-- | creating a more artistic or skin-smoothing effect.

module Hydrogen.Schema.Motion.Effects.Blur.EdgePreserving
  ( -- * Bilateral Blur Effect
    BilateralBlurEffect
  , defaultBilateralBlur
  , mkBilateralBlur
  , isBilateralNeutral
  , bilateralBlurToString
  
  -- * Smart Blur Effect
  , SmartBlurEffect
  , defaultSmartBlur
  , mkSmartBlur
  , isSmartBlurNeutral
  ) where

import Prelude
  ( class Show
  , show
  , (<>)
  , not
  , (==)
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Motion.Effects.Blur.Types
  ( SmartBlurMode(SBMNormal)
  , SmartBlurQuality(SBQMedium)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bilateral // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bilateral Blur effect — edge-preserving blur.
-- |
-- | Selectively blurs image while preserving edges. Areas with high contrast
-- | are blurred less than low-contrast areas. Creates a softer, dreamier look
-- | than Smart Blur.
-- |
-- | AE Properties:
-- | - Radius: Size of blur kernel (0-100)
-- | - Threshold: Edge preservation threshold (0-100, lower = more edges preserved)
-- | - Colorize: When true, operates on RGB channels; when false, luminance only
type BilateralBlurEffect =
  { radius :: Number      -- ^ Blur kernel size in pixels (0-100)
  , threshold :: Number   -- ^ Edge preservation threshold (0-100)
  , colorize :: Boolean   -- ^ True = color, False = monochrome (luminance only)
  }

defaultBilateralBlur :: BilateralBlurEffect
defaultBilateralBlur =
  { radius: 5.0
  , threshold: 10.0
  , colorize: true
  }

mkBilateralBlur :: Number -> Number -> Boolean -> BilateralBlurEffect
mkBilateralBlur rad thresh color =
  { radius: clampNumber 0.0 100.0 rad
  , threshold: clampNumber 0.0 100.0 thresh
  , colorize: color
  }

isBilateralNeutral :: BilateralBlurEffect -> Boolean
isBilateralNeutral effect = effect.radius == 0.0

-- | Serialize Bilateral blur to readable string.
bilateralBlurToString :: BilateralBlurEffect -> String
bilateralBlurToString effect =
  "BilateralBlur(r=" <> show effect.radius <> ", thresh=" <>
  show effect.threshold <> 
  (if not effect.colorize then ", mono" else "") <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // smart // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Smart Blur effect — edge-preserving blur with edge detection.
-- |
-- | More aggressive edge preservation than Bilateral Blur.
-- | Can visualize detected edges.
-- |
-- | AE Properties:
-- | - Radius: Blur amount (0.1-100)
-- | - Threshold: Edge detection threshold (0.1-100)
-- | - Mode: Normal, Edge Only, or Overlay Edge
-- | - Quality: Low, Medium, High
type SmartBlurEffect =
  { radius :: Number           -- ^ Blur radius (0.1-100)
  , threshold :: Number        -- ^ Edge threshold (0.1-100)
  , mode :: SmartBlurMode      -- ^ Output mode
  , quality :: SmartBlurQuality -- ^ Render quality
  }

defaultSmartBlur :: SmartBlurEffect
defaultSmartBlur =
  { radius: 3.0
  , threshold: 25.0
  , mode: SBMNormal
  , quality: SBQMedium
  }

mkSmartBlur :: Number -> Number -> SmartBlurMode -> SmartBlurQuality -> SmartBlurEffect
mkSmartBlur rad thresh mode qual =
  { radius: clampNumber 0.1 100.0 rad
  , threshold: clampNumber 0.1 100.0 thresh
  , mode: mode
  , quality: qual
  }

isSmartBlurNeutral :: SmartBlurEffect -> Boolean
isSmartBlurNeutral effect = effect.radius == 0.0
