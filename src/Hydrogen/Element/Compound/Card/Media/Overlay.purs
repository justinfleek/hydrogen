-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // element // component // card // media // overlay
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Media Overlay — Overlay configuration for cover/background media.
-- |
-- | ## Overview
-- |
-- | This module contains types for configuring overlays on media elements,
-- | including solid color overlays and gradient overlays for improved
-- | text readability on cover images.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Element.Compound.Card.Media.Overlay
  ( -- * Overlay Config
    OverlayConfig
      ( OverlayNone
      , OverlaySolid
      , OverlayGradient
      )
  
  -- * Gradient Direction
  , GradientDirection
      ( GradientTop
      , GradientBottom
      , GradientLeft
      , GradientRight
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // overlay config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay configuration for cover/background media
data OverlayConfig
  = OverlayNone                            -- ^ No overlay
  | OverlaySolid String Number             -- ^ Solid color with opacity
  | OverlayGradient GradientDirection String String Number
                                           -- ^ Gradient overlay

derive instance eqOverlayConfig :: Eq OverlayConfig

instance showOverlayConfig :: Show OverlayConfig where
  show OverlayNone = "none"
  show (OverlaySolid _ _) = "solid"
  show (OverlayGradient _ _ _ _) = "gradient"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gradient direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gradient direction
data GradientDirection
  = GradientTop           -- ^ Top to bottom
  | GradientBottom        -- ^ Bottom to top
  | GradientLeft          -- ^ Left to right
  | GradientRight         -- ^ Right to left

derive instance eqGradientDirection :: Eq GradientDirection

instance showGradientDirection :: Show GradientDirection where
  show GradientTop = "to-bottom"
  show GradientBottom = "to-top"
  show GradientLeft = "to-right"
  show GradientRight = "to-left"
