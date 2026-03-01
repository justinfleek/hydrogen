-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // card // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Media — Media zones for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Media (images, videos, Lottie animations) can be positioned in various
-- | zones within a card:
-- | - Top/Bottom: Full-width media above/below content
-- | - Left/Right: Side-by-side with content
-- | - Cover: Full background with overlay
-- | - Background: Behind content (parallax capable)
-- |
-- | ## Use Cases
-- |
-- | - Product cards with hero images
-- | - Profile cards with avatars
-- | - Article cards with cover images
-- | - Portfolio items with video previews
-- |
-- | ## Submodules
-- |
-- | - Types: Core type definitions (MediaPosition, MediaType, etc.)
-- | - Loading: Loading strategies and placeholders
-- | - Overlay: Overlay configuration
-- | - Config: MediaConfig type and constructors
-- | - Presets: Common media configuration presets
-- |
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Device (sizing)

module Hydrogen.Element.Compound.Card.Media
  ( module Types
  , module Loading
  , module Overlay
  , module Config
  , module Presets
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Card.Media.Types
  ( AspectRatio
      ( Ratio16x9
      , Ratio4x3
      , Ratio1x1
      , Ratio3x2
      , Ratio21x9
      , RatioCustom
      )
  , MediaDimension
      ( DimAuto
      , DimPixels
      , DimPercent
      , DimFill
      )
  , MediaPosition
      ( MediaTop
      , MediaBottom
      , MediaLeft
      , MediaRight
      , MediaCover
      , MediaBackground
      )
  , MediaSource
      ( SourceUrl
      , SourceData
      )
  , MediaType
      ( MediaImage
      , MediaVideo
      , MediaLottie
      , MediaIcon
      , MediaAvatar
      )
  , ObjectFit
      ( FitCover
      , FitContain
      , FitFill
      , FitNone
      , FitScaleDown
      )
  , aspectRatio
  , sourceData
  , sourceUrl
  ) as Types

import Hydrogen.Element.Compound.Card.Media.Loading
  ( AutoplayBehavior
      ( AutoplayNever
      , AutoplayAlways
      , AutoplayOnHover
      , AutoplayInViewport
      )
  , LoadingStrategy
      ( LoadEager
      , LoadLazy
      , LoadOnHover
      )
  , MediaPlaceholder
      ( PlaceholderNone
      , PlaceholderColor
      , PlaceholderBlur
      , PlaceholderShimmer
      , PlaceholderSkeleton
      )
  ) as Loading

import Hydrogen.Element.Compound.Card.Media.Overlay
  ( GradientDirection
      ( GradientTop
      , GradientBottom
      , GradientLeft
      , GradientRight
      )
  , OverlayConfig
      ( OverlayNone
      , OverlaySolid
      , OverlayGradient
      )
  ) as Overlay

import Hydrogen.Element.Compound.Card.Media.Config
  ( MediaConfig
      ( MediaConfig
      )
  , defaultMediaConfig
  , mediaConfig
  ) as Config

import Hydrogen.Element.Compound.Card.Media.Presets
  ( avatarMedia
  , coverWithOverlay
  , heroImage
  , lottieMedia
  , parallaxBackground
  , squareThumbnail
  , videoPreview
  ) as Presets
