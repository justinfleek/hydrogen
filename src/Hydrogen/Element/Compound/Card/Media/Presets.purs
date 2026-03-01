-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // element // component // card // media // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Media Presets — Common media configuration presets.
-- |
-- | ## Overview
-- |
-- | This module contains preset functions for common media configurations:
-- | - Hero images
-- | - Thumbnails
-- | - Cover images with overlays
-- | - Video previews
-- | - Avatars
-- | - Parallax backgrounds
-- | - Lottie animations
-- |
-- | ## Dependencies
-- |
-- | - Config (MediaConfig)
-- | - Types (MediaPosition, MediaType, MediaSource, AspectRatio, ObjectFit, MediaDimension)
-- | - Loading (LoadingStrategy, MediaPlaceholder, AutoplayBehavior)
-- | - Overlay (OverlayConfig, GradientDirection)

module Hydrogen.Element.Compound.Card.Media.Presets
  ( -- * Presets
    heroImage
  , squareThumbnail
  , coverWithOverlay
  , videoPreview
  , avatarMedia
  , parallaxBackground
  , lottieMedia
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Card.Media.Config
  ( MediaConfig
      ( MediaConfig
      )
  )

import Hydrogen.Element.Compound.Card.Media.Types
  ( MediaPosition
      ( MediaTop
      , MediaLeft
      , MediaCover
      , MediaBackground
      )
  , MediaType
      ( MediaImage
      , MediaVideo
      , MediaLottie
      , MediaAvatar
      )
  , MediaSource
  , AspectRatio
      ( Ratio16x9
      , Ratio1x1
      )
  , ObjectFit
      ( FitCover
      , FitContain
      )
  , MediaDimension
      ( DimAuto
      , DimPixels
      , DimFill
      )
  )

import Hydrogen.Element.Compound.Card.Media.Loading
  ( LoadingStrategy
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
  , AutoplayBehavior
      ( AutoplayNever
      , AutoplayOnHover
      , AutoplayInViewport
      )
  )

import Hydrogen.Element.Compound.Card.Media.Overlay
  ( OverlayConfig
      ( OverlayNone
      , OverlaySolid
      , OverlayGradient
      )
  , GradientDirection
      ( GradientBottom
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hero image preset (full-width top image)
heroImage :: MediaSource -> String -> MediaConfig
heroImage src altText = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaTop
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: altText
  , loading: LoadEager
  , placeholder: PlaceholderShimmer
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Square thumbnail preset (1:1 ratio)
squareThumbnail :: MediaSource -> String -> MediaConfig
squareThumbnail src altText = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaTop
  , aspectRatio: Ratio1x1
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: altText
  , loading: LoadLazy
  , placeholder: PlaceholderSkeleton
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 8.0
  }

-- | Cover media with dark overlay (for text readability)
coverWithOverlay :: MediaSource -> String -> String -> Number -> MediaConfig
coverWithOverlay src altText overlayColor overlayOpacity = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaCover
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimFill
  , alt: altText
  , loading: LoadEager
  , placeholder: PlaceholderColor overlayColor
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlaySolid overlayColor overlayOpacity
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Video preview (plays on hover)
videoPreview :: MediaSource -> MediaConfig
videoPreview src = MediaConfig
  { source: src
  , mediaType: MediaVideo
  , position: MediaTop
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: "Video preview"
  , loading: LoadOnHover
  , placeholder: PlaceholderSkeleton
  , autoplay: AutoplayOnHover
  , muted: true
  , loop: true
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Avatar preset (circular profile image)
avatarMedia :: MediaSource -> String -> MediaConfig
avatarMedia src altText = MediaConfig
  { source: src
  , mediaType: MediaAvatar
  , position: MediaLeft
  , aspectRatio: Ratio1x1
  , objectFit: FitCover
  , width: DimPixels 48.0
  , height: DimPixels 48.0
  , alt: altText
  , loading: LoadLazy
  , placeholder: PlaceholderShimmer
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 50.0
  }

-- | Background with parallax effect
parallaxBackground :: MediaSource -> String -> MediaConfig
parallaxBackground src altText = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaBackground
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimFill
  , alt: altText
  , loading: LoadEager
  , placeholder: PlaceholderBlur ""
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayGradient GradientBottom "#000000" "#00000000" 0.5
  , parallaxEnabled: true
  , parallaxIntensity: 0.3
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Lottie animation preset
lottieMedia :: MediaSource -> MediaConfig
lottieMedia src = MediaConfig
  { source: src
  , mediaType: MediaLottie
  , position: MediaTop
  , aspectRatio: Ratio1x1
  , objectFit: FitContain
  , width: DimFill
  , height: DimAuto
  , alt: "Animation"
  , loading: LoadLazy
  , placeholder: PlaceholderNone
  , autoplay: AutoplayInViewport
  , muted: true
  , loop: true
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }
