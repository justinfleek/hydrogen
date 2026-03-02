-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // element // component // card // media // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Media Config — Configuration type and constructors for media zones.
-- |
-- | ## Overview
-- |
-- | This module contains the MediaConfig type that brings together all
-- | media configuration options, plus constructor functions for creating
-- | media configurations.
-- |
-- | ## Dependencies
-- |
-- | - Types (MediaPosition, MediaType, MediaSource, AspectRatio, ObjectFit, MediaDimension)
-- | - Loading (LoadingStrategy, MediaPlaceholder, AutoplayBehavior)
-- | - Overlay (OverlayConfig)

module Hydrogen.Element.Compound.Card.Media.Config
  ( -- * Media Config
    MediaConfig
        ( MediaConfig
        )
  , mediaConfig
  , defaultMediaConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (<>)
  , (<)
  , (>)
  , otherwise
  , show
  )

import Hydrogen.Element.Compound.Card.Media.Types
  ( MediaPosition
      ( MediaTop
      )
  , MediaType
      ( MediaImage
      )
  , MediaSource
      ( SourceUrl
      )
  , AspectRatio
      ( Ratio16x9
      )
  , ObjectFit
      ( FitCover
      )
  , MediaDimension
      ( DimAuto
      , DimFill
      )
  )

import Hydrogen.Element.Compound.Card.Media.Loading
  ( LoadingStrategy
      ( LoadLazy
      )
  , MediaPlaceholder
      ( PlaceholderSkeleton
      )
  , AutoplayBehavior
      ( AutoplayNever
      )
  )

import Hydrogen.Element.Compound.Card.Media.Overlay
  ( OverlayConfig
      ( OverlayNone
      )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // media config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete media configuration for card media zones.
-- |
-- | ## Configuration Fields
-- |
-- | - `source`: Media source (URL or embedded data)
-- | - `mediaType`: Type of media content (image, video, Lottie, etc.)
-- | - `position`: Where media appears in the card
-- | - `aspectRatio`: Aspect ratio constraint
-- | - `objectFit`: How media fits within its container
-- | - `alt`: Accessible alternative text
-- | - `loading`: Loading strategy (lazy, eager)
-- | - `autoplay`: Video/Lottie autoplay behavior
-- | - `muted`: Video mute state
-- | - `loop`: Video/Lottie loop behavior
-- | - `overlay`: Optional color overlay for cover media
-- | - `overlayOpacity`: Overlay opacity (0.0 to 1.0)
-- | - `parallaxEnabled`: Enable parallax scrolling effect
-- | - `parallaxIntensity`: Parallax movement intensity
-- | - `borderRadius`: Corner radius for media
-- | - `grayscale`: Apply grayscale filter
-- | - `grayscaleOnHover`: Toggle grayscale on hover
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple hero image
-- | heroMedia = mediaConfig
-- |   { source: sourceUrl "/images/hero.jpg"
-- |   , mediaType: MediaImage
-- |   , position: MediaTop
-- |   , aspectRatio: Ratio16x9
-- |   , objectFit: FitCover
-- |   , alt: "Product hero image"
-- |   }
-- |
-- | -- Video preview on hover
-- | videoPreview = mediaConfig
-- |   { source: sourceUrl "/videos/preview.mp4"
-- |   , mediaType: MediaVideo
-- |   , position: MediaCover
-- |   , autoplay: AutoplayOnHover
-- |   , muted: true
-- |   , loop: true
-- |   }
-- | ```
newtype MediaConfig = MediaConfig
  { -- Source
    source :: MediaSource               -- ^ Media source
  , mediaType :: MediaType              -- ^ Type of media
  
  -- Position & Sizing
  , position :: MediaPosition           -- ^ Position within card
  , aspectRatio :: AspectRatio          -- ^ Aspect ratio constraint
  , objectFit :: ObjectFit              -- ^ How media fits container
  , width :: MediaDimension             -- ^ Width constraint
  , height :: MediaDimension            -- ^ Height constraint
  
  -- Accessibility
  , alt :: String                       -- ^ Alternative text
  
  -- Loading
  , loading :: LoadingStrategy          -- ^ Loading strategy
  , placeholder :: MediaPlaceholder     -- ^ Placeholder while loading
  
  -- Video/Animation Behavior
  , autoplay :: AutoplayBehavior        -- ^ Autoplay behavior
  , muted :: Boolean                    -- ^ Mute video audio
  , loop :: Boolean                     -- ^ Loop video/animation
  , playbackRate :: Number              -- ^ Playback speed (1.0 = normal)
  
  -- Overlay (for cover/background media)
  , overlay :: OverlayConfig            -- ^ Color overlay config
  
  -- Effects
  , parallaxEnabled :: Boolean          -- ^ Enable parallax effect
  , parallaxIntensity :: Number         -- ^ Parallax intensity (0.0 to 1.0)
  , grayscale :: Boolean                -- ^ Apply grayscale filter
  , grayscaleOnHover :: Boolean         -- ^ Remove grayscale on hover
  , blur :: Number                      -- ^ Blur amount in pixels
  
  -- Styling
  , borderRadius :: Number              -- ^ Corner radius in pixels
  }

derive instance eqMediaConfig :: Eq MediaConfig

instance showMediaConfig :: Show MediaConfig where
  show (MediaConfig c) = 
    "MediaConfig(" <> show c.mediaType <> 
    " @ " <> show c.position <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create media config with full options
mediaConfig
  :: { source :: MediaSource
     , mediaType :: MediaType
     , position :: MediaPosition
     , aspectRatio :: AspectRatio
     , objectFit :: ObjectFit
     , width :: MediaDimension
     , height :: MediaDimension
     , alt :: String
     , loading :: LoadingStrategy
     , placeholder :: MediaPlaceholder
     , autoplay :: AutoplayBehavior
     , muted :: Boolean
     , loop :: Boolean
     , playbackRate :: Number
     , overlay :: OverlayConfig
     , parallaxEnabled :: Boolean
     , parallaxIntensity :: Number
     , grayscale :: Boolean
     , grayscaleOnHover :: Boolean
     , blur :: Number
     , borderRadius :: Number
     }
  -> MediaConfig
mediaConfig cfg = MediaConfig
  { source: cfg.source
  , mediaType: cfg.mediaType
  , position: cfg.position
  , aspectRatio: cfg.aspectRatio
  , objectFit: cfg.objectFit
  , width: cfg.width
  , height: cfg.height
  , alt: cfg.alt
  , loading: cfg.loading
  , placeholder: cfg.placeholder
  , autoplay: cfg.autoplay
  , muted: cfg.muted
  , loop: cfg.loop
  , playbackRate: clampPlaybackRate cfg.playbackRate
  , overlay: cfg.overlay
  , parallaxEnabled: cfg.parallaxEnabled
  , parallaxIntensity: clampIntensity cfg.parallaxIntensity
  , grayscale: cfg.grayscale
  , grayscaleOnHover: cfg.grayscaleOnHover
  , blur: clampBlur cfg.blur
  , borderRadius: clampRadius cfg.borderRadius
  }
  where
    clampPlaybackRate r
      | r < 0.25 = 0.25
      | r > 4.0 = 4.0
      | otherwise = r
    clampIntensity i
      | i < 0.0 = 0.0
      | i > 1.0 = 1.0
      | otherwise = i
    clampBlur b
      | b < 0.0 = 0.0
      | b > 100.0 = 100.0
      | otherwise = b
    clampRadius r
      | r < 0.0 = 0.0
      | r > 100.0 = 100.0
      | otherwise = r

-- | Default media config for a simple image
defaultMediaConfig :: MediaConfig
defaultMediaConfig = MediaConfig
  { source: SourceUrl ""
  , mediaType: MediaImage
  , position: MediaTop
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: ""
  , loading: LoadLazy
  , placeholder: PlaceholderSkeleton
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.2
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }
