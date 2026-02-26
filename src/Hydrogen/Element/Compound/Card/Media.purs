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
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Device (sizing)

module Hydrogen.Element.Compound.Card.Media
  ( -- * Media Position
    MediaPosition
      ( MediaTop
      , MediaBottom
      , MediaLeft
      , MediaRight
      , MediaCover
      , MediaBackground
      )
  
  -- * Media Type
  , MediaType
      ( MediaImage
      , MediaVideo
      , MediaLottie
      , MediaIcon
      , MediaAvatar
      )
  
  -- * Media Config
  , MediaConfig
  , mediaConfig
  , defaultMediaConfig
  
  -- * Media Source
  , MediaSource
      ( SourceUrl
      , SourceData
      )
  , sourceUrl
  , sourceData
  
  -- * Aspect Ratio
  , AspectRatio
      ( Ratio16x9
      , Ratio4x3
      , Ratio1x1
      , Ratio3x2
      , Ratio21x9
      , RatioCustom
      )
  , aspectRatio
  
  -- * Object Fit
  , ObjectFit
      ( FitCover
      , FitContain
      , FitFill
      , FitNone
      , FitScaleDown
      )
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // media position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of media within the card
data MediaPosition
  = MediaTop          -- ^ Full-width at top
  | MediaBottom       -- ^ Full-width at bottom
  | MediaLeft         -- ^ Left side, content on right
  | MediaRight        -- ^ Right side, content on left
  | MediaCover        -- ^ Full card background with content overlay
  | MediaBackground   -- ^ Behind content (can have parallax)

derive instance eqMediaPosition :: Eq MediaPosition
derive instance ordMediaPosition :: Ord MediaPosition

instance showMediaPosition :: Show MediaPosition where
  show MediaTop = "top"
  show MediaBottom = "bottom"
  show MediaLeft = "left"
  show MediaRight = "right"
  show MediaCover = "cover"
  show MediaBackground = "background"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // media type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of media content
data MediaType
  = MediaImage        -- ^ Static image
  | MediaVideo        -- ^ Video (auto-plays on hover typically)
  | MediaLottie       -- ^ Lottie animation
  | MediaIcon         -- ^ Icon/symbol
  | MediaAvatar       -- ^ Avatar/profile image (rounded)

derive instance eqMediaType :: Eq MediaType
derive instance ordMediaType :: Ord MediaType

instance showMediaType :: Show MediaType where
  show MediaImage = "image"
  show MediaVideo = "video"
  show MediaLottie = "lottie"
  show MediaIcon = "icon"
  show MediaAvatar = "avatar"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // media source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of media content
data MediaSource
  = SourceUrl String      -- ^ URL to media file
  | SourceData String     -- ^ Base64-encoded or data URI

derive instance eqMediaSource :: Eq MediaSource
derive instance ordMediaSource :: Ord MediaSource

instance showMediaSource :: Show MediaSource where
  show (SourceUrl _) = "url"
  show (SourceData _) = "data"

-- | Create URL media source
sourceUrl :: String -> MediaSource
sourceUrl = SourceUrl

-- | Create data media source
sourceData :: String -> MediaSource
sourceData = SourceData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // aspect ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aspect ratio presets
data AspectRatio
  = Ratio16x9         -- ^ Widescreen video (16:9)
  | Ratio4x3          -- ^ Traditional TV (4:3)
  | Ratio1x1          -- ^ Square
  | Ratio3x2          -- ^ Classic photo (3:2)
  | Ratio21x9         -- ^ Ultrawide (21:9)
  | RatioCustom Number Number  -- ^ Custom ratio (width:height)

derive instance eqAspectRatio :: Eq AspectRatio

instance showAspectRatio :: Show AspectRatio where
  show Ratio16x9 = "16/9"
  show Ratio4x3 = "4/3"
  show Ratio1x1 = "1/1"
  show Ratio3x2 = "3/2"
  show Ratio21x9 = "21/9"
  show (RatioCustom w h) = show w <> "/" <> show h

-- | Create aspect ratio
aspectRatio :: AspectRatio -> AspectRatio
aspectRatio = \r -> r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // object fit
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS object-fit values
data ObjectFit
  = FitCover          -- ^ Cover container, may crop
  | FitContain        -- ^ Fit inside container, may letterbox
  | FitFill           -- ^ Stretch to fill (distorts)
  | FitNone           -- ^ No resizing
  | FitScaleDown      -- ^ Like contain but never scales up

derive instance eqObjectFit :: Eq ObjectFit
derive instance ordObjectFit :: Ord ObjectFit

instance showObjectFit :: Show ObjectFit where
  show FitCover = "cover"
  show FitContain = "contain"
  show FitFill = "fill"
  show FitNone = "none"
  show FitScaleDown = "scale-down"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // media config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete media configuration
data MediaConfig = MediaConfigPlaceholder

derive instance eqMediaConfig :: Eq MediaConfig

instance showMediaConfig :: Show MediaConfig where
  show _ = "MediaConfig"

-- | Create media config (placeholder)
mediaConfig :: MediaConfig
mediaConfig = MediaConfigPlaceholder

-- | Default media config
defaultMediaConfig :: MediaConfig
defaultMediaConfig = MediaConfigPlaceholder
