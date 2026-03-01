-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // carousel // item content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Item Content — Content types for carousel items.
-- |
-- | ## Design Philosophy
-- |
-- | Each carousel item wraps a piece of content:
-- | - Images with lazy loading and srcset support
-- | - Videos with autoplay and poster options
-- | - Card compounds (full Card component)
-- | - Lottie animations
-- | - Point clouds (3D data visualization)
-- | - Custom elements (user-provided)
-- |
-- | ## Dependencies
-- |
-- | - Data.Maybe for optional configuration fields

module Hydrogen.Element.Compound.Carousel.Item.Content
  ( ItemContent
      ( ContentImage
      , ContentVideo
      , ContentCard
      , ContentLottie
      , ContentPointCloud
      , ContentCustom
      )
  , ImageConfig
  , ImageLoading(LoadLazy, LoadEager)
  , ObjectFit(FitContain, FitCover, FitFill, FitNone, FitScaleDown)
  , VideoConfig
  , CardConfig
  , PointCloudConfig
  , PointColorMode(ColorFromData, ColorUniform, ColorByHeight, ColorByDepth)
  , imageContent
  , imageContentWith
  , videoContent
  , videoContentWith
  , cardContent
  , cardContentWith
  , lottieContent
  , pointCloudContent
  , customContent
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content types for carousel items.
-- |
-- | Each carousel item wraps a piece of content:
-- | - Images with lazy loading and srcset support
-- | - Videos with autoplay and poster options
-- | - Card compounds (full Card component)
-- | - Lottie animations
-- | - Point clouds (3D data visualization)
-- | - Custom elements (user-provided)
-- |
-- | ## Image Options
-- |
-- | Images support:
-- | - url: Main image URL
-- | - alt: Accessibility text
-- | - srcset: Responsive image sources
-- | - loading: lazy or eager
-- |
-- | ## Video Options
-- |
-- | Videos support:
-- | - url: Video file URL
-- | - poster: Preview image URL
-- | - autoplay, loop, muted flags
data ItemContent
  = ContentImage ImageConfig                      -- ^ Image with configuration
  | ContentVideo VideoConfig                      -- ^ Video with configuration
  | ContentCard CardConfig                        -- ^ Card compound
  | ContentLottie String                          -- ^ Lottie animation URL
  | ContentPointCloud PointCloudConfig            -- ^ 3D point cloud
  | ContentCustom String                          -- ^ Custom element ID/type

-- | Image content configuration
type ImageConfig =
  { url :: String                   -- ^ Image URL
  , alt :: String                   -- ^ Alt text for accessibility
  , srcset :: Maybe String          -- ^ Responsive srcset
  , loading :: ImageLoading         -- ^ Loading strategy
  , objectFit :: ObjectFit          -- ^ How image fits container
  }

-- | Image loading strategy
data ImageLoading
  = LoadLazy                        -- ^ Lazy load when near viewport
  | LoadEager                       -- ^ Load immediately

derive instance eqImageLoading :: Eq ImageLoading

instance showImageLoading :: Show ImageLoading where
  show LoadLazy = "lazy"
  show LoadEager = "eager"

-- | Object fit mode
data ObjectFit
  = FitContain                      -- ^ Scale to fit, preserve aspect
  | FitCover                        -- ^ Scale to cover, may crop
  | FitFill                         -- ^ Stretch to fill
  | FitNone                         -- ^ No scaling
  | FitScaleDown                    -- ^ Scale down if needed

derive instance eqObjectFit :: Eq ObjectFit

instance showObjectFit :: Show ObjectFit where
  show FitContain = "contain"
  show FitCover = "cover"
  show FitFill = "fill"
  show FitNone = "none"
  show FitScaleDown = "scale-down"

-- | Video content configuration
type VideoConfig =
  { url :: String                   -- ^ Video URL
  , poster :: Maybe String          -- ^ Poster image URL
  , autoplay :: Boolean             -- ^ Autoplay on load
  , loop :: Boolean                 -- ^ Loop playback
  , muted :: Boolean                -- ^ Muted audio
  , controls :: Boolean             -- ^ Show video controls
  }

-- | Card content configuration
type CardConfig =
  { title :: Maybe String           -- ^ Card title
  , subtitle :: Maybe String        -- ^ Card subtitle
  , description :: Maybe String     -- ^ Card description
  , imageUrl :: Maybe String        -- ^ Card image
  , actionLabel :: Maybe String     -- ^ Action button label
  }

-- | Point cloud configuration
type PointCloudConfig =
  { dataUrl :: String               -- ^ Point cloud data URL (.ply, .pcd)
  , pointSize :: Number             -- ^ Point size in pixels
  , colorMode :: PointColorMode     -- ^ How points are colored
  }

-- | Point cloud coloring mode
data PointColorMode
  = ColorFromData                   -- ^ Use colors from data file
  | ColorUniform String             -- ^ Single color for all points
  | ColorByHeight                   -- ^ Color based on Y position
  | ColorByDepth                    -- ^ Color based on Z distance

derive instance eqPointColorMode :: Eq PointColorMode

instance showPointColorMode :: Show PointColorMode where
  show ColorFromData = "from-data"
  show (ColorUniform _) = "uniform"
  show ColorByHeight = "by-height"
  show ColorByDepth = "by-depth"

derive instance eqItemContent :: Eq ItemContent

instance showItemContent :: Show ItemContent where
  show (ContentImage _) = "image"
  show (ContentVideo _) = "video"
  show (ContentCard _) = "card"
  show (ContentLottie _) = "lottie"
  show (ContentPointCloud _) = "pointcloud"
  show (ContentCustom _) = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create image content with minimal config
imageContent :: String -> String -> ItemContent
imageContent url alt = ContentImage
  { url: url
  , alt: alt
  , srcset: Nothing
  , loading: LoadLazy
  , objectFit: FitCover
  }

-- | Create image with full configuration
imageContentWith :: ImageConfig -> ItemContent
imageContentWith = ContentImage

-- | Create video content with minimal config
videoContent :: String -> String -> ItemContent
videoContent url poster = ContentVideo
  { url: url
  , poster: Just poster
  , autoplay: false
  , loop: false
  , muted: true
  , controls: true
  }

-- | Create video with full configuration
videoContentWith :: VideoConfig -> ItemContent
videoContentWith = ContentVideo

-- | Create card content
cardContent :: ItemContent
cardContent = ContentCard
  { title: Nothing
  , subtitle: Nothing
  , description: Nothing
  , imageUrl: Nothing
  , actionLabel: Nothing
  }

-- | Create card with configuration
cardContentWith :: CardConfig -> ItemContent
cardContentWith = ContentCard

-- | Create Lottie content
lottieContent :: String -> ItemContent
lottieContent = ContentLottie

-- | Create point cloud content
pointCloudContent :: String -> ItemContent
pointCloudContent url = ContentPointCloud
  { dataUrl: url
  , pointSize: 2.0
  , colorMode: ColorFromData
  }

-- | Create custom element content
customContent :: String -> ItemContent
customContent = ContentCustom
