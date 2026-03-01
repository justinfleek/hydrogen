-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // carousel // item
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Item — Content wrapper with shape, border, and hover effects.
-- |
-- | ## Design Philosophy
-- |
-- | An Item is the container for carousel content. It wraps content with:
-- | - Shape masking (star, hexagon, custom SVG)
-- | - Animated borders (gradient strokes, glowing edges)
-- | - Hover effects (audio triggers, Lottie animations)
-- |
-- | Items can contain:
-- | - Images, videos, point clouds
-- | - Cards (full Card compound)
-- | - Lottie animations
-- | - Custom elements
-- |
-- | ## Architecture
-- |
-- | ```
-- | Item
-- |   └─ ItemShape (geometry mask)
-- |   └─ ItemBorder (animated stroke)
-- |   └─ ItemHover (hover behaviors)
-- |   └─ ItemContent (actual content)
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - Item.Shape — Shape clipping masks
-- | - Item.Border — Border effects
-- | - Item.Hover — Hover interactions
-- | - Item.Content — Content types
-- | - Item.Config — Configuration bundles

module Hydrogen.Element.Compound.Carousel.Item
  ( -- * Item Shape
    module Shape
  
    -- * Item Border
  , module Border
  
    -- * Item Hover
  , module Hover
  
    -- * Item Content
  , module Content
  
    -- * Item Config
  , module Config
  
    -- * Complete Item
  , Item(..)
  , item
  , simpleItem
  , imageItem
  , videoItem
  , lottieItem
  , cardItem
  , interactiveItem
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Carousel.Item.Shape
  ( ItemShape
      ( ShapeRectangle
      , ShapeCircle
      , ShapeEllipse
      , ShapePolygon
      , ShapeStar
      , ShapeSvgPath
      , ShapeNone
      )
  , itemShape
  , noItemShape
  , rectangleShape
  , starItem
  , starItemWithRatio
  , hexagonItem
  , octagonItem
  , circleItem
  , ellipseItem
  , polygonItem
  , customShapeItem
  ) as Shape

import Hydrogen.Element.Compound.Carousel.Item.Border
  ( ItemBorder
      ( BorderNone
      , BorderSolid
      , BorderGradientLinear
      , BorderGradientConic
      , BorderGlow
      , BorderDashed
      , BorderAnimatedDash
      , BorderPulse
      , BorderRainbow
      )
  , itemBorder
  , noItemBorder
  , solidBorder
  , glowingBorder
  , glowingBorderWith
  , gradientBorder
  , gradientBorderWith
  , animatedDashBorder
  , animatedDashBorderWith
  , dashedBorder
  , pulseBorder
  , rainbowBorder
  ) as Border

import Hydrogen.Element.Compound.Carousel.Item.Hover
  ( ItemHover
      ( HoverNone
      , HoverAudio
      , HoverAudioEnterLeave
      , HoverLottie
      , HoverLottieReverse
      , HoverScale
      , HoverLift
      , HoverCombined
      )
  , ItemHoverConfig
  , itemHover
  , noItemHover
  , audioOnHover
  , audioOnHoverWith
  , audioOnHoverEnterLeave
  , lottieOnHover
  , lottieOnHoverReverse
  , scaleOnHover
  , liftOnHover
  , combinedHover
  , combinedHoverWith
  , defaultHoverConfig
  ) as Hover

import Hydrogen.Element.Compound.Carousel.Item.Content
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
  ) as Content

import Hydrogen.Element.Compound.Carousel.Item.Config
  ( ItemConfig(..)
  , itemConfig
  , defaultItemConfig
  , imageItemConfig
  , cardItemConfig
  , interactiveItemConfig
  ) as Config

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete carousel item.
-- |
-- | Combines content with configuration to create a fully-specified
-- | carousel item ready for rendering.
-- |
-- | ## Structure
-- |
-- | ```
-- | Item
-- |   ├─ content: ItemContent    (what to display)
-- |   └─ config: ItemConfig      (how to display it)
-- | ```
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple image item
-- | photoItem = simpleItem (imageContent "/photo.jpg" "Beach sunset")
-- |
-- | -- Interactive dog card
-- | dogItem = item
-- |   (imageContent "/dog.jpg" "Happy dog")
-- |   (interactiveItemConfig "/sounds/bark.mp3" "/animations/wag.json")
-- | ```
newtype Item = Item
  { content :: Content.ItemContent  -- ^ What to display
  , config :: Config.ItemConfig     -- ^ How to display it
  }

derive instance eqItem :: Eq Item

instance showItem :: Show Item where
  show (Item i) = 
    "Item(" <> show i.content <> ", " <> show i.config <> ")"

-- | Create complete item with content and config
item :: Content.ItemContent -> Config.ItemConfig -> Item
item content config = Item
  { content: content
  , config: config
  }

-- | Simple item (content only, default styling)
simpleItem :: Content.ItemContent -> Item
simpleItem content = Item
  { content: content
  , config: Config.defaultItemConfig
  }

-- | Image item with default image styling
imageItem :: String -> String -> Item
imageItem url alt = Item
  { content: Content.imageContent url alt
  , config: Config.imageItemConfig
  }

-- | Video item with default video styling
videoItem :: String -> String -> Item
videoItem url poster = Item
  { content: Content.videoContent url poster
  , config: Config.defaultItemConfig
  }

-- | Lottie item
lottieItem :: String -> Item
lottieItem url = Item
  { content: Content.ContentLottie url
  , config: Config.defaultItemConfig
  }

-- | Card item with title and image
cardItem :: String -> String -> Item
cardItem title imageUrl = Item
  { content: Content.ContentCard
      { title: Just title
      , subtitle: Nothing
      , description: Nothing
      , imageUrl: Just imageUrl
      , actionLabel: Nothing
      }
  , config: Config.cardItemConfig
  }

-- | Interactive item with audio and animation on hover
interactiveItem :: Content.ItemContent -> String -> String -> Item
interactiveItem content audioUrl lottieUrl = Item
  { content: content
  , config: Config.interactiveItemConfig audioUrl lottieUrl
  }
