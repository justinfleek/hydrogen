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
-- | ## Dependencies
-- |
-- | - Card.Shape (shape masking)
-- | - Card.Hover (hover effects)
-- | - Schema.Geometry.AnimatedBorder (border effects)

module Hydrogen.Element.Compound.Carousel.Item
  ( -- * Item Config
    ItemConfig
  , itemConfig
  , defaultItemConfig
  
  -- * Item Shape
  , ItemShape
  , itemShape
  , noItemShape
  , starItem
  , hexagonItem
  , circleItem
  , customShapeItem
  
  -- * Item Border
  , ItemBorder
  , itemBorder
  , noItemBorder
  , glowingBorder
  , gradientBorder
  , animatedDashBorder
  
  -- * Item Hover
  , ItemHover
  , itemHover
  , noItemHover
  , audioOnHover
  , lottieOnHover
  , combinedHover
  
  -- * Item Content
  , ItemContent
      ( ContentImage
      , ContentVideo
      , ContentCard
      , ContentLottie
      , ContentPointCloud
      , ContentElement
      )
  , imageContent
  , videoContent
  , cardContent
  , lottieContent
  
  -- * Complete Item
  , Item
  , item
  , simpleItem
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // item shape
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Shape configuration for an item
data ItemShape = ItemShapePlaceholder

derive instance eqItemShape :: Eq ItemShape

instance showItemShape :: Show ItemShape where
  show _ = "ItemShape"

-- | Create item shape
itemShape :: ItemShape
itemShape = ItemShapePlaceholder

-- | No shape (default rectangle)
noItemShape :: ItemShape
noItemShape = ItemShapePlaceholder

-- | Star-shaped item
starItem :: Int -> ItemShape
starItem _ = ItemShapePlaceholder

-- | Hexagon-shaped item
hexagonItem :: ItemShape
hexagonItem = ItemShapePlaceholder

-- | Circle-shaped item
circleItem :: ItemShape
circleItem = ItemShapePlaceholder

-- | Custom SVG path item
customShapeItem :: String -> ItemShape
customShapeItem _ = ItemShapePlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // item border
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Border configuration for an item
data ItemBorder = ItemBorderPlaceholder

derive instance eqItemBorder :: Eq ItemBorder

instance showItemBorder :: Show ItemBorder where
  show _ = "ItemBorder"

-- | Create item border
itemBorder :: ItemBorder
itemBorder = ItemBorderPlaceholder

-- | No border
noItemBorder :: ItemBorder
noItemBorder = ItemBorderPlaceholder

-- | Glowing border effect
glowingBorder :: ItemBorder
glowingBorder = ItemBorderPlaceholder

-- | Gradient stroke border
gradientBorder :: ItemBorder
gradientBorder = ItemBorderPlaceholder

-- | Animated dash border (marching ants)
animatedDashBorder :: ItemBorder
animatedDashBorder = ItemBorderPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // item hover
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Hover effect configuration for an item
data ItemHover = ItemHoverPlaceholder

derive instance eqItemHover :: Eq ItemHover

instance showItemHover :: Show ItemHover where
  show _ = "ItemHover"

-- | Create item hover
itemHover :: ItemHover
itemHover = ItemHoverPlaceholder

-- | No hover effects
noItemHover :: ItemHover
noItemHover = ItemHoverPlaceholder

-- | Play audio on hover
audioOnHover :: String -> ItemHover
audioOnHover _ = ItemHoverPlaceholder

-- | Start Lottie on hover
lottieOnHover :: String -> ItemHover
lottieOnHover _ = ItemHoverPlaceholder

-- | Combined hover effects
combinedHover :: ItemHover
combinedHover = ItemHoverPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // item content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Content types for carousel items
data ItemContent
  = ContentImage String String    -- ^ url, alt
  | ContentVideo String String    -- ^ url, alt
  | ContentCard                   -- ^ Card compound (placeholder)
  | ContentLottie String          -- ^ Lottie animation url
  | ContentPointCloud String      -- ^ Point cloud data url
  | ContentElement                -- ^ Custom element (placeholder)

derive instance eqItemContent :: Eq ItemContent

instance showItemContent :: Show ItemContent where
  show (ContentImage _ _) = "image"
  show (ContentVideo _ _) = "video"
  show ContentCard = "card"
  show (ContentLottie _) = "lottie"
  show (ContentPointCloud _) = "pointcloud"
  show ContentElement = "element"

-- | Create image content
imageContent :: String -> String -> ItemContent
imageContent = ContentImage

-- | Create video content
videoContent :: String -> String -> ItemContent
videoContent = ContentVideo

-- | Create card content (placeholder)
cardContent :: ItemContent
cardContent = ContentCard

-- | Create Lottie content
lottieContent :: String -> ItemContent
lottieContent = ContentLottie

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // item config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete item configuration
data ItemConfig = ItemConfigPlaceholder

derive instance eqItemConfig :: Eq ItemConfig

instance showItemConfig :: Show ItemConfig where
  show _ = "ItemConfig"

-- | Create item config
itemConfig :: ItemConfig
itemConfig = ItemConfigPlaceholder

-- | Default item config
defaultItemConfig :: ItemConfig
defaultItemConfig = ItemConfigPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // item
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete carousel item
data Item = ItemPlaceholder

derive instance eqItem :: Eq Item

instance showItem :: Show Item where
  show _ = "Item"

-- | Create complete item
item :: Item
item = ItemPlaceholder

-- | Simple item (content only, no effects)
simpleItem :: ItemContent -> Item
simpleItem _ = ItemPlaceholder
