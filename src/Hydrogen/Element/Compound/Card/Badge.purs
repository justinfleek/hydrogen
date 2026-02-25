-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // component // card // badge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Badge — Overlay badges, tags, and labels for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Badges are positioned overlays that communicate status, price, category,
-- | or other metadata. They can be placed at corners or edges.
-- |
-- | ## Badge Types
-- |
-- | - **Status**: "NEW", "SALE", "SOLD OUT", "HOT"
-- | - **Price**: "$19.99", "From $5"
-- | - **Rating**: "4.5 ★"
-- | - **Category**: "Electronics", "Fashion"
-- | - **Custom**: Any text/icon combination
-- |
-- | ## Use Cases
-- |
-- | - E-commerce product cards (price, sale badge)
-- | - Etsy/Amazon-style UGC cards
-- | - Article cards (category tag)
-- | - Profile cards (online status)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Color.RGB (badge colors)
-- | - Schema.Typography (text styling)

module Hydrogen.Element.Compound.Card.Badge
  ( -- * Badge Position
    BadgePosition
      ( BadgeTopLeft
      , BadgeTopRight
      , BadgeBottomLeft
      , BadgeBottomRight
      , BadgeTopCenter
      , BadgeBottomCenter
      )
  
  -- * Badge Variant
  , BadgeVariant
      ( BadgeStatus
      , BadgePrice
      , BadgeRating
      , BadgeCategory
      , BadgeCustom
      )
  
  -- * Badge Style
  , BadgeStyle
      ( StyleSolid
      , StyleOutline
      , StyleGlass
      , StyleGradient
      )
  
  -- * Badge Config
  , BadgeConfig
  , badgeConfig
  , defaultBadgeConfig
  
  -- * Presets
  , newBadge
  , saleBadge
  , soldOutBadge
  , hotBadge
  , priceBadge
  , ratingBadge
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // badge position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Position of badge on the card
data BadgePosition
  = BadgeTopLeft
  | BadgeTopRight
  | BadgeBottomLeft
  | BadgeBottomRight
  | BadgeTopCenter
  | BadgeBottomCenter

derive instance eqBadgePosition :: Eq BadgePosition
derive instance ordBadgePosition :: Ord BadgePosition

instance showBadgePosition :: Show BadgePosition where
  show BadgeTopLeft = "top-left"
  show BadgeTopRight = "top-right"
  show BadgeBottomLeft = "bottom-left"
  show BadgeBottomRight = "bottom-right"
  show BadgeTopCenter = "top-center"
  show BadgeBottomCenter = "bottom-center"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // badge variant
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Semantic badge type
data BadgeVariant
  = BadgeStatus       -- ^ Status indicator (NEW, SALE, etc.)
  | BadgePrice        -- ^ Price display
  | BadgeRating       -- ^ Rating display (stars)
  | BadgeCategory     -- ^ Category/tag
  | BadgeCustom       -- ^ Custom content

derive instance eqBadgeVariant :: Eq BadgeVariant
derive instance ordBadgeVariant :: Ord BadgeVariant

instance showBadgeVariant :: Show BadgeVariant where
  show BadgeStatus = "status"
  show BadgePrice = "price"
  show BadgeRating = "rating"
  show BadgeCategory = "category"
  show BadgeCustom = "custom"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // badge style
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Visual style of the badge
data BadgeStyle
  = StyleSolid        -- ^ Solid background
  | StyleOutline      -- ^ Border only, transparent fill
  | StyleGlass        -- ^ Frosted glass effect
  | StyleGradient     -- ^ Gradient background

derive instance eqBadgeStyle :: Eq BadgeStyle
derive instance ordBadgeStyle :: Ord BadgeStyle

instance showBadgeStyle :: Show BadgeStyle where
  show StyleSolid = "solid"
  show StyleOutline = "outline"
  show StyleGlass = "glass"
  show StyleGradient = "gradient"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // badge config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete badge configuration
data BadgeConfig = BadgeConfigPlaceholder

derive instance eqBadgeConfig :: Eq BadgeConfig

instance showBadgeConfig :: Show BadgeConfig where
  show _ = "BadgeConfig"

-- | Create badge config (placeholder)
badgeConfig :: BadgeConfig
badgeConfig = BadgeConfigPlaceholder

-- | Default badge config
defaultBadgeConfig :: BadgeConfig
defaultBadgeConfig = BadgeConfigPlaceholder

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // presets
-- ═══════════════════════════════════════════════════════════════════════════════

-- | "NEW" badge preset
newBadge :: BadgeConfig
newBadge = BadgeConfigPlaceholder

-- | "SALE" badge preset
saleBadge :: BadgeConfig
saleBadge = BadgeConfigPlaceholder

-- | "SOLD OUT" badge preset
soldOutBadge :: BadgeConfig
soldOutBadge = BadgeConfigPlaceholder

-- | "HOT" badge preset
hotBadge :: BadgeConfig
hotBadge = BadgeConfigPlaceholder

-- | Price badge preset (placeholder)
priceBadge :: BadgeConfig
priceBadge = BadgeConfigPlaceholder

-- | Rating badge preset (placeholder)
ratingBadge :: BadgeConfig
ratingBadge = BadgeConfigPlaceholder
