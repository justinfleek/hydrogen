-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // carousel // item config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Item Config — Configuration bundles for carousel items.
-- |
-- | ## Design Philosophy
-- |
-- | ItemConfig bundles all item styling options:
-- | - Shape clipping
-- | - Border styling
-- | - Hover effects
-- | - Sizing and spacing
-- |
-- | ## Dependencies
-- |
-- | - Item.Shape for shape configuration
-- | - Item.Border for border configuration
-- | - Item.Hover for hover configuration
-- | - Data.Maybe for optional sizing

module Hydrogen.Element.Compound.Carousel.Item.Config
  ( ItemConfig(..)
  , itemConfig
  , defaultItemConfig
  , imageItemConfig
  , cardItemConfig
  , interactiveItemConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Element.Compound.Carousel.Item.Shape
  ( ItemShape
      ( ShapeRectangle
      , ShapeNone
      )
  )

import Hydrogen.Element.Compound.Carousel.Item.Border
  ( ItemBorder
      ( BorderNone
      , BorderSolid
      )
  , glowingBorder
  )

import Hydrogen.Element.Compound.Carousel.Item.Hover
  ( ItemHover
      ( HoverNone
      , HoverScale
      , HoverLift
      )
  , combinedHoverWith
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete item configuration.
-- |
-- | Bundles all item styling options:
-- | - Shape clipping
-- | - Border styling
-- | - Hover effects
-- | - Sizing and spacing
-- |
-- | ## Sizing
-- |
-- | Items can have fixed or flexible sizing:
-- | - Fixed: Exact pixel dimensions
-- | - Flexible: Percentage or aspect ratio based
-- |
-- | ## Spacing
-- |
-- | Gap between items in the carousel is controlled at the carousel level,
-- | but items can have internal padding.
newtype ItemConfig = ItemConfig
  { shape :: ItemShape              -- ^ Shape clipping mask
  , border :: ItemBorder            -- ^ Border styling
  , hover :: ItemHover              -- ^ Hover effects
  , padding :: Number               -- ^ Internal padding (pixels)
  , aspectRatio :: Maybe Number     -- ^ Aspect ratio (width/height)
  , minWidth :: Maybe Number        -- ^ Minimum width (pixels)
  , maxWidth :: Maybe Number        -- ^ Maximum width (pixels)
  , className :: String             -- ^ Additional CSS class
  , ariaLabel :: String             -- ^ Accessibility label
  }

derive instance eqItemConfig :: Eq ItemConfig

instance showItemConfig :: Show ItemConfig where
  show (ItemConfig c) = 
    "ItemConfig(" <> show c.shape <> 
    ", " <> show c.border <> 
    ", " <> show c.hover <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create item config with all options
itemConfig
  :: { shape :: ItemShape
     , border :: ItemBorder
     , hover :: ItemHover
     , padding :: Number
     , aspectRatio :: Maybe Number
     , minWidth :: Maybe Number
     , maxWidth :: Maybe Number
     , className :: String
     , ariaLabel :: String
     }
  -> ItemConfig
itemConfig cfg = ItemConfig
  { shape: cfg.shape
  , border: cfg.border
  , hover: cfg.hover
  , padding: clampPadding cfg.padding
  , aspectRatio: cfg.aspectRatio
  , minWidth: cfg.minWidth
  , maxWidth: cfg.maxWidth
  , className: cfg.className
  , ariaLabel: cfg.ariaLabel
  }
  where
    clampPadding p
      | p < 0.0 = 0.0
      | p > 100.0 = 100.0
      | otherwise = p

-- | Default item config (no shape, no border, no hover)
defaultItemConfig :: ItemConfig
defaultItemConfig = ItemConfig
  { shape: ShapeNone
  , border: BorderNone
  , hover: HoverNone
  , padding: 0.0
  , aspectRatio: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , className: ""
  , ariaLabel: "Carousel item"
  }

-- | Image-optimized config (cover fit, subtle hover)
imageItemConfig :: ItemConfig
imageItemConfig = ItemConfig
  { shape: ShapeRectangle 8.0
  , border: BorderNone
  , hover: HoverScale 1.02 200.0
  , padding: 0.0
  , aspectRatio: Just 1.0
  , minWidth: Nothing
  , maxWidth: Nothing
  , className: "image-item"
  , ariaLabel: "Image"
  }

-- | Card-optimized config (padding, shadow feel)
cardItemConfig :: ItemConfig
cardItemConfig = ItemConfig
  { shape: ShapeRectangle 12.0
  , border: BorderSolid 1.0 "#E5E7EB"
  , hover: HoverLift 4.0 200.0
  , padding: 16.0
  , aspectRatio: Nothing
  , minWidth: Just 280.0
  , maxWidth: Just 400.0
  , className: "card-item"
  , ariaLabel: "Card"
  }

-- | Interactive config (audio + animation)
interactiveItemConfig :: String -> String -> ItemConfig
interactiveItemConfig audioUrl lottieUrl = ItemConfig
  { shape: ShapeRectangle 8.0
  , border: glowingBorder
  , hover: combinedHoverWith (Just audioUrl) (Just lottieUrl) 1.05
  , padding: 8.0
  , aspectRatio: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , className: "interactive-item"
  , ariaLabel: "Interactive item"
  }
