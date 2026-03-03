-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // scraper // types // image
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Image extraction types for 1:1 visual parity.
-- |
-- | Captures all image-related properties:
-- | - Source URL and content hash for identity
-- | - Natural dimensions vs rendered dimensions
-- | - Object fit and position
-- | - Aspect ratio and loading state

module Hydrogen.Scraper.Types.Image
  ( -- * Types
    ExtractedImage
  , ObjectFit(..)
  , ObjectPosition
  
  -- * Constructors
  , emptyImage
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Device (px) as Dev

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // object fit
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS object-fit property values
data ObjectFit
  = Fill        -- ^ Stretch to fill (distorts aspect ratio)
  | Contain     -- ^ Scale to fit within container (letterbox)
  | Cover       -- ^ Scale to cover container (crops)
  | None        -- ^ Natural size (may overflow)
  | ScaleDown   -- ^ Like contain but never upscales

derive instance eqObjectFit :: Eq ObjectFit

instance showObjectFit :: Show ObjectFit where
  show Fill = "fill"
  show Contain = "contain"
  show Cover = "cover"
  show None = "none"
  show ScaleDown = "scale-down"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // object position
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS object-position as percentages (0-100)
type ObjectPosition =
  { x :: Number  -- ^ Horizontal position (0 = left, 50 = center, 100 = right)
  , y :: Number  -- ^ Vertical position (0 = top, 50 = center, 100 = bottom)
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // extracted image
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete image extraction for 1:1 parity
type ExtractedImage =
  { -- Source identification
    src :: String              -- ^ URL or data URI
  , alt :: String              -- ^ Alt text for accessibility
  , contentHash :: Maybe String -- ^ SHA256 of image content for UUID5
  
  -- Natural dimensions (intrinsic image size)
  , naturalWidth :: Pixel
  , naturalHeight :: Pixel
  
  -- Rendered dimensions (how it appears on page)
  , renderedWidth :: Pixel
  , renderedHeight :: Pixel
  
  -- Positioning within container
  , objectFit :: ObjectFit
  , objectPosition :: ObjectPosition
  
  -- Loading state
  , isLoaded :: Boolean
  , isDecoded :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty image with default values
emptyImage :: ExtractedImage
emptyImage =
  { src: ""
  , alt: ""
  , contentHash: Nothing
  , naturalWidth: Dev.px 0.0
  , naturalHeight: Dev.px 0.0
  , renderedWidth: Dev.px 0.0
  , renderedHeight: Dev.px 0.0
  , objectFit: Fill
  , objectPosition: { x: 50.0, y: 50.0 }
  , isLoaded: false
  , isDecoded: false
  }
