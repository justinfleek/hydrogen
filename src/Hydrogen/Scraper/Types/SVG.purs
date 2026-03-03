-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // scraper // types // svg
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SVG extraction types for 1:1 visual parity.
-- |
-- | Captures all SVG-related properties:
-- | - Path data (d attribute) as typed Path atoms
-- | - ViewBox for coordinate system
-- | - Fill and stroke with full color support
-- | - Transforms applied to SVG elements

module Hydrogen.Scraper.Types.SVG
  ( -- * Types
    ExtractedSVG
  , ExtractedSVGPath
  , ViewBox
  , StrokeStyle
  
  -- * Constructors  
  , emptySVG
  , emptySVGPath
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Device (px) as Dev
import Hydrogen.Schema.Geometry.Path (Path)
import Hydrogen.Schema.Geometry.Path (emptyPath) as Path

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // viewbox
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SVG viewBox attribute
-- |
-- | Defines the coordinate system for the SVG content.
type ViewBox =
  { minX :: Number
  , minY :: Number
  , width :: Number
  , height :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // stroke style
-- ═══════════════════════════════════════════════════════════════════════════════

-- | SVG stroke properties
type StrokeStyle =
  { color :: Maybe OKLCH
  , width :: Pixel
  , lineCap :: String   -- ^ "butt", "round", "square"
  , lineJoin :: String  -- ^ "miter", "round", "bevel"
  , dashArray :: Array Number
  , dashOffset :: Number
  }

-- ══════════════════════════════════════════════════════���════════════════════════
--                                                          // extracted path
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A single SVG path element
type ExtractedSVGPath =
  { path :: Path
  , fill :: Maybe OKLCH
  , stroke :: StrokeStyle
  , fillRule :: String  -- ^ "nonzero" or "evenodd"
  , opacity :: Number   -- ^ 0.0 to 1.0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // extracted svg
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete SVG extraction for 1:1 parity
type ExtractedSVG =
  { -- Dimensions
    width :: Pixel
  , height :: Pixel
  , viewBox :: Maybe ViewBox
  
  -- Content
  , paths :: Array ExtractedSVGPath
  
  -- Metadata
  , title :: Maybe String
  , description :: Maybe String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty stroke style
emptyStroke :: StrokeStyle
emptyStroke =
  { color: Nothing
  , width: Dev.px 0.0
  , lineCap: "butt"
  , lineJoin: "miter"
  , dashArray: []
  , dashOffset: 0.0
  }

-- | Empty SVG path
emptySVGPath :: ExtractedSVGPath
emptySVGPath =
  { path: Path.emptyPath
  , fill: Nothing
  , stroke: emptyStroke
  , fillRule: "nonzero"
  , opacity: 1.0
  }

-- | Empty SVG
emptySVG :: ExtractedSVG
emptySVG =
  { width: Dev.px 0.0
  , height: Dev.px 0.0
  , viewBox: Nothing
  , paths: []
  , title: Nothing
  , description: Nothing
  }
