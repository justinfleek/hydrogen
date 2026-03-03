-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // scraper // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for the Brand Parity scraper.
-- |
-- | This module defines the typed representations of visual elements extracted
-- | from web pages. Every value is a bounded Schema atom — no strings, no CSS,
-- | no escape hatches.
-- |
-- | ## Architecture
-- |
-- | The scraper extracts computed styles from the DOM via Playwright's evaluate,
-- | then converts raw CSS values to Schema atoms:
-- |
-- | ```
-- | DOM + CSS → RawElementStyle (JSON) → ExtractedElement (Schema atoms)
-- | ```
-- |
-- | ## Bounded Types
-- |
-- | All values are bounded:
-- | - Colors: OKLCH (L: 0-1, C: 0-0.4, H: 0-359)
-- | - Dimensions: Pixel (non-negative for most properties)
-- | - Font weights: 1-1000
-- | - Z-index: Integer (no arbitrary CSS like "auto" - converted to 0)
-- |
-- | This ensures extracted data is immediately usable for AI training without
-- | normalization or validation at consumption time.

module Hydrogen.Scraper.Types
  ( -- * Raw extraction types (from JS)
    RawElementStyle
  , RawBoundingBox
  
  -- * Extracted atom types
  , ExtractedColor
  , ExtractedTypography
  , ExtractedSpacing
  , ExtractedElevation
  , ExtractedBorder
  
  -- * Compound types
  , ExtractedElementData
  , ExtractedElement(..)
  , ElementTree
  , VisualLayer
  , ScrapedPage
  
  -- * Accessors
  , unwrapElement
  , elementData
  , elementChildren
  
  -- * Constructors
  , emptyExtractedElementData
  , emptyExtractedElement
  , emptyScrapedPage
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Device (px) as Dev
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow, noShadow)
import Hydrogen.Schema.Elevation.ZIndex (ZIndex)
import Hydrogen.Schema.Elevation.ZIndex as ZIndex
import Hydrogen.Schema.Geometry.Radius (Corners, cornersAll, none) as Radius
import Hydrogen.Schema.Typography.FontFamily (FontFamily)
import Hydrogen.Schema.Typography.FontFamily (fontFamily) as FF
import Hydrogen.Schema.Typography.FontSize (FontSize)
import Hydrogen.Schema.Typography.FontSize (browserDefault) as FS
import Hydrogen.Schema.Typography.FontWeight (FontWeight)
import Hydrogen.Schema.Typography.FontWeight (normal) as FW
import Hydrogen.Schema.Typography.LineHeight (LineHeight)
import Hydrogen.Schema.Typography.LineHeight (normal) as LH
import Hydrogen.Schema.Typography.LetterSpacing (LetterSpacing)
import Hydrogen.Schema.Typography.LetterSpacing (normal) as LS

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // raw js types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Raw bounding box from getBoundingClientRect
-- |
-- | Coordinates are in CSS pixels relative to the viewport.
type RawBoundingBox =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  , left :: Number
  }

-- | Raw computed style extracted via getComputedStyle
-- |
-- | This is the intermediate representation before conversion to Schema atoms.
-- | All values are strings exactly as CSS returns them.
type RawElementStyle =
  { -- Identification
    tagName :: String
  , id :: String
  , className :: String
  
  -- Bounding box
  , boundingBox :: RawBoundingBox
  
  -- Colors (CSS color strings)
  , backgroundColor :: String
  , color :: String
  , borderColor :: String
  
  -- Typography (CSS values)
  , fontFamily :: String
  , fontSize :: String
  , fontWeight :: String
  , lineHeight :: String
  , letterSpacing :: String
  
  -- Spacing (CSS values)
  , marginTop :: String
  , marginRight :: String
  , marginBottom :: String
  , marginLeft :: String
  , paddingTop :: String
  , paddingRight :: String
  , paddingBottom :: String
  , paddingLeft :: String
  
  -- Borders (CSS values)
  , borderTopWidth :: String
  , borderRightWidth :: String
  , borderBottomWidth :: String
  , borderLeftWidth :: String
  , borderTopLeftRadius :: String
  , borderTopRightRadius :: String
  , borderBottomRightRadius :: String
  , borderBottomLeftRadius :: String
  
  -- Elevation
  , boxShadow :: String
  , zIndex :: String
  
  -- Children element IDs for tree reconstruction
  , childIndices :: Array Int
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // extracted color
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted color values converted to OKLCH
-- |
-- | All colors are normalized to OKLCH for perceptual uniformity.
-- | Transparent colors are represented as Nothing.
type ExtractedColor =
  { background :: Maybe OKLCH
  , foreground :: Maybe OKLCH
  , border :: Maybe OKLCH
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // extracted typography
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted typography values
-- |
-- | Font family is kept as a string because it references external resources.
-- | All other values are bounded Schema atoms.
type ExtractedTypography =
  { family :: FontFamily
  , size :: FontSize
  , weight :: FontWeight
  , lineHeight :: LineHeight
  , letterSpacing :: LetterSpacing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // extracted spacing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted spacing (margin and padding)
-- |
-- | All values in CSS pixels as Pixel atoms.
type ExtractedSpacing =
  { marginTop :: Pixel
  , marginRight :: Pixel
  , marginBottom :: Pixel
  , marginLeft :: Pixel
  , paddingTop :: Pixel
  , paddingRight :: Pixel
  , paddingBottom :: Pixel
  , paddingLeft :: Pixel
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // extracted elevation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted elevation (shadow and z-index)
type ExtractedElevation =
  { shadow :: LayeredShadow
  , zIndex :: ZIndex
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // extracted border
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted border values
-- |
-- | Border widths in pixels, corner radii as Radius.Corners.
type ExtractedBorder =
  { topWidth :: Pixel
  , rightWidth :: Pixel
  , bottomWidth :: Pixel
  , leftWidth :: Pixel
  , corners :: Radius.Corners
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // extracted element
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Record type for extracted element data
-- |
-- | This is the data portion without the recursive children.
-- | Use ExtractedElement for the full recursive type.
type ExtractedElementData =
  { -- Identification
    tagName :: String
  , elementId :: String
  , className :: String
  
  -- Position and size (in CSS pixels)
  , x :: Pixel
  , y :: Pixel
  , width :: Pixel
  , height :: Pixel
  
  -- Visual properties as Schema atoms
  , colors :: ExtractedColor
  , typography :: ExtractedTypography
  , spacing :: ExtractedSpacing
  , elevation :: ExtractedElevation
  , border :: ExtractedBorder
  }

-- | A fully extracted element with all Schema atoms
-- |
-- | This is the core output type: a visual element decomposed into typed atoms
-- | that can be reconstructed faithfully.
-- |
-- | Uses newtype to allow recursive children field.
newtype ExtractedElement = ExtractedElement
  { element :: ExtractedElementData
  , children :: Array ExtractedElement
  }

derive instance eqExtractedElement :: Eq ExtractedElement

instance showExtractedElement :: Show ExtractedElement where
  show (ExtractedElement el) = "ExtractedElement(" <> el.element.tagName <> ")"

-- | Unwrap an ExtractedElement to access its data
unwrapElement :: ExtractedElement -> { element :: ExtractedElementData, children :: Array ExtractedElement }
unwrapElement (ExtractedElement e) = e

-- | Get the element data from an ExtractedElement
elementData :: ExtractedElement -> ExtractedElementData
elementData (ExtractedElement e) = e.element

-- | Get children from an ExtractedElement
elementChildren :: ExtractedElement -> Array ExtractedElement
elementChildren (ExtractedElement e) = e.children

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // element tree
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A tree of extracted elements
-- |
-- | The root is typically the body element. This is an alias for ExtractedElement
-- | to make the intent clear at the API level.
type ElementTree = ExtractedElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // visual layer
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A visual layer grouped by z-index
-- |
-- | Elements at the same z-index form a layer for comparison rendering.
type VisualLayer =
  { zIndex :: ZIndex
  , elements :: Array ExtractedElement
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // scraped page
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete scraped page with all extracted data
-- |
-- | Includes metadata, the element tree, and layered view for comparison.
type ScrapedPage =
  { url :: String
  , title :: String
  , viewportWidth :: Pixel
  , viewportHeight :: Pixel
  , tree :: ElementTree
  , layers :: Array VisualLayer
  , screenshotPath :: Maybe String
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty extracted element data (default values)
-- |
-- | Used as a starting point for building element data incrementally.
emptyExtractedElementData :: ExtractedElementData
emptyExtractedElementData =
  { tagName: ""
  , elementId: ""
  , className: ""
  , x: zero
  , y: zero
  , width: zero
  , height: zero
  , colors:
      { background: Nothing
      , foreground: Nothing
      , border: Nothing
      }
  , typography: defaultTypography
  , spacing: zeroSpacing
  , elevation:
      { shadow: noShadow
      , zIndex: ZIndex.auto
      }
  , border: zeroBorder
  }
  where
    zero = zeroPixel
    
    defaultTypography =
      { family: defaultFontFamily
      , size: defaultFontSize
      , weight: defaultFontWeight
      , lineHeight: defaultLineHeight
      , letterSpacing: defaultLetterSpacing
      }
    
    zeroSpacing =
      { marginTop: zero
      , marginRight: zero
      , marginBottom: zero
      , marginLeft: zero
      , paddingTop: zero
      , paddingRight: zero
      , paddingBottom: zero
      , paddingLeft: zero
      }
    
    zeroBorder =
      { topWidth: zero
      , rightWidth: zero
      , bottomWidth: zero
      , leftWidth: zero
      , corners: Radius.cornersAll Radius.none
      }

-- | Empty extracted element (default values)
-- |
-- | Used as a starting point for building elements incrementally.
emptyExtractedElement :: ExtractedElement
emptyExtractedElement = ExtractedElement
  { element: emptyExtractedElementData
  , children: []
  }

-- | Empty scraped page
emptyScrapedPage :: ScrapedPage
emptyScrapedPage =
  { url: ""
  , title: ""
  , viewportWidth: zeroPixel
  , viewportHeight: zeroPixel
  , tree: emptyExtractedElement
  , layers: []
  , screenshotPath: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

zeroPixel :: Pixel
zeroPixel = Dev.px 0.0

defaultFontFamily :: FontFamily
defaultFontFamily = FF.fontFamily "sans-serif"

defaultFontSize :: FontSize
defaultFontSize = FS.browserDefault

defaultFontWeight :: FontWeight
defaultFontWeight = FW.normal

defaultLineHeight :: LineHeight
defaultLineHeight = LH.normal

defaultLetterSpacing :: LetterSpacing
defaultLetterSpacing = LS.normal
