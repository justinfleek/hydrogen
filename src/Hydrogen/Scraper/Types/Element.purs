-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // scraper // types // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Complete element type composing all extraction submodules.
-- |
-- | This is the unified element type for 1:1 visual parity extraction.
-- | Every visual property is captured as bounded Schema atoms.

module Hydrogen.Scraper.Types.Element
  ( -- * Types
    FullExtractedElement(..)
  , ElementContent(..)
  
  -- * Accessors
  , unwrapFullElement
  
  -- * Constructors
  , emptyFullElement
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Device (px) as Dev
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow, noShadow)
import Hydrogen.Schema.Elevation.ZIndex (ZIndex)
import Hydrogen.Schema.Elevation.ZIndex as ZIndex
import Hydrogen.Schema.Geometry.Radius (Corners, cornersAll, none) as Radius
import Hydrogen.Schema.Typography.FontFamily (FontFamily, fontFamily)
import Hydrogen.Schema.Typography.FontSize (FontSize, browserDefault)
import Hydrogen.Schema.Typography.FontWeight (FontWeight)
import Hydrogen.Schema.Typography.FontWeight (normal) as FW
import Hydrogen.Schema.Typography.LineHeight (LineHeight)
import Hydrogen.Schema.Typography.LineHeight (normal) as LH
import Hydrogen.Schema.Typography.LetterSpacing (LetterSpacing)
import Hydrogen.Schema.Typography.LetterSpacing (normal) as LS

import Hydrogen.Scraper.Types.Identity (ElementIdentity, emptyIdentity)
import Hydrogen.Scraper.Types.Image (ExtractedImage)
import Hydrogen.Scraper.Types.SVG (ExtractedSVG)
import Hydrogen.Scraper.Types.Transform (ExtractedTransform, identityTransform)
import Hydrogen.Scraper.Types.State (InteractiveStyles, emptyInteractiveStyles)
import Hydrogen.Scraper.Types.Gradient (ExtractedBackground, emptyBackground)
import Hydrogen.Scraper.Types.Animation (ExtractedTransition, ExtractedAnimation)
import Hydrogen.Scraper.Types.Pseudo (ExtractedPseudo)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // element content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | The semantic content of an element
data ElementContent
  = TextContent String
  | ImageContent ExtractedImage
  | SVGContent ExtractedSVG
  | VideoContent { src :: String, poster :: Maybe String }
  | IframeContent { src :: String }
  | InputContent { inputType :: String, value :: String, placeholder :: String }
  | EmptyContent

derive instance eqElementContent :: Eq ElementContent

instance showElementContent :: Show ElementContent where
  show (TextContent t) = "Text(" <> show t <> ")"
  show (ImageContent _) = "Image"
  show (SVGContent _) = "SVG"
  show (VideoContent _) = "Video"
  show (IframeContent _) = "Iframe"
  show (InputContent _) = "Input"
  show EmptyContent = "Empty"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // full extracted element
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete element extraction for 1:1 visual parity
-- |
-- | This is THE type. Every visual property, every state, every atom.
newtype FullExtractedElement = FullExtractedElement
  { -- Identity (UUID5, hashes, accessibility)
    identity :: ElementIdentity
  
  -- DOM info
  , tagName :: String
  , className :: String
  
  -- Geometry
  , x :: Pixel
  , y :: Pixel
  , width :: Pixel
  , height :: Pixel
  
  -- Content
  , content :: ElementContent
  
  -- Colors
  , backgroundColor :: Maybe OKLCH
  , color :: Maybe OKLCH
  , borderColor :: Maybe OKLCH
  
  -- Background (solid, gradient, image layers)
  , background :: ExtractedBackground
  
  -- Typography
  , fontFamily :: FontFamily
  , fontSize :: FontSize
  , fontWeight :: FontWeight
  , lineHeight :: LineHeight
  , letterSpacing :: LetterSpacing
  
  -- Spacing
  , marginTop :: Pixel
  , marginRight :: Pixel
  , marginBottom :: Pixel
  , marginLeft :: Pixel
  , paddingTop :: Pixel
  , paddingRight :: Pixel
  , paddingBottom :: Pixel
  , paddingLeft :: Pixel
  
  -- Borders
  , borderTopWidth :: Pixel
  , borderRightWidth :: Pixel
  , borderBottomWidth :: Pixel
  , borderLeftWidth :: Pixel
  , borderRadius :: Radius.Corners
  
  -- Elevation
  , shadow :: LayeredShadow
  , zIndex :: ZIndex
  
  -- Transform
  , transform :: ExtractedTransform
  
  -- Opacity & visibility
  , opacity :: Number
  , visibility :: String
  , display :: String
  , overflow :: String
  
  -- Interactive states
  , interactiveStyles :: InteractiveStyles
  
  -- Animations
  , transitions :: Array ExtractedTransition
  , animations :: Array ExtractedAnimation
  
  -- Pseudo-elements
  , pseudoBefore :: Maybe ExtractedPseudo
  , pseudoAfter :: Maybe ExtractedPseudo
  
  -- Tree structure
  , children :: Array FullExtractedElement
  }

derive instance eqFullExtractedElement :: Eq FullExtractedElement

instance showFullExtractedElement :: Show FullExtractedElement where
  show (FullExtractedElement el) = 
    "FullExtractedElement(" <> el.tagName <> "." <> el.className <> ")"

-- | Unwrap element
unwrapFullElement :: FullExtractedElement 
  -> { identity :: ElementIdentity
     , tagName :: String
     , children :: Array FullExtractedElement
     }
unwrapFullElement (FullExtractedElement el) = 
  { identity: el.identity
  , tagName: el.tagName
  , children: el.children
  }

-- ═════════════════════════════════════════════════════════════════════════��═════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty element with all default values
emptyFullElement :: FullExtractedElement
emptyFullElement = FullExtractedElement
  { identity: emptyIdentity
  , tagName: ""
  , className: ""
  , x: Dev.px 0.0
  , y: Dev.px 0.0
  , width: Dev.px 0.0
  , height: Dev.px 0.0
  , content: EmptyContent
  , backgroundColor: Nothing
  , color: Nothing
  , borderColor: Nothing
  , background: emptyBackground
  , fontFamily: fontFamily "sans-serif"
  , fontSize: browserDefault
  , fontWeight: FW.normal
  , lineHeight: LH.normal
  , letterSpacing: LS.normal
  , marginTop: Dev.px 0.0
  , marginRight: Dev.px 0.0
  , marginBottom: Dev.px 0.0
  , marginLeft: Dev.px 0.0
  , paddingTop: Dev.px 0.0
  , paddingRight: Dev.px 0.0
  , paddingBottom: Dev.px 0.0
  , paddingLeft: Dev.px 0.0
  , borderTopWidth: Dev.px 0.0
  , borderRightWidth: Dev.px 0.0
  , borderBottomWidth: Dev.px 0.0
  , borderLeftWidth: Dev.px 0.0
  , borderRadius: Radius.cornersAll Radius.none
  , shadow: noShadow
  , zIndex: ZIndex.auto
  , transform: identityTransform
  , opacity: 1.0
  , visibility: "visible"
  , display: "block"
  , overflow: "visible"
  , interactiveStyles: emptyInteractiveStyles
  , transitions: []
  , animations: []
  , pseudoBefore: Nothing
  , pseudoAfter: Nothing
  , children: []
  }
