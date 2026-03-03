-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // scraper // types // pseudo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pseudo-element extraction types for 1:1 visual parity.
-- |
-- | Captures CSS pseudo-elements:
-- | - ::before content
-- | - ::after content
-- | - ::first-letter styling
-- | - ::first-line styling
-- | - ::selection styling
-- | - ::placeholder styling

module Hydrogen.Scraper.Types.Pseudo
  ( -- * Types
    PseudoElement(..)
  , ExtractedPseudo
  , PseudoContent(..)
  
  -- * Constructors
  , emptyPseudo
  ) where

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing))
import Hydrogen.Schema.Color.OKLCH (OKLCH)
import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Dimension.Device (px) as Dev

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // pseudo element
-- ═══════════════════════════════════════════════════════════════════════════════

-- | CSS pseudo-element types
data PseudoElement
  = Before
  | After
  | FirstLetter
  | FirstLine
  | Selection
  | Placeholder
  | Marker
  | Backdrop

derive instance eqPseudoElement :: Eq PseudoElement

instance showPseudoElement :: Show PseudoElement where
  show Before = "::before"
  show After = "::after"
  show FirstLetter = "::first-letter"
  show FirstLine = "::first-line"
  show Selection = "::selection"
  show Placeholder = "::placeholder"
  show Marker = "::marker"
  show Backdrop = "::backdrop"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // pseudo content
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Content property value for ::before/::after
data PseudoContent
  = TextContent String
  | UrlContent String      -- ^ url("...")
  | AttrContent String     -- ^ attr(data-foo)
  | CounterContent String  -- ^ counter(name)
  | QuoteContent           -- ^ open-quote, close-quote
  | NoContent              -- ^ content: none or normal

derive instance eqPseudoContent :: Eq PseudoContent

instance showPseudoContent :: Show PseudoContent where
  show (TextContent s) = "\"" <> s <> "\""
  show (UrlContent u) = "url(" <> u <> ")"
  show (AttrContent a) = "attr(" <> a <> ")"
  show (CounterContent c) = "counter(" <> c <> ")"
  show QuoteContent = "quote"
  show NoContent = "none"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // extracted pseudo
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extracted pseudo-element
type ExtractedPseudo =
  { element :: PseudoElement
  , content :: PseudoContent
  
  -- Dimensions (computed)
  , width :: Pixel
  , height :: Pixel
  
  -- Colors
  , color :: Maybe OKLCH
  , backgroundColor :: Maybe OKLCH
  
  -- Display
  , display :: String
  , position :: String
  
  -- Exists and visible
  , exists :: Boolean
  , visible :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty pseudo-element
emptyPseudo :: ExtractedPseudo
emptyPseudo =
  { element: Before
  , content: NoContent
  , width: Dev.px 0.0
  , height: Dev.px 0.0
  , color: Nothing
  , backgroundColor: Nothing
  , display: "none"
  , position: "static"
  , exists: false
  , visible: false
  }
