-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // carousel // slide
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Slide — Content-aware slide configuration and data.
-- |
-- | ## Design Philosophy
-- |
-- | Slides are content-agnostic containers. The ContentKind determines
-- | how the runtime loads and renders each slide's content.
-- |
-- | ## Content Categories
-- |
-- | - Static: Image, text, cards
-- | - Media: Video, audio (with controls)
-- | - Interactive: Canvas, WebGL, games
-- | - Dynamic: Live data feeds, embeds
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (ContentKind, SlideIndex)

module Hydrogen.Element.Compound.Carousel.Slide
  ( -- * Slide Data
    SlideData
  , slideData
  , imageSlide
  , videoSlide
  , textSlide
  , embedSlide
  
  -- * Slide Collection
  , SlideCollection
  , slides
  , slideAt
  , slideCount
  
  -- * Content Source
  , ContentSource
      ( SourceUrl
      , SourceInline
      , SourceData
      )
  , sourceUrl
  , sourceData
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (<)
  , (>=)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Element.Compound.Carousel.Types 
  ( ContentKind
      ( ContentImage
      , ContentVideo
      , ContentAudio
      , ContentEmbed
      , ContentText
      , ContentCard
      , ContentHTML
      , ContentCanvas
      , ContentWebGL
      , ContentGame
      , ContentLiveData
      , ContentInteractive
      )
  , SlideIndex
  , unwrapSlideIndex
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // content source
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Source of slide content
-- |
-- | Content can come from a URL or be inline data.
data ContentSource
  = SourceUrl String         -- ^ Remote URL (image src, video src, embed)
  | SourceInline String      -- ^ Inline content (text, HTML, SVG)
  | SourceData String        -- ^ Base64 or data URI

derive instance eqContentSource :: Eq ContentSource

instance showContentSource :: Show ContentSource where
  show (SourceUrl url) = "url(" <> url <> ")"
  show (SourceInline _) = "inline"
  show (SourceData _) = "data"

-- | Create URL source
sourceUrl :: String -> ContentSource
sourceUrl = SourceUrl

-- | Create inline data source
sourceData :: String -> ContentSource
sourceData = SourceData

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // slide data
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Data for a single slide
-- |
-- | Content-agnostic slide configuration with metadata.
type SlideData =
  { kind :: ContentKind
  , source :: ContentSource
  , alt :: String              -- ^ Accessibility text / description
  , title :: Maybe String      -- ^ Optional slide title
  , caption :: Maybe String    -- ^ Optional caption
  }

-- | Create slide data
slideData :: ContentKind -> ContentSource -> String -> SlideData
slideData kind source alt =
  { kind
  , source
  , alt
  , title: Nothing
  , caption: Nothing
  }

-- | Create image slide
imageSlide :: String -> String -> SlideData
imageSlide url alt = slideData ContentImage (SourceUrl url) alt

-- | Create video slide
videoSlide :: String -> String -> SlideData
videoSlide url alt = slideData ContentVideo (SourceUrl url) alt

-- | Create text slide
textSlide :: String -> SlideData
textSlide content = slideData ContentText (SourceInline content) content

-- | Create embed slide (YouTube, Vimeo, etc.)
embedSlide :: String -> String -> SlideData
embedSlide url alt = slideData ContentEmbed (SourceUrl url) alt

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // slide collection
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Collection of slides
-- |
-- | Wraps Array for type safety and convenience.
newtype SlideCollection = SlideCollection (Array SlideData)

derive instance eqSlideCollection :: Eq SlideCollection

instance showSlideCollection :: Show SlideCollection where
  show (SlideCollection arr) = "Slides[" <> show (Array.length arr) <> "]"

-- | Create slide collection from array
slides :: Array SlideData -> SlideCollection
slides = SlideCollection

-- | Get slide at index
slideAt :: SlideIndex -> SlideCollection -> Maybe SlideData
slideAt idx (SlideCollection arr) = 
  let i = unwrapSlideIndex idx
  in if i >= 0 then Array.index arr i else Nothing

-- | Get number of slides
slideCount :: SlideCollection -> Int
slideCount (SlideCollection arr) = Array.length arr
