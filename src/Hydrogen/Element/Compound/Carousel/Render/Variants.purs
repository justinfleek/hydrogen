-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // element // carousel // render // variants
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Variants — Alternative carousel layouts with different features.
-- |
-- | ## Design Philosophy
-- |
-- | Variants are pre-composed carousel configurations that add specific
-- | features like captions, thumbnails, or different navigation styles.
-- | Each variant is a thin wrapper around the core carousel renderer.
-- |
-- | ## Variants
-- |
-- | - carouselWithCaptions: Shows caption bar below the carousel
-- |
-- | ## Dependencies
-- |
-- | - Render.Types (CarouselConfig)
-- | - Render.Track (renderTrack)
-- | - Render.Navigation (renderNavigation)
-- | - Render.Content (renderCaption)

module Hydrogen.Element.Compound.Carousel.Render.Variants
  ( -- * Carousel Variants
    carouselWithCaptions
  
  -- * Caption Rendering
  , renderCaptionBar
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))
import Data.String.Common (joinWith) as String

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Carousel.Types (CarouselMsg)
import Hydrogen.Element.Compound.Carousel.State (CarouselState)
import Hydrogen.Element.Compound.Carousel.Slide 
  ( SlideCollection
  , slideAt
  )
import Hydrogen.Element.Compound.Carousel.Render.Types (CarouselConfig)
import Hydrogen.Element.Compound.Carousel.Render.Track (renderTrack)
import Hydrogen.Element.Compound.Carousel.Render.Navigation (renderNavigation)
import Hydrogen.Element.Compound.Carousel.Render.Content (renderCaption)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // carousel variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a carousel with captions displayed below each slide
-- |
-- | This variant adds a caption bar that shows the current slide's caption
-- | text. The caption updates as slides change.
-- |
-- | Structure:
-- | ```
-- | .carousel-container.carousel-with-captions
-- |   .carousel-track
-- |   .carousel-caption-bar
-- |   .carousel-navigation
-- | ```
carouselWithCaptions :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
carouselWithCaptions config state slides' =
  E.div_
    [ E.class_ (String.joinWith " " ["carousel-container", "carousel-with-captions", config.cssClass]) ]
    [ renderTrack config state slides'
    , renderCaptionBar config state slides'
    , renderNavigation config.navigation config.loop state slides'
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // caption rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the caption bar showing current slide's caption
-- |
-- | Displays the caption from the currently active slide.
-- | Returns empty element if the slide has no caption or doesn't exist.
renderCaptionBar :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderCaptionBar _config state slides' =
  case slideAt state.current slides' of
    Just slideData' -> 
      E.div_
        [ E.class_ "carousel-caption-bar" ]
        [ renderCaption slideData' ]
    Nothing -> 
      E.empty
