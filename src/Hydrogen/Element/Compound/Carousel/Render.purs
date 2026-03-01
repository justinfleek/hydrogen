-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // carousel // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Render — Pure render function for carousel state.
-- |
-- | ## Design Philosophy
-- |
-- | The render function is pure: State -> Element.
-- | It composes all the carousel sub-modules to produce the final UI.
-- | No side effects, no DOM manipulation — just Element construction.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Types: CarouselConfig, defaultConfig
-- | - Track: Track rendering and slide positioning
-- | - Navigation: Arrow, dot, progress, thumbnail controls
-- | - Visibility: Index validation and visibility calculations
-- | - Position: Mathematical position calculations
-- | - ColorEffects: Color tinting based on position
-- | - Variants: Alternative carousel layouts
-- | - Layout: 3D spatial transforms
-- | - Content: Slide content rendering
-- | - Effects: Visual effects computation
-- |
-- | ## Render Structure
-- |
-- | ```
-- | .carousel-container
-- |   .carousel-track
-- |     .carousel-slide[n]
-- |   .carousel-nav-arrows
-- |   .carousel-nav-dots
-- |   .carousel-nav-progress
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Carousel.State (CarouselState)
-- | - Carousel.Slide (SlideCollection, SlideData)
-- | - Carousel.Navigation (NavigationConfig)
-- | - Carousel.Effects (SlideEffects)
-- | - Hydrogen.Render.Element (Element constructors)

module Hydrogen.Element.Compound.Carousel.Render
  ( -- * Re-exports from Types
    module Types
  
  -- * Re-exports from Track
  , module Track
  
  -- * Re-exports from Navigation
  , module Navigation
  
  -- * Re-exports from Visibility
  , module Visibility
  
  -- * Re-exports from Position
  , module Position
  
  -- * Re-exports from ColorEffects
  , module ColorEffects
  
  -- * Re-exports from Variants
  , module Variants
  
  -- * Re-exports from Layout
  , module Layout
  
  -- * Re-exports from Content
  , module Content
  
  -- * Re-exports from Effects
  , module Effects
  
  -- * Main Carousel Render
  , carousel
  
  -- * Messages (re-exported from Carousel.Types)
  , module CarouselMsgExport
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude ((<>), (==))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Carousel.Types 
  ( CarouselMsg
      ( GoToSlide
      , NextSlide
      , PrevSlide
      , StartAutoplay
      , StopAutoplay
      , ToggleAutoplay
      )
  ) as CarouselMsgExport
import Hydrogen.Element.Compound.Carousel.State (CarouselState)
import Hydrogen.Element.Compound.Carousel.Slide (SlideCollection)

-- Submodule imports for re-export
import Hydrogen.Element.Compound.Carousel.Render.Types 
  ( CarouselConfig
  , defaultConfig
  ) as Types

import Hydrogen.Element.Compound.Carousel.Render.Track 
  ( renderTrack
  , renderSlides
  , renderSlide
  , trackStyles
  , linearTrackStyles
  , linearVerticalTrackStyles
  , layout3DContainerStyles
  , gridContainerStyles
  , masonryContainerStyles
  , stackContainerStyles
  , transitionKindToClass
  , toPixel
  , renderParallaxLayers
  , renderParallaxLayer
  , renderReflection
  ) as Track

import Hydrogen.Element.Compound.Carousel.Render.Navigation 
  ( renderNavigation
  , renderArrows
  , renderDots
  , renderProgress
  , renderThumbnails
  , arrowPositionToClass
  , dotsPositionToClass
  , thumbnailPositionToClass
  , renderThumbnail
  , renderThumbnailContent
  , contentKindToIcon
  , contentKindToLabel
  , makeSlideIndex
  ) as Navigation

import Hydrogen.Element.Compound.Carousel.Render.Visibility 
  ( isValidSlideIndex
  , clampSlideIndex
  , isSlideVisible
  , visibleSlideIndices
  , slideDistance
  , visibilityThreshold
  , getTransitionState
  , getGestureState
  ) as Visibility

import Hydrogen.Element.Compound.Carousel.Render.Position 
  ( wavePosition
  , circularPosition
  , easeOutPosition
  , positionDistance
  , defaultCase
  ) as Position

import Hydrogen.Element.Compound.Carousel.Render.ColorEffects 
  ( slidePositionTint
  ) as ColorEffects

import Hydrogen.Element.Compound.Carousel.Render.Variants 
  ( carouselWithCaptions
  , renderCaptionBar
  ) as Variants

import Hydrogen.Element.Compound.Carousel.Render.Layout 
  ( computeLayoutTransform
  , circularTransform
  , helixTransform
  , sphereTransform
  , cylinderTransform
  , mobiusTransform
  , arcTransform
  , stackTransform
  , sin
  , cos
  , asin
  , acos
  , abs
  , absInt
  , toInt
  ) as Layout

import Hydrogen.Element.Compound.Carousel.Render.Content 
  ( renderSlideContent
  , renderCaption
  , renderImageContent
  , renderVideoContent
  , renderAudioContent
  , renderEmbedContent
  , renderTextContent
  , renderCardContent
  , renderHTMLContent
  , renderCanvasContent
  , renderWebGLContent
  , renderGameContent
  , renderLiveDataContent
  , renderInteractiveContent
  , getSourceText
  , guessVideoMimeType
  , guessAudioMimeType
  , isVideoEmbedUrl
  , debugSlideInfo
  , showContentKind
  ) as Content

import Hydrogen.Element.Compound.Carousel.Render.Effects 
  ( computeSlidePosition
  , computeSlidePositionFromIndex
  , positionToClass
  , positionOffset
  , computeEffectStyles
  , computeTransformComponents
  , computeFilterComponents
  , pow
  , interpolateEffect
  ) as Effects

-- Internal imports for carousel function
import Hydrogen.Element.Compound.Carousel.Render.Types (CarouselConfig)
import Hydrogen.Element.Compound.Carousel.Render.Track (renderTrack)
import Hydrogen.Element.Compound.Carousel.Render.Navigation (renderNavigation)
import Hydrogen.Element.Compound.Carousel.Types (CarouselMsg)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // render functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a carousel from state and configuration
-- |
-- | This is the main entry point for carousel rendering.
-- | Composes the track (containing all slides) with navigation controls.
-- |
-- | Structure:
-- | ```
-- | .carousel-container
-- |   .carousel-track
-- |     .carousel-slide[0]
-- |     .carousel-slide[1]
-- |     ...
-- |   .carousel-navigation
-- |     .carousel-arrows
-- |     .carousel-dots
-- |     .carousel-progress
-- |     .carousel-thumbnails
-- | ```
carousel :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
carousel config state slides' =
  E.div_
    [ E.class_ ("carousel-container" <> additionalClass) ]
    [ renderTrack config state slides'
    , renderNavigation config.navigation config.loop state slides'
    ]
  where
    additionalClass = if config.cssClass == "" then "" else " " <> config.cssClass
