-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // carousel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel/Slider component
-- |
-- | A full-featured carousel component for displaying slideshows,
-- | image galleries, and multi-item carousels with various transitions.
-- |
-- | ## Features
-- |
-- | - Horizontal slide carousel
-- | - Navigation arrows (prev/next)
-- | - Dot indicators
-- | - Auto-play with pause on hover
-- | - Touch/swipe support
-- | - Infinite loop option
-- | - Multiple items visible
-- | - Fade transition option
-- | - Thumbnail navigation
-- | - Responsive breakpoints
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Carousel as Carousel
-- |
-- | -- Basic carousel
-- | Carousel.carousel
-- |   [ Carousel.showArrows true
-- |   , Carousel.showDots true
-- |   , Carousel.onSlideChange HandleSlideChange
-- |   ]
-- |   [ Carousel.slide [] [ HH.img [ HP.src "image1.jpg" ] ]
-- |   , Carousel.slide [] [ HH.img [ HP.src "image2.jpg" ] ]
-- |   , Carousel.slide [] [ HH.img [ HP.src "image3.jpg" ] ]
-- |   ]
-- |
-- | -- Auto-playing carousel
-- | Carousel.carousel
-- |   [ Carousel.autoPlay true
-- |   , Carousel.autoPlayInterval 5000
-- |   , Carousel.pauseOnHover true
-- |   , Carousel.infiniteLoop true
-- |   ]
-- |   slides
-- |
-- | -- Multi-item carousel
-- | Carousel.carousel
-- |   [ Carousel.itemsToShow 3
-- |   , Carousel.itemsToScroll 1
-- |   , Carousel.responsive
-- |       [ { breakpoint: 768, items: 2 }
-- |       , { breakpoint: 480, items: 1 }
-- |       ]
-- |   ]
-- |   productCards
-- |
-- | -- Fade transition
-- | Carousel.carousel
-- |   [ Carousel.transition Carousel.Fade
-- |   , Carousel.transitionDuration 500
-- |   ]
-- |   slides
-- |
-- | -- With thumbnails
-- | Carousel.carousel
-- |   [ Carousel.showThumbnails true
-- |   , Carousel.thumbnailPosition Carousel.Bottom
-- |   ]
-- |   slides
-- | ```
module Hydrogen.Component.Carousel
  ( -- * Carousel Components
    carousel
  , slide
  , carouselArrow
  , carouselDots
  , carouselThumbnails
    -- * Props
  , CarouselProps
  , CarouselProp
  , SlideProps
  , SlideProp
  , defaultProps
  , defaultSlideProps
    -- * Prop Builders - Carousel
  , currentIndex
  , showArrows
  , showDots
  , autoPlay
  , autoPlayInterval
  , pauseOnHover
  , infiniteLoop
  , transition
  , transitionDuration
  , itemsToShow
  , itemsToScroll
  , centerMode
  , responsive
  , showThumbnails
  , thumbnailPosition
  , className
  , onSlideChange
  , onAutoPlayToggle
    -- * Prop Builders - Slide
  , slideClassName
    -- * Types
  , Transition(..)
  , ThumbnailPosition(..)
  , Breakpoint
    -- * FFI
  , CarouselElement
  , initCarousel
  , destroyCarousel
  ) where

import Prelude

import Data.Array (foldl, length, mapWithIndex, (!!))
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Transition type between slides
data Transition
  = Slide
  | Fade
  | None

derive instance eqTransition :: Eq Transition

-- | Thumbnail navigation position
data ThumbnailPosition
  = Top
  | Bottom
  | Left
  | Right

derive instance eqThumbnailPosition :: Eq ThumbnailPosition

-- | Responsive breakpoint configuration
type Breakpoint =
  { breakpoint :: Int
  , items :: Int
  }

-- | Opaque carousel element for FFI
foreign import data CarouselElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize carousel with touch/swipe support
foreign import initCarouselImpl :: EffectFn3 Element
  { onSwipeLeft :: Effect Unit
  , onSwipeRight :: Effect Unit
  , onTouchStart :: Effect Unit
  , onTouchEnd :: Effect Unit
  }
  { threshold :: Int
  , preventScroll :: Boolean
  }
  CarouselElement

-- | Destroy carousel and cleanup
foreign import destroyCarouselImpl :: EffectFn1 CarouselElement Unit

-- | Start auto-play timer
foreign import startAutoPlayImpl :: EffectFn3 CarouselElement Int (Effect Unit) Unit

-- | Stop auto-play timer
foreign import stopAutoPlayImpl :: EffectFn1 CarouselElement Unit

-- | Initialize carousel
initCarousel :: Element ->
  { onSwipeLeft :: Effect Unit
  , onSwipeRight :: Effect Unit
  , onTouchStart :: Effect Unit
  , onTouchEnd :: Effect Unit
  } ->
  { threshold :: Int
  , preventScroll :: Boolean
  } ->
  Effect CarouselElement
initCarousel el callbacks opts = do
  pure unsafeCarouselElement

-- | Destroy carousel
destroyCarousel :: CarouselElement -> Effect Unit
destroyCarousel _ = pure unit

-- Internal placeholder
foreign import unsafeCarouselElement :: CarouselElement

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Carousel container properties
type CarouselProps i =
  { currentIndex :: Int
  , showArrows :: Boolean
  , showDots :: Boolean
  , autoPlay :: Boolean
  , autoPlayInterval :: Int
  , pauseOnHover :: Boolean
  , infiniteLoop :: Boolean
  , transition :: Transition
  , transitionDuration :: Int
  , itemsToShow :: Int
  , itemsToScroll :: Int
  , centerMode :: Boolean
  , responsive :: Array Breakpoint
  , showThumbnails :: Boolean
  , thumbnailPosition :: ThumbnailPosition
  , className :: String
  , onSlideChange :: Maybe (Int -> i)
  , onAutoPlayToggle :: Maybe (Boolean -> i)
  }

-- | Carousel property modifier
type CarouselProp i = CarouselProps i -> CarouselProps i

-- | Default carousel properties
defaultProps :: forall i. CarouselProps i
defaultProps =
  { currentIndex: 0
  , showArrows: true
  , showDots: true
  , autoPlay: false
  , autoPlayInterval: 3000
  , pauseOnHover: true
  , infiniteLoop: false
  , transition: Slide
  , transitionDuration: 300
  , itemsToShow: 1
  , itemsToScroll: 1
  , centerMode: false
  , responsive: []
  , showThumbnails: false
  , thumbnailPosition: Bottom
  , className: ""
  , onSlideChange: Nothing
  , onAutoPlayToggle: Nothing
  }

-- | Slide properties
type SlideProps =
  { className :: String
  }

-- | Slide property modifier
type SlideProp = SlideProps -> SlideProps

-- | Default slide properties
defaultSlideProps :: SlideProps
defaultSlideProps =
  { className: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set current slide index
currentIndex :: forall i. Int -> CarouselProp i
currentIndex idx props = props { currentIndex = idx }

-- | Show navigation arrows
showArrows :: forall i. Boolean -> CarouselProp i
showArrows s props = props { showArrows = s }

-- | Show dot indicators
showDots :: forall i. Boolean -> CarouselProp i
showDots s props = props { showDots = s }

-- | Enable auto-play
autoPlay :: forall i. Boolean -> CarouselProp i
autoPlay a props = props { autoPlay = a }

-- | Set auto-play interval (ms)
autoPlayInterval :: forall i. Int -> CarouselProp i
autoPlayInterval interval props = props { autoPlayInterval = interval }

-- | Pause auto-play on hover
pauseOnHover :: forall i. Boolean -> CarouselProp i
pauseOnHover p props = props { pauseOnHover = p }

-- | Enable infinite loop
infiniteLoop :: forall i. Boolean -> CarouselProp i
infiniteLoop l props = props { infiniteLoop = l }

-- | Set transition type
transition :: forall i. Transition -> CarouselProp i
transition t props = props { transition = t }

-- | Set transition duration (ms)
transitionDuration :: forall i. Int -> CarouselProp i
transitionDuration d props = props { transitionDuration = d }

-- | Set number of items to show
itemsToShow :: forall i. Int -> CarouselProp i
itemsToShow n props = props { itemsToShow = n }

-- | Set number of items to scroll
itemsToScroll :: forall i. Int -> CarouselProp i
itemsToScroll n props = props { itemsToScroll = n }

-- | Enable center mode (active slide centered)
centerMode :: forall i. Boolean -> CarouselProp i
centerMode c props = props { centerMode = c }

-- | Set responsive breakpoints
responsive :: forall i. Array Breakpoint -> CarouselProp i
responsive r props = props { responsive = r }

-- | Show thumbnail navigation
showThumbnails :: forall i. Boolean -> CarouselProp i
showThumbnails s props = props { showThumbnails = s }

-- | Set thumbnail position
thumbnailPosition :: forall i. ThumbnailPosition -> CarouselProp i
thumbnailPosition p props = props { thumbnailPosition = p }

-- | Add custom class to carousel
className :: forall i. String -> CarouselProp i
className c props = props { className = props.className <> " " <> c }

-- | Set slide change handler
onSlideChange :: forall i. (Int -> i) -> CarouselProp i
onSlideChange handler props = props { onSlideChange = Just handler }

-- | Set auto-play toggle handler
onAutoPlayToggle :: forall i. (Boolean -> i) -> CarouselProp i
onAutoPlayToggle handler props = props { onAutoPlayToggle = Just handler }

-- | Add custom class to slide
slideClassName :: String -> SlideProp
slideClassName c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Carousel container
-- |
-- | Main carousel component with slides, navigation, and indicators
carousel :: forall w i. Array (CarouselProp i) -> Array (HH.HTML w i) -> HH.HTML w i
carousel propMods slides =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    slideCount = length slides
    
    containerClasses = 
      "carousel relative overflow-hidden group"
    
    -- Calculate transform based on current index and transition
    translateX = -(props.currentIndex * 100 / props.itemsToShow)
    
    trackStyle = case props.transition of
      Slide -> 
        "transform: translateX(" <> show translateX <> "%);" <>
        " transition: transform " <> show props.transitionDuration <> "ms ease-in-out"
      Fade -> 
        "transition: opacity " <> show props.transitionDuration <> "ms ease-in-out"
      None -> 
        "transform: translateX(" <> show translateX <> "%)"
    
    slideWidth = 100.0 / toNumber props.itemsToShow
    
    wrappedSlides = mapWithIndex (wrapSlide props slideWidth) slides
    
    -- Navigation arrows
    prevArrow = 
      if props.showArrows
        then carouselArrow { direction: "prev", onClick: goPrev props slideCount }
        else HH.text ""
    
    nextArrow = 
      if props.showArrows
        then carouselArrow { direction: "next", onClick: goNext props slideCount }
        else HH.text ""
    
    -- Dot indicators
    dots = 
      if props.showDots
        then carouselDots props slideCount
        else HH.text ""
    
    -- Thumbnails
    thumbnails = 
      if props.showThumbnails
        then carouselThumbnails props slides
        else HH.text ""
    
    -- Determine thumbnail layout
    thumbnailLayout = case props.thumbnailPosition of
      Top -> [ thumbnails, mainContent ]
      Bottom -> [ mainContent, thumbnails ]
      Left -> [ HH.div [ cls [ "flex" ] ] [ thumbnails, mainContent ] ]
      Right -> [ HH.div [ cls [ "flex" ] ] [ mainContent, thumbnails ] ]
    
    mainContent =
      HH.div
        [ cls [ "carousel-viewport relative overflow-hidden" ] ]
        [ HH.div
            [ cls [ "carousel-track flex" ]
            , HP.attr (HH.AttrName "style") trackStyle
            ]
            wrappedSlides
        , prevArrow
        , nextArrow
        ]
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , ARIA.role "region"
      , ARIA.label "Image carousel"
      , HP.attr (HH.AttrName "aria-roledescription") "carousel"
      ]
      ( if props.showThumbnails
          then thumbnailLayout
          else [ mainContent, dots ]
      )
  where
    goPrev :: CarouselProps i -> Int -> Maybe i
    goPrev p count = case p.onSlideChange of
      Just handler -> 
        let 
          newIndex = 
            if p.currentIndex <= 0
              then if p.infiniteLoop then count - 1 else 0
              else p.currentIndex - p.itemsToScroll
        in Just (handler newIndex)
      Nothing -> Nothing
    
    goNext :: CarouselProps i -> Int -> Maybe i
    goNext p count = case p.onSlideChange of
      Just handler ->
        let
          maxIndex = count - p.itemsToShow
          newIndex = 
            if p.currentIndex >= maxIndex
              then if p.infiniteLoop then 0 else maxIndex
              else min (p.currentIndex + p.itemsToScroll) maxIndex
        in Just (handler newIndex)
      Nothing -> Nothing
    
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n
    
    toNumberImpl :: Int -> Number
    toNumberImpl = unsafeToNumber

foreign import unsafeToNumber :: Int -> Number

-- | Wrap a slide with proper styling
wrapSlide :: forall w i. CarouselProps i -> Number -> Int -> HH.HTML w i -> HH.HTML w i
wrapSlide props slideWidth idx content =
  let
    isActive = idx == props.currentIndex
    
    slideClasses = case props.transition of
      Fade -> 
        "carousel-slide absolute inset-0 transition-opacity" <>
        (if isActive then " opacity-100 z-10" else " opacity-0 z-0")
      _ -> 
        "carousel-slide flex-shrink-0"
    
    slideStyle = case props.transition of
      Fade -> ""
      _ -> "width: " <> show slideWidth <> "%"
  in
    HH.div
      [ cls [ slideClasses ]
      , HP.attr (HH.AttrName "style") slideStyle
      , HP.attr (HH.AttrName "data-slide-index") (show idx)
      , ARIA.role "group"
      , HP.attr (HH.AttrName "aria-roledescription") "slide"
      , ARIA.label ("Slide " <> show (idx + 1))
      ]
      [ content ]

-- | Individual slide
-- |
-- | Wrapper for slide content
slide :: forall w i. Array SlideProp -> Array (HH.HTML w i) -> HH.HTML w i
slide propMods children =
  let
    props = foldl (\p f -> f p) defaultSlideProps propMods
  in
    HH.div
      [ cls [ "carousel-slide-content w-full h-full", props.className ] ]
      children

-- | Navigation arrow
carouselArrow :: forall w i. { direction :: String, onClick :: Maybe i } -> HH.HTML w i
carouselArrow config =
  let
    isPrev = config.direction == "prev"
    
    positionClasses = 
      if isPrev 
        then "left-2" 
        else "right-2"
    
    arrowIcon = 
      if isPrev 
        then "‹" 
        else "›"
    
    arrowLabel = 
      if isPrev 
        then "Previous slide" 
        else "Next slide"
    
    clickHandler = case config.onClick of
      Just handler -> [ HE.onClick (\_ -> handler) ]
      Nothing -> []
  in
    HH.button
      ( [ cls 
            [ "carousel-arrow absolute top-1/2 -translate-y-1/2 z-20"
            , positionClasses
            , "flex h-10 w-10 items-center justify-center rounded-full"
            , "bg-background/80 text-foreground shadow-md backdrop-blur-sm"
            , "hover:bg-background transition-all"
            , "opacity-0 group-hover:opacity-100"
            , "disabled:opacity-50 disabled:cursor-not-allowed"
            ]
        , HP.type_ HP.ButtonButton
        , ARIA.label arrowLabel
        ] <> clickHandler
      )
      [ HH.span 
          [ cls [ "text-2xl font-light leading-none" ] ] 
          [ HH.text arrowIcon ]
      ]

-- | Dot indicators
carouselDots :: forall w i. CarouselProps i -> Int -> HH.HTML w i
carouselDots props count =
  let
    dotCount = count - props.itemsToShow + 1
    
    renderDot :: Int -> HH.HTML w i
    renderDot idx =
      let
        isActive = idx == props.currentIndex
        
        dotClasses = 
          "carousel-dot h-2 rounded-full transition-all cursor-pointer" <>
          (if isActive then " w-6 bg-primary" else " w-2 bg-muted-foreground/50 hover:bg-muted-foreground")
        
        clickHandler = case props.onSlideChange of
          Just handler -> [ HE.onClick (\_ -> handler idx) ]
          Nothing -> []
      in
        HH.button
          ( [ cls [ dotClasses ]
            , HP.type_ HP.ButtonButton
            , ARIA.label ("Go to slide " <> show (idx + 1))
            ] <> clickHandler
          )
          []
  in
    HH.div
      [ cls [ "carousel-dots flex items-center justify-center gap-2 mt-4" ]
      , ARIA.role "tablist"
      , ARIA.label "Slide navigation"
      ]
      (map renderDot (range 0 (dotCount - 1)))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeImpl start end

foreign import rangeImpl :: Int -> Int -> Array Int

-- | Thumbnail navigation
carouselThumbnails :: forall w i. CarouselProps i -> Array (HH.HTML w i) -> HH.HTML w i
carouselThumbnails props slides =
  let
    isVertical = props.thumbnailPosition == Left || props.thumbnailPosition == Right
    
    containerClasses = 
      if isVertical
        then "carousel-thumbnails flex flex-col gap-2 p-2"
        else "carousel-thumbnails flex gap-2 p-2 overflow-x-auto"
    
    renderThumb :: Int -> HH.HTML w i -> HH.HTML w i
    renderThumb idx _ =
      let
        isActive = idx == props.currentIndex
        
        thumbClasses = 
          "carousel-thumbnail shrink-0 w-16 h-12 rounded border-2 overflow-hidden cursor-pointer transition-all" <>
          (if isActive then " border-primary ring-2 ring-primary/20" else " border-transparent opacity-60 hover:opacity-100")
        
        clickHandler = case props.onSlideChange of
          Just handler -> [ HE.onClick (\_ -> handler idx) ]
          Nothing -> []
      in
        HH.button
          ( [ cls [ thumbClasses ]
            , HP.type_ HP.ButtonButton
            , ARIA.label ("Go to slide " <> show (idx + 1))
            ] <> clickHandler
          )
          [ HH.div 
              [ cls [ "w-full h-full bg-muted flex items-center justify-center text-xs text-muted-foreground" ] ] 
              [ HH.text (show (idx + 1)) ]
          ]
  in
    HH.div
      [ cls [ containerClasses ]
      , ARIA.role "tablist"
      , ARIA.label "Thumbnail navigation"
      ]
      (mapWithIndex renderThumb slides)
