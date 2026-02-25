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

module Hydrogen.Element.Component.Carousel.Render
  ( -- * Render Function
    carousel
  
  -- * Carousel Config
  , CarouselConfig
  , defaultConfig
  
  -- * Messages (re-exported from Types)
  , module CarouselMsgExport
  
  -- * State Accessors
  , getTransitionState
  , getGestureState
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , map
  , (<>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<=)
  , (<)
  , (&&)
  , not
  , negate
  , otherwise
  )

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))




import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Color.RGB as Color
import Data.String.Common (joinWith) as String
import Hydrogen.Element.Component.Carousel.Types 
  ( slideIndex
  , unwrapSlideIndex
  , SlidePosition
      ( PositionActive
      , PositionPrev
      , PositionNext
      , PositionNearby
      , PositionOffscreen
      )
  , TransitionKind
      ( TransitionNone
      , TransitionSlide
      , TransitionSlideVertical
      , TransitionFade
      , TransitionZoom
      , TransitionFlip
      , TransitionFlipVertical
      , TransitionCube
      , TransitionCoverflow
      , TransitionCards
      , TransitionWheel
      , TransitionSpiral
      , TransitionParallax
      , TransitionMorph
      , TransitionDissolve
      , TransitionBlur
      , TransitionWipe
      , TransitionReveal
      )
  , LayoutPath
      ( PathLinear
      , PathLinearVertical
      , PathGrid
      , PathMasonry
      , PathStack
      , PathCircular
      , PathArc
      , PathHelix
      , PathSphere
      , PathCylinder
      , PathMobius
      , PathCustom
      )
  , CarouselMsg
  )
import Hydrogen.Element.Component.Carousel.Types 
  ( CarouselMsg
      ( GoToSlide
      , NextSlide
      , PrevSlide
      , StartAutoplay
      , StopAutoplay
      , ToggleAutoplay
      )
  ) as CarouselMsgExport
import Hydrogen.Element.Component.Carousel.State 
  ( CarouselState
  , TransitionState
  , isTransitioning
  , transitionProgress
  )
import Hydrogen.Element.Component.Carousel.Slide 
  ( SlideCollection
  , SlideData
  , slideAt
  , slideCount
  )
import Hydrogen.Element.Component.Carousel.Navigation 
  ( NavigationConfig
  , defaultNavigation
  )
import Hydrogen.Element.Component.Carousel.Render.Navigation 
  ( renderNavigation
  )
import Hydrogen.Element.Component.Carousel.Render.Layout
  ( computeLayoutTransform
  , sin
  , cos
  , abs
  , absInt
  , toInt
  )
import Hydrogen.Element.Component.Carousel.Render.Content
  ( renderSlideContent
  , renderCaption
  )
import Hydrogen.Element.Component.Carousel.Render.Effects
  ( computeSlidePosition
  , positionToClass
  , computeEffectStyles
  , pow
  )
import Hydrogen.Element.Component.Carousel.Effects 
  ( SlideEffects
  , defaultEffects
  , isEffectEnabled
  , ParallaxDirection
      ( ParallaxHorizontal
      , ParallaxVertical
      , ParallaxBoth
      )
  )
import Hydrogen.Element.Component.Carousel.Transitions 
  ( TransitionConfig
  , defaultTransition
  , easingToCss
  )
import Hydrogen.Element.Component.Carousel.Gestures (GestureState, isDragActive, dragOffset)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // carousel config
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Complete carousel configuration
type CarouselConfig =
  { navigation :: NavigationConfig
  , transition :: TransitionConfig
  , effects :: SlideEffects
  , layoutPath :: LayoutPath      -- spatial arrangement of slides
  , loop :: Boolean
  , autoplayInterval :: Int      -- milliseconds, 0 = no autoplay
  , cssClass :: String           -- additional CSS class
  }

-- | Default carousel configuration
defaultConfig :: CarouselConfig
defaultConfig =
  { navigation: defaultNavigation
  , transition: defaultTransition
  , effects: defaultEffects
  , layoutPath: PathLinear
  , loop: true
  , autoplayInterval: 0
  , cssClass: ""
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // render functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a carousel from state and configuration
-- |
-- | This is the main entry point for carousel rendering.
carousel :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
carousel config state slides' =
  E.div_
    [ E.class_ ("carousel-container" <> additionalClass) ]
    [ renderTrack config state slides'
    , renderNavigation config.navigation config.loop state slides'
    ]
  where
    additionalClass = if config.cssClass == "" then "" else " " <> config.cssClass

-- | Render the slide track with transition and gesture transforms
renderTrack :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderTrack config state slides' =
  let 
    -- Transition type class for CSS styling hooks
    transitionClass = transitionKindToClass config.transition.kind
  in
    E.div_
      ([ E.class_ ("carousel-track " <> transitionClass) ] <> E.styles (trackStyles config state))
      (renderSlides config state slides')

-- | Convert transition kind to CSS class for transition-specific styling
transitionKindToClass :: TransitionKind -> String
transitionKindToClass kind = case kind of
  TransitionNone -> "carousel-transition-none"
  TransitionSlide -> "carousel-transition-slide"
  TransitionSlideVertical -> "carousel-transition-slide-vertical"
  TransitionFade -> "carousel-transition-fade"
  TransitionZoom -> "carousel-transition-zoom"
  TransitionFlip -> "carousel-transition-flip"
  TransitionFlipVertical -> "carousel-transition-flip-vertical"
  TransitionCube -> "carousel-transition-cube"
  TransitionCoverflow -> "carousel-transition-coverflow"
  TransitionCards -> "carousel-transition-cards"
  TransitionWheel -> "carousel-transition-wheel"
  TransitionSpiral -> "carousel-transition-spiral"
  TransitionParallax -> "carousel-transition-parallax"
  TransitionMorph -> "carousel-transition-morph"
  TransitionDissolve -> "carousel-transition-dissolve"
  TransitionBlur -> "carousel-transition-blur"
  TransitionWipe -> "carousel-transition-wipe"
  TransitionReveal -> "carousel-transition-reveal"

-- | Compute track styles based on state and layout path
trackStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
trackStyles config state =
  case config.layoutPath of
    -- Linear layouts use translate on the track
    PathLinear -> linearTrackStyles config state
    PathLinearVertical -> linearVerticalTrackStyles config state
    -- 3D layouts use perspective on the track, slides positioned individually
    PathCircular -> layout3DContainerStyles config
    PathHelix -> layout3DContainerStyles config
    PathSphere -> layout3DContainerStyles config
    PathCylinder -> layout3DContainerStyles config
    PathMobius -> layout3DContainerStyles config
    -- Other layouts
    PathGrid -> gridContainerStyles
    PathMasonry -> masonryContainerStyles
    PathStack -> stackContainerStyles config state
    PathArc -> layout3DContainerStyles config
    PathCustom -> linearTrackStyles config state  -- Fallback to linear

-- | Linear horizontal track styles (traditional carousel)
linearTrackStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
linearTrackStyles config state =
  let 
    currentIdx = unwrapSlideIndex state.current
    baseOffset = toNumber currentIdx * (-100.0)
    gestureOffset = if isDragActive state.gesture.drag
      then (dragOffset state.gesture.drag).x / 10.0
      else 0.0
    transitionOffset = if isTransitioning state.transition
      then 
        let 
          fromIdx = unwrapSlideIndex state.transition.fromIndex
          toIdx = unwrapSlideIndex state.transition.toIndex
          progress = transitionProgress state.transition
          fromOffset = toNumber fromIdx * (-100.0)
          toOffset = toNumber toIdx * (-100.0)
        in fromOffset + (toOffset - fromOffset) * progress
      else baseOffset
    finalOffset = if isTransitioning state.transition 
      then transitionOffset 
      else baseOffset + gestureOffset
    transitionCss = if isTransitioning state.transition
      then "transform " <> show (Device.unwrapPixel (toPixel config.transition.duration)) <> "ms " <> easingToCss config.transition.easing
      else "none"
  in
    [ Tuple "transform" ("translateX(" <> show finalOffset <> "%)")
    , Tuple "transition" transitionCss
    , Tuple "display" "flex"
    ]

-- | Linear vertical track styles
linearVerticalTrackStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
linearVerticalTrackStyles config state =
  let 
    currentIdx = unwrapSlideIndex state.current
    baseOffset = toNumber currentIdx * (-100.0)
    gestureOffset = if isDragActive state.gesture.drag
      then (dragOffset state.gesture.drag).y / 10.0
      else 0.0
    finalOffset = baseOffset + gestureOffset
    transitionCss = if isTransitioning state.transition
      then "transform " <> show (Device.unwrapPixel (toPixel config.transition.duration)) <> "ms " <> easingToCss config.transition.easing
      else "none"
  in
    [ Tuple "transform" ("translateY(" <> show finalOffset <> "%)")
    , Tuple "transition" transitionCss
    , Tuple "display" "flex"
    , Tuple "flex-direction" "column"
    ]

-- | 3D container styles (for circular, helix, sphere, etc.)
layout3DContainerStyles :: CarouselConfig -> Array (Tuple String String)
layout3DContainerStyles _config =
  [ Tuple "perspective" "1000px"
  , Tuple "perspective-origin" "50% 50%"
  , Tuple "transform-style" "preserve-3d"
  , Tuple "position" "relative"
  ]

-- | Grid container styles
gridContainerStyles :: Array (Tuple String String)
gridContainerStyles =
  [ Tuple "display" "grid"
  , Tuple "grid-template-columns" "repeat(auto-fill, minmax(200px, 1fr))"
  , Tuple "gap" "16px"
  ]

-- | Masonry container styles
masonryContainerStyles :: Array (Tuple String String)
masonryContainerStyles =
  [ Tuple "columns" "3"
  , Tuple "column-gap" "16px"
  ]

-- | Stack container styles (cards stacked on top of each other)
stackContainerStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
stackContainerStyles _config _state =
  [ Tuple "position" "relative"
  , Tuple "perspective" "1000px"
  ]

-- Note: computeLayoutTransform, circularTransform, helixTransform, etc.
-- have been moved to Render/Layout.purs and are imported above.

-- | Convert milliseconds to pixel (for duration display)
toPixel :: Temporal.Milliseconds -> Device.Pixel
toPixel ms = Device.px (Temporal.unwrapMilliseconds ms)

-- | Render all slides with position-aware effects
renderSlides :: CarouselConfig -> CarouselState -> SlideCollection -> Array (E.Element CarouselMsg)
renderSlides config state slides' =
  Array.mapWithIndex (\i _ -> renderSlide config state i slides') (Array.range 0 (slideCount slides' - 1))

-- | Render a single slide with effects based on position
renderSlide :: CarouselConfig -> CarouselState -> Int -> SlideCollection -> E.Element CarouselMsg
renderSlide config state index slides' =
  case slideAt (slideIndex index) slides' of
    Just slideData' ->
      let 
        position = computeSlidePosition state index
        currentIdx = unwrapSlideIndex state.current
        total = slideCount slides'
        -- Visual effects based on position (opacity, scale, blur, etc.)
        effectStyles = computeEffectStyles config.effects position
        -- 3D layout transform based on layout path (circular, helix, sphere, etc.)
        layoutStyles = computeLayoutTransform config.layoutPath index currentIdx total
        -- Combine all styles
        allStyles = effectStyles <> layoutStyles
        positionClass = positionToClass position
        baseAttrs = 
          [ E.class_ ("carousel-slide " <> positionClass)
          , E.dataAttr "slide-index" (show index)
          , E.ariaHidden (position == PositionOffscreen)
          ]
        -- Base content (may be wrapped in parallax layers)
        baseContent = renderSlideContent slideData'
        -- Apply parallax wrapper if enabled
        parallaxContent = renderParallaxLayers config.effects position baseContent
        -- Reflection element (rendered below slide content)
        reflectionEl = renderReflection config.effects slideData'
      in
        E.div_
          (baseAttrs <> E.styles allStyles)
          [ parallaxContent
          , reflectionEl
          ]
    Nothing ->
      E.empty

-- | Render reflection effect (mirrored content below slide)
renderReflection :: SlideEffects -> SlideData -> E.Element CarouselMsg
renderReflection effects slideData' =
  if isEffectEnabled effects.reflection.enabled
    then 
      let
        heightPercent = show (effects.reflection.height * 100.0) <> "%"
        startOpacity = show effects.reflection.opacity
        gapPx = show (Device.unwrapPixel effects.reflection.gap) <> "px"
        -- Reflection uses CSS transform: scaleY(-1) to flip vertically
        -- and a gradient mask to fade out
        reflectionStyles = 
          [ Tuple "height" heightPercent
          , Tuple "margin-top" gapPx
          , Tuple "transform" "scaleY(-1)"
          , Tuple "opacity" startOpacity
          , Tuple "mask-image" "linear-gradient(to bottom, rgba(0,0,0,1) 0%, rgba(0,0,0,0) 100%)"
          , Tuple "-webkit-mask-image" "linear-gradient(to bottom, rgba(0,0,0,1) 0%, rgba(0,0,0,0) 100%)"
          , Tuple "pointer-events" "none"
          , Tuple "overflow" "hidden"
          ]
      in
        E.div_
          ([ E.class_ "carousel-slide-reflection"
           , E.ariaHidden true
           ] <> E.styles reflectionStyles)
          [ renderSlideContent slideData' ]
    else
      E.empty

-- Note: renderSlideContent is imported from Render/Content.purs

-- | Render parallax layers wrapper
-- | Each layer moves at a different speed based on its depth
renderParallaxLayers :: SlideEffects -> SlidePosition -> E.Element CarouselMsg -> E.Element CarouselMsg
renderParallaxLayers effects position content =
  if isEffectEnabled effects.parallax.enabled
    then
      let 
        numLayers = effects.parallax.layers
        speedRatio = effects.parallax.speedRatio
        direction = effects.parallax.direction
      in
        E.div_
          [ E.class_ "carousel-parallax-container" ]
          (map (renderParallaxLayer speedRatio direction position content) (Array.range 0 (numLayers - 1)))
    else
      content

-- | Render a single parallax layer with depth-based transform
renderParallaxLayer :: Number -> ParallaxDirection -> SlidePosition -> E.Element CarouselMsg -> Int -> E.Element CarouselMsg
renderParallaxLayer speedRatio direction position content layerIndex =
  let
    -- Calculate speed multiplier for this layer (deeper layers move slower)
    layerDepth = toNumber layerIndex
    speedMultiplier = 1.0 - (layerDepth * speedRatio)
    
    -- Calculate offset based on position and layer depth
    positionOffset = case position of
      PositionActive -> 0.0
      PositionPrev -> negate 20.0 * speedMultiplier
      PositionNext -> 20.0 * speedMultiplier
      PositionNearby n -> toNumber n * 10.0 * speedMultiplier
      PositionOffscreen -> 0.0
    
    -- Build transform based on direction
    transformValue = case direction of
      ParallaxHorizontal -> "translateX(" <> show positionOffset <> "px)"
      ParallaxVertical -> "translateY(" <> show positionOffset <> "px)"
      ParallaxBoth -> "translate(" <> show positionOffset <> "px, " <> show (positionOffset * 0.5) <> "px)"
    
    -- Z-index for layering (deeper = lower z-index)
    zIndex = show (10 - layerIndex)
    
    layerStyles = 
      [ Tuple "transform" transformValue
      , Tuple "z-index" zIndex
      , Tuple "transition" "transform 0.3s ease-out"
      ]
  in
    E.div_
      ([ E.class_ ("carousel-parallax-layer carousel-parallax-layer-" <> show layerIndex) 
       ] <> E.styles layerStyles)
      [ if layerIndex == 0 then content else E.empty ]  -- Only first layer has content

-- | Get the current transition state from carousel state
-- | Useful for tracking animation progress
getTransitionState :: CarouselState -> TransitionState
getTransitionState state = state.transition

-- | Get the current gesture state from carousel state
-- | Useful for responding to user input
getGestureState :: CarouselState -> GestureState
getGestureState state = state.gesture

-- Note: Navigation rendering has been moved to Render/Navigation.purs
-- The renderNavigation function is imported and used in the carousel function above.
-- This keeps Render.purs under 500 lines while maintaining full functionality.
