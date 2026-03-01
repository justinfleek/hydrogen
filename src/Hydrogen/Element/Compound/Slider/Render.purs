-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // slider // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Slider Render — Pure Element rendering for slider components.
-- |
-- | This module contains the main slider rendering functions:
-- | - `slider` — Single-thumb slider for selecting a value
-- | - `rangeSlider` — Dual-thumb slider for selecting a range
-- |
-- | Both components are pure `Element` data structures that can be
-- | rendered to any target: DOM, Halogen, Static HTML, etc.

module Hydrogen.Element.Compound.Slider.Render
  ( -- * Components
    slider
  , rangeSlider
  ) where

import Prelude
  ( show
  , (<>)
  , (+)
  , (-)
  , (/)
  , (*)
  , (==)
  , map
  )

import Data.Array (foldl, range)
import Data.Int (round, toNumber)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry

import Hydrogen.Element.Compound.Slider.Types
  ( Orientation(Horizontal, Vertical)
  , SliderProp
  , SliderProps
  )
import Hydrogen.Element.Compound.Slider.Defaults
  ( defaultProps
  , defaultTrackColor
  , defaultRangeColor
  , defaultThumbColor
  , defaultThumbBorderColor
  , defaultTickColor
  , defaultTooltipBgColor
  , defaultTooltipTextColor
  , defaultTrackHeight
  , defaultThumbSize
  , defaultThumbBorderWidth
  , defaultBorderRadius
  , defaultTransitionDuration
  )
import Hydrogen.Element.Compound.Slider.Internal
  ( toPercent
  , showPercent
  , getColor
  , getPixel
  , getRadius
  , getDuration
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // single slider
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single value slider
-- |
-- | A slider for selecting a single numeric value.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Slider as Slider
-- |
-- | Slider.slider
-- |   [ Slider.value 50.0
-- |   , Slider.trackColor brand.surfaceColor
-- |   , Slider.rangeColor brand.primaryColor
-- |   , Slider.onChange HandleSliderChange
-- |   ]
-- | ```
slider :: forall msg. Array (SliderProp msg) -> E.Element msg
slider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    percent = toPercent props.minVal props.maxVal props.value
    
    -- Resolve colors
    trkColor = getColor props.trackColor defaultTrackColor
    rngColor = getColor props.rangeColor defaultRangeColor
    tmbColor = getColor props.thumbColor defaultThumbColor
    tmbBorderColor = getColor props.thumbBorderColor defaultThumbBorderColor
    
    -- Resolve dimensions
    trkHeight = getPixel props.trackHeight defaultTrackHeight
    tmbSize = getPixel props.thumbSize defaultThumbSize
    tmbBorderW = getPixel props.thumbBorderWidth defaultThumbBorderWidth
    
    -- Resolve geometry
    radius = getRadius props.borderRadius defaultBorderRadius
    
    -- Resolve motion
    duration = getDuration props.transitionDuration defaultTransitionDuration
    
    -- Container styles
    containerStyles = 
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "touch-action" "none"
      , E.style "user-select" "none"
      ] <> (if isVertical
              then [ E.style "flex-direction" "column"
                   , E.style "align-items" "center"
                   , E.style "height" "100%"
                   , E.style "width" (show tmbSize)
                   ]
              else [ E.style "align-items" "center"
                   , E.style "width" "100%"
                   ])
    
    -- Track styles
    trackStyles =
      [ E.style "position" "relative"
      , E.style "background-color" (Color.toLegacyCss trkColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" (show trkHeight)
                   , E.style "height" "100%"
                   ]
              else [ E.style "height" (show trkHeight)
                   , E.style "width" "100%"
                   ])
    
    -- Range (filled portion) styles
    rangeStyles =
      [ E.style "position" "absolute"
      , E.style "background-color" (Color.toLegacyCss rngColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" "100%"
                   , E.style "bottom" "0"
                   , E.style "height" (showPercent percent)
                   ]
              else [ E.style "height" "100%"
                   , E.style "width" (showPercent percent)
                   ])
    
    -- Thumb styles
    thumbStyles =
      [ E.style "position" "absolute"
      , E.style "display" "block"
      , E.style "width" (show tmbSize)
      , E.style "height" (show tmbSize)
      , E.style "border-radius" "50%"
      , E.style "border-style" "solid"
      , E.style "border-width" (show tmbBorderW)
      , E.style "border-color" (Color.toLegacyCss tmbBorderColor)
      , E.style "background-color" (Color.toLegacyCss tmbColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> show duration <> " ease-out")
      , E.style "outline" "none"
      ] <> (if isVertical
              then [ E.style "left" "50%"
                   , E.style "transform" "translate(-50%, 50%)"
                   , E.style "bottom" (showPercent percent)
                   ]
              else [ E.style "top" "50%"
                   , E.style "transform" "translate(-50%, -50%)"
                   , E.style "left" (showPercent percent)
                   ])
    
    -- Disabled styles
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    tabIndexVal = if props.disabled then "-1" else "0"
  in
    E.div_
      (containerStyles <> [ E.dataAttr "orientation" (if isVertical then "vertical" else "horizontal") ])
      [ E.div_
          trackStyles
          [ E.div_ rangeStyles []
          , E.div_
              ( thumbStyles <> disabledStyles <>
                [ E.attr "tabindex" tabIndexVal
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.value)
                , E.attr "aria-valuemin" (show props.minVal)
                , E.attr "aria-valuemax" (show props.maxVal)
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.ariaLabel props.ariaLabel
                ]
              )
              ( if props.showTooltip
                  then [ renderTooltip props props.value ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else E.text ""
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // range slider
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range slider (dual thumbs)
-- |
-- | A slider for selecting a range of values with low and high bounds.
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- |
-- | ## Example
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Slider as Slider
-- |
-- | Slider.rangeSlider
-- |   [ Slider.rangeValue { low: 20.0, high: 80.0 }
-- |   , Slider.trackColor brand.surfaceColor
-- |   , Slider.rangeColor brand.primaryColor
-- |   , Slider.onRangeChange HandleRangeChange
-- |   ]
-- | ```
rangeSlider :: forall msg. Array (SliderProp msg) -> E.Element msg
rangeSlider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    lowPercent = toPercent props.minVal props.maxVal props.rangeVal.low
    highPercent = toPercent props.minVal props.maxVal props.rangeVal.high
    
    -- Resolve colors
    trkColor = getColor props.trackColor defaultTrackColor
    rngColor = getColor props.rangeColor defaultRangeColor
    tmbColor = getColor props.thumbColor defaultThumbColor
    tmbBorderColor = getColor props.thumbBorderColor defaultThumbBorderColor
    
    -- Resolve dimensions
    trkHeight = getPixel props.trackHeight defaultTrackHeight
    tmbSize = getPixel props.thumbSize defaultThumbSize
    tmbBorderW = getPixel props.thumbBorderWidth defaultThumbBorderWidth
    
    -- Resolve geometry
    radius = getRadius props.borderRadius defaultBorderRadius
    
    -- Resolve motion
    duration = getDuration props.transitionDuration defaultTransitionDuration
    
    -- Container styles
    containerStyles = 
      [ E.style "position" "relative"
      , E.style "display" "flex"
      , E.style "touch-action" "none"
      , E.style "user-select" "none"
      ] <> (if isVertical
              then [ E.style "flex-direction" "column"
                   , E.style "align-items" "center"
                   , E.style "height" "100%"
                   , E.style "width" (show tmbSize)
                   ]
              else [ E.style "align-items" "center"
                   , E.style "width" "100%"
                   ])
    
    -- Track styles
    trackStyles =
      [ E.style "position" "relative"
      , E.style "background-color" (Color.toLegacyCss trkColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" (show trkHeight)
                   , E.style "height" "100%"
                   ]
              else [ E.style "height" (show trkHeight)
                   , E.style "width" "100%"
                   ])
    
    -- Range (filled portion) styles
    rangeStyles =
      [ E.style "position" "absolute"
      , E.style "background-color" (Color.toLegacyCss rngColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      ] <> (if isVertical
              then [ E.style "width" "100%"
                   , E.style "bottom" (showPercent lowPercent)
                   , E.style "height" (showPercent (highPercent - lowPercent))
                   ]
              else [ E.style "height" "100%"
                   , E.style "left" (showPercent lowPercent)
                   , E.style "width" (showPercent (highPercent - lowPercent))
                   ])
    
    -- Build thumb styles for a given position
    buildThumbStyles :: Number -> Array (E.Attribute msg)
    buildThumbStyles pct =
      [ E.style "position" "absolute"
      , E.style "display" "block"
      , E.style "width" (show tmbSize)
      , E.style "height" (show tmbSize)
      , E.style "border-radius" "50%"
      , E.style "border-style" "solid"
      , E.style "border-width" (show tmbBorderW)
      , E.style "border-color" (Color.toLegacyCss tmbBorderColor)
      , E.style "background-color" (Color.toLegacyCss tmbColor)
      , E.style "cursor" (if props.disabled then "not-allowed" else "pointer")
      , E.style "transition" ("all " <> show duration <> " ease-out")
      , E.style "outline" "none"
      ] <> (if isVertical
              then [ E.style "left" "50%"
                   , E.style "transform" "translate(-50%, 50%)"
                   , E.style "bottom" (showPercent pct)
                   ]
              else [ E.style "top" "50%"
                   , E.style "transform" "translate(-50%, -50%)"
                   , E.style "left" (showPercent pct)
                   ])
    
    -- Disabled styles
    disabledStyles = if props.disabled
      then [ E.style "opacity" "0.5", E.style "pointer-events" "none" ]
      else []
    
    tabIndexVal = if props.disabled then "-1" else "0"
  in
    E.div_
      (containerStyles <> [ E.dataAttr "orientation" (if isVertical then "vertical" else "horizontal") ])
      [ E.div_
          trackStyles
          [ E.div_ rangeStyles []
          -- Low thumb
          , E.div_
              ( buildThumbStyles lowPercent <> disabledStyles <>
                [ E.dataAttr "thumb" "low"
                , E.attr "tabindex" tabIndexVal
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.rangeVal.low)
                , E.attr "aria-valuemin" (show props.minVal)
                , E.attr "aria-valuemax" (show props.rangeVal.high)
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.ariaLabel "Minimum value"
                ]
              )
              ( if props.showTooltip
                  then [ renderTooltip props props.rangeVal.low ]
                  else []
              )
          -- High thumb
          , E.div_
              ( buildThumbStyles highPercent <> disabledStyles <>
                [ E.dataAttr "thumb" "high"
                , E.attr "tabindex" tabIndexVal
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.rangeVal.high)
                , E.attr "aria-valuemin" (show props.rangeVal.low)
                , E.attr "aria-valuemax" (show props.maxVal)
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.ariaLabel "Maximum value"
                ]
              )
              ( if props.showTooltip
                  then [ renderTooltip props props.rangeVal.high ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else E.text ""
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // supporting elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render tooltip
-- |
-- | Displays the current value in a floating label above the thumb.
renderTooltip :: forall msg. SliderProps msg -> Number -> E.Element msg
renderTooltip props val =
  let
    bgColor = getColor props.tooltipBackgroundColor defaultTooltipBgColor
    textColor = getColor props.tooltipTextColor defaultTooltipTextColor
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "top" "-32px"
      , E.style "left" "50%"
      , E.style "transform" "translateX(-50%)"
      , E.style "padding" "4px 8px"
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss textColor)
      , E.style "font-size" "12px"
      , E.style "border-radius" "4px"
      , E.style "white-space" "nowrap"
      , E.style "pointer-events" "none"
      ]
      [ E.text (show (round val)) ]

-- | Render tick marks
-- |
-- | Displays step indicators along the track.
renderTicks :: forall msg. SliderProps msg -> E.Element msg
renderTicks props =
  let
    isVertical = props.orientation == Vertical
    numSteps = round ((props.maxVal - props.minVal) / props.step)
    ticks = range 0 numSteps
    tckColor = getColor props.tickColor defaultTickColor
    
    containerStyles =
      [ E.style "position" "absolute"
      , E.style "display" "flex"
      , E.style "justify-content" "space-between"
      ] <> (if isVertical
              then [ E.style "left" "100%"
                   , E.style "margin-left" "8px"
                   , E.style "height" "100%"
                   , E.style "flex-direction" "column"
                   ]
              else [ E.style "top" "100%"
                   , E.style "margin-top" "8px"
                   , E.style "width" "100%"
                   ])
    
    renderTick :: Int -> E.Element msg
    renderTick idx =
      let
        tickVal = props.minVal + (toNumber idx * props.step)
      in
        E.div_
          [ E.style "display" "flex"
          , E.style "flex-direction" "column"
          , E.style "align-items" "center"
          ]
          [ E.div_
              [ E.style "width" "2px"
              , E.style "height" "4px"
              , E.style "background-color" (Color.toLegacyCss tckColor)
              ]
              []
          , E.span_
              [ E.style "font-size" "10px"
              , E.style "color" (Color.toLegacyCss tckColor)
              , E.style "margin-top" "4px"
              ]
              [ E.text (show (round tickVal)) ]
          ]
  in
    E.div_ containerStyles (map renderTick ticks)
