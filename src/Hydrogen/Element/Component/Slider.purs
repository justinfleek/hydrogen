-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // slider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Slider Component
-- |
-- | Range slider components for selecting numeric values.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Component.Slider as Slider
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic single value slider
-- | Slider.slider 
-- |   [ Slider.value 50.0
-- |   , Slider.onChange HandleSliderChange
-- |   ]
-- |
-- | -- Range slider (dual thumbs)
-- | Slider.rangeSlider
-- |   [ Slider.rangeValue { low: 20.0, high: 80.0 }
-- |   , Slider.onRangeChange HandleRangeChange
-- |   ]
-- |
-- | -- Vertical slider with ticks
-- | Slider.slider
-- |   [ Slider.value 30.0
-- |   , Slider.orientation Slider.Vertical
-- |   , Slider.showTicks true
-- |   , Slider.step 10.0
-- |   ]
-- | ```
module Hydrogen.Element.Component.Slider
  ( -- * Slider Components
    slider
  , rangeSlider
    -- * Props
  , SliderProps
  , SliderProp
  , RangeValue
  , defaultProps
    -- * Prop Builders
  , value
  , rangeValue
  , minValue
  , maxValue
  , step
  , sliderDisabled
  , orientation
  , showTicks
  , showTooltip
  , className
  , onChange
  , onRangeChange
  , sliderAriaLabel
    -- * Types
  , Orientation(..)
  ) where

import Prelude
  ( class Eq
  , show
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
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Slider orientation
data Orientation
  = Horizontal
  | Vertical

derive instance eqOrientation :: Eq Orientation

-- | Range slider value
type RangeValue =
  { low :: Number
  , high :: Number
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type SliderProps msg =
  { value :: Number
  , rangeVal :: RangeValue
  , minVal :: Number
  , maxVal :: Number
  , step :: Number
  , disabled :: Boolean
  , orientation :: Orientation
  , showTicks :: Boolean
  , showTooltip :: Boolean
  , className :: String
  , onChange :: Maybe (Number -> msg)
  , onRangeChange :: Maybe (RangeValue -> msg)
  , ariaLabel :: String
  }

type SliderProp msg = SliderProps msg -> SliderProps msg

defaultProps :: forall msg. SliderProps msg
defaultProps =
  { value: 0.0
  , rangeVal: { low: 0.0, high: 100.0 }
  , minVal: 0.0
  , maxVal: 100.0
  , step: 1.0
  , disabled: false
  , orientation: Horizontal
  , showTicks: false
  , showTooltip: false
  , className: ""
  , onChange: Nothing
  , onRangeChange: Nothing
  , ariaLabel: "Slider"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set slider value
value :: forall msg. Number -> SliderProp msg
value v props = props { value = v }

-- | Set range slider value
rangeValue :: forall msg. RangeValue -> SliderProp msg
rangeValue v props = props { rangeVal = v }

-- | Set minimum value
minValue :: forall msg. Number -> SliderProp msg
minValue v props = props { minVal = v }

-- | Set maximum value
maxValue :: forall msg. Number -> SliderProp msg
maxValue v props = props { maxVal = v }

-- | Set step increment
step :: forall msg. Number -> SliderProp msg
step v props = props { step = v }

-- | Set disabled state
sliderDisabled :: forall msg. Boolean -> SliderProp msg
sliderDisabled d props = props { disabled = d }

-- | Set orientation
orientation :: forall msg. Orientation -> SliderProp msg
orientation o props = props { orientation = o }

-- | Show tick marks
showTicks :: forall msg. Boolean -> SliderProp msg
showTicks s props = props { showTicks = s }

-- | Show tooltip on drag
showTooltip :: forall msg. Boolean -> SliderProp msg
showTooltip s props = props { showTooltip = s }

-- | Add custom class
className :: forall msg. String -> SliderProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set value change handler
onChange :: forall msg. (Number -> msg) -> SliderProp msg
onChange handler props = props { onChange = Just handler }

-- | Set range change handler
onRangeChange :: forall msg. (RangeValue -> msg) -> SliderProp msg
onRangeChange handler props = props { onRangeChange = Just handler }

-- | Set ARIA label
sliderAriaLabel :: forall msg. String -> SliderProp msg
sliderAriaLabel l props = props { ariaLabel = l }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate percentage position
toPercent :: Number -> Number -> Number -> Number
toPercent minV maxV val =
  ((val - minV) / (maxV - minV)) * 100.0

-- | Show a number as percentage string
showPercent :: Number -> String
showPercent n = show n <> "%"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Single value slider
-- |
-- | A slider for selecting a single numeric value.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
slider :: forall msg. Array (SliderProp msg) -> E.Element msg
slider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    percent = toPercent props.minVal props.maxVal props.value
    
    trackClasses = 
      if isVertical 
      then "relative w-2 h-full rounded-full bg-secondary"
      else "relative h-2 w-full rounded-full bg-secondary"
    
    rangeClasses =
      if isVertical
      then "absolute w-full rounded-full bg-primary"
      else "absolute h-full rounded-full bg-primary"
    
    thumbClasses =
      "absolute block h-5 w-5 rounded-full border-2 border-primary bg-background ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
    
    containerClasses =
      if isVertical
      then "relative flex h-full w-5 touch-none select-none flex-col items-center"
      else "relative flex w-full touch-none select-none items-center"
    
    rangeStyles = if isVertical
      then [ E.style "bottom" "0", E.style "height" (showPercent percent) ]
      else [ E.style "width" (showPercent percent) ]
    
    thumbStyles = if isVertical
      then [ E.style "left" "50%"
           , E.style "transform" "translate(-50%, 50%)"
           , E.style "bottom" (showPercent percent)
           ]
      else [ E.style "top" "50%"
           , E.style "transform" "translate(-50%, -50%)"
           , E.style "left" (showPercent percent)
           ]
    
    tabIndexVal = if props.disabled then "-1" else "0"
  in
    E.div_
      [ E.classes [ containerClasses, props.className ]
      , E.dataAttr "orientation" (if isVertical then "vertical" else "horizontal")
      ]
      [ E.div_
          [ E.class_ trackClasses ]
          [ E.div_
              ([ E.class_ rangeClasses ] <> rangeStyles)
              []
          , E.div_
              ( [ E.class_ thumbClasses
                , E.attr "tabindex" tabIndexVal
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.value)
                , E.attr "aria-valuemin" (show props.minVal)
                , E.attr "aria-valuemax" (show props.maxVal)
                , E.ariaLabel props.ariaLabel
                ] <> thumbStyles
              )
              ( if props.showTooltip
                  then [ tooltip props.value ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else E.text ""
      ]

-- | Range slider (dual thumbs)
-- |
-- | A slider for selecting a range of values.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
rangeSlider :: forall msg. Array (SliderProp msg) -> E.Element msg
rangeSlider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    lowPercent = toPercent props.minVal props.maxVal props.rangeVal.low
    highPercent = toPercent props.minVal props.maxVal props.rangeVal.high
    
    trackClasses = 
      if isVertical 
      then "relative w-2 h-full rounded-full bg-secondary"
      else "relative h-2 w-full rounded-full bg-secondary"
    
    rangeClasses =
      if isVertical
      then "absolute w-full rounded-full bg-primary"
      else "absolute h-full rounded-full bg-primary"
    
    thumbClasses =
      "absolute block h-5 w-5 rounded-full border-2 border-primary bg-background ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
    
    containerClasses =
      if isVertical
      then "relative flex h-full w-5 touch-none select-none flex-col items-center"
      else "relative flex w-full touch-none select-none items-center"
    
    rangeStyles = if isVertical
      then [ E.style "bottom" (showPercent lowPercent)
           , E.style "height" (showPercent (highPercent - lowPercent))
           ]
      else [ E.style "left" (showPercent lowPercent)
           , E.style "width" (showPercent (highPercent - lowPercent))
           ]
    
    lowThumbStyles = if isVertical
      then [ E.style "left" "50%"
           , E.style "transform" "translate(-50%, 50%)"
           , E.style "bottom" (showPercent lowPercent)
           ]
      else [ E.style "top" "50%"
           , E.style "transform" "translate(-50%, -50%)"
           , E.style "left" (showPercent lowPercent)
           ]
    
    highThumbStyles = if isVertical
      then [ E.style "left" "50%"
           , E.style "transform" "translate(-50%, 50%)"
           , E.style "bottom" (showPercent highPercent)
           ]
      else [ E.style "top" "50%"
           , E.style "transform" "translate(-50%, -50%)"
           , E.style "left" (showPercent highPercent)
           ]
    
    tabIndexVal = if props.disabled then "-1" else "0"
  in
    E.div_
      [ E.classes [ containerClasses, props.className ]
      , E.dataAttr "orientation" (if isVertical then "vertical" else "horizontal")
      ]
      [ E.div_
          [ E.class_ trackClasses ]
          [ E.div_
              ([ E.class_ rangeClasses ] <> rangeStyles)
              []
          , E.div_
              ( [ E.class_ thumbClasses
                , E.dataAttr "thumb" "low"
                , E.attr "tabindex" tabIndexVal
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.rangeVal.low)
                , E.attr "aria-valuemin" (show props.minVal)
                , E.attr "aria-valuemax" (show props.rangeVal.high)
                , E.ariaLabel "Minimum value"
                ] <> lowThumbStyles
              )
              ( if props.showTooltip
                  then [ tooltip props.rangeVal.low ]
                  else []
              )
          , E.div_
              ( [ E.class_ thumbClasses
                , E.dataAttr "thumb" "high"
                , E.attr "tabindex" tabIndexVal
                , E.attr "aria-disabled" (if props.disabled then "true" else "false")
                , E.role "slider"
                , E.attr "aria-valuenow" (show props.rangeVal.high)
                , E.attr "aria-valuemin" (show props.rangeVal.low)
                , E.attr "aria-valuemax" (show props.maxVal)
                , E.ariaLabel "Maximum value"
                ] <> highThumbStyles
              )
              ( if props.showTooltip
                  then [ tooltip props.rangeVal.high ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else E.text ""
      ]

-- | Tooltip display
tooltip :: forall msg. Number -> E.Element msg
tooltip val =
  E.div_
    [ E.classes 
        [ "absolute -top-8 left-1/2 -translate-x-1/2 px-2 py-1 bg-popover text-popover-foreground text-xs rounded shadow-md"
        , "opacity-0 group-hover:opacity-100 group-focus-visible:opacity-100 transition-opacity"
        ]
    ]
    [ E.text (show (round val)) ]

-- | Render tick marks
renderTicks :: forall msg. SliderProps msg -> E.Element msg
renderTicks props =
  let
    isVertical = props.orientation == Vertical
    numSteps = round ((props.maxVal - props.minVal) / props.step)
    ticks = range 0 numSteps
    
    tickContainerClasses =
      if isVertical
      then "absolute left-full ml-2 h-full flex flex-col justify-between"
      else "absolute top-full mt-2 w-full flex justify-between"
  in
    E.div_
      [ E.class_ tickContainerClasses ]
      (map renderTick ticks)
  where
    renderTick :: Int -> E.Element msg
    renderTick idx =
      let
        tickVal = props.minVal + (toNumber idx * props.step)
      in
        E.div_
          [ E.class_ "flex flex-col items-center" ]
          [ E.div_ [ E.class_ "w-0.5 h-1 bg-muted-foreground" ] []
          , E.span_ [ E.class_ "text-xs text-muted-foreground mt-1" ] [ E.text (show (round tickVal)) ]
          ]
