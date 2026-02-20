-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                         // hydrogen // slider
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Range slider component
-- |
-- | Slider components for selecting numeric values.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.Slider as Slider
-- |
-- | -- Basic single value slider
-- | Slider.slider 
-- |   [ Slider.value 50
-- |   , Slider.onChange HandleSliderChange
-- |   ]
-- |
-- | -- Range slider (dual thumbs)
-- | Slider.rangeSlider
-- |   [ Slider.rangeValue { min: 20, max: 80 }
-- |   , Slider.onRangeChange HandleRangeChange
-- |   ]
-- |
-- | -- Vertical slider with ticks
-- | Slider.slider
-- |   [ Slider.value 30
-- |   , Slider.orientation Slider.Vertical
-- |   , Slider.showTicks true
-- |   , Slider.step 10
-- |   ]
-- |
-- | -- With tooltip on drag
-- | Slider.slider
-- |   [ Slider.value 75
-- |   , Slider.showTooltip true
-- |   ]
-- | ```
module Hydrogen.Component.Slider
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
  , min
  , max
  , step
  , disabled
  , orientation
  , showTicks
  , showTooltip
  , className
  , onChange
  , onRangeChange
  , ariaLabel
  , ariaLabelMin
  , ariaLabelMax
    -- * Types
  , Orientation(..)
    -- * FFI
  , SliderElement
  ) where

import Prelude

import Data.Array (foldl, range)
import Data.Int (round)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.DOM.Element (Element)
import Web.Event.Event (Event)

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
  { min :: Number
  , max :: Number
  }

-- | Opaque slider element type
foreign import data SliderElement :: Type

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initialize slider pointer events
foreign import initSliderImpl :: EffectFn3 Element (Number -> Effect Unit) { min :: Number, max :: Number, step :: Number, vertical :: Boolean } SliderElement

-- | Initialize range slider pointer events
foreign import initRangeSliderImpl :: EffectFn3 Element (RangeValue -> Effect Unit) { min :: Number, max :: Number, step :: Number, vertical :: Boolean } SliderElement

-- | Cleanup slider
foreign import destroySliderImpl :: EffectFn1 SliderElement Unit

-- | Get current position during drag
foreign import getSliderPositionImpl :: EffectFn2 Event { min :: Number, max :: Number, step :: Number, vertical :: Boolean } Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // props
-- ═══════════════════════════════════════════════════════════════════════════════

type SliderProps i =
  { value :: Number
  , rangeValue :: RangeValue
  , min :: Number
  , max :: Number
  , step :: Number
  , disabled :: Boolean
  , orientation :: Orientation
  , showTicks :: Boolean
  , showTooltip :: Boolean
  , className :: String
  , onChange :: Maybe (Number -> i)
  , onRangeChange :: Maybe (RangeValue -> i)
  , ariaLabel :: String
  , ariaLabelMin :: String
  , ariaLabelMax :: String
  }

type SliderProp i = SliderProps i -> SliderProps i

defaultProps :: forall i. SliderProps i
defaultProps =
  { value: 0.0
  , rangeValue: { min: 0.0, max: 100.0 }
  , min: 0.0
  , max: 100.0
  , step: 1.0
  , disabled: false
  , orientation: Horizontal
  , showTicks: false
  , showTooltip: false
  , className: ""
  , onChange: Nothing
  , onRangeChange: Nothing
  , ariaLabel: "Slider"
  , ariaLabelMin: "Minimum value"
  , ariaLabelMax: "Maximum value"
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set slider value
value :: forall i. Number -> SliderProp i
value v props = props { value = v }

-- | Set range slider value
rangeValue :: forall i. RangeValue -> SliderProp i
rangeValue v props = props { rangeValue = v }

-- | Set minimum value
min :: forall i. Number -> SliderProp i
min v props = props { min = v }

-- | Set maximum value
max :: forall i. Number -> SliderProp i
max v props = props { max = v }

-- | Set step increment
step :: forall i. Number -> SliderProp i
step v props = props { step = v }

-- | Set disabled state
disabled :: forall i. Boolean -> SliderProp i
disabled d props = props { disabled = d }

-- | Set orientation
orientation :: forall i. Orientation -> SliderProp i
orientation o props = props { orientation = o }

-- | Show tick marks
showTicks :: forall i. Boolean -> SliderProp i
showTicks s props = props { showTicks = s }

-- | Show tooltip on drag
showTooltip :: forall i. Boolean -> SliderProp i
showTooltip s props = props { showTooltip = s }

-- | Add custom class
className :: forall i. String -> SliderProp i
className c props = props { className = props.className <> " " <> c }

-- | Set value change handler
onChange :: forall i. (Number -> i) -> SliderProp i
onChange handler props = props { onChange = Just handler }

-- | Set range change handler
onRangeChange :: forall i. (RangeValue -> i) -> SliderProp i
onRangeChange handler props = props { onRangeChange = Just handler }

-- | Set ARIA label
ariaLabel :: forall i. String -> SliderProp i
ariaLabel l props = props { ariaLabel = l }

-- | Set ARIA label for min thumb
ariaLabelMin :: forall i. String -> SliderProp i
ariaLabelMin l props = props { ariaLabelMin = l }

-- | Set ARIA label for max thumb
ariaLabelMax :: forall i. String -> SliderProp i
ariaLabelMax l props = props { ariaLabelMax = l }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // components
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate percentage position
toPercent :: Number -> Number -> Number -> Number
toPercent minVal maxVal val =
  ((val - minVal) / (maxVal - minVal)) * 100.0

-- | Single value slider
slider :: forall w i. Array (SliderProp i) -> HH.HTML w i
slider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    percent = toPercent props.min props.max props.value
    
    trackClasses = 
      if isVertical 
      then "relative w-2 h-full rounded-full bg-secondary"
      else "relative h-2 w-full rounded-full bg-secondary"
    
    rangeClasses =
      if isVertical
      then "absolute w-full rounded-full bg-primary"
      else "absolute h-full rounded-full bg-primary"
    
    rangeStyle =
      if isVertical
      then "bottom: 0; height: " <> show percent <> "%"
      else "width: " <> show percent <> "%"
    
    thumbClasses =
      "absolute block h-5 w-5 rounded-full border-2 border-primary bg-background ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
    
    thumbStyle =
      if isVertical
      then "left: 50%; transform: translate(-50%, 50%); bottom: " <> show percent <> "%"
      else "top: 50%; transform: translate(-50%, -50%); left: " <> show percent <> "%"
    
    containerClasses =
      if isVertical
      then "relative flex h-full w-5 touch-none select-none flex-col items-center"
      else "relative flex w-full touch-none select-none items-center"
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-orientation") (if isVertical then "vertical" else "horizontal")
      ]
      [ HH.div
          [ cls [ trackClasses ] ]
          [ HH.div
              [ cls [ rangeClasses ]
              , HP.attr (HH.AttrName "style") rangeStyle
              ]
              []
          , HH.div
              [ cls [ thumbClasses ]
              , HP.attr (HH.AttrName "style") thumbStyle
              , HP.tabIndex (if props.disabled then (-1) else 0)
              , ARIA.disabled (show props.disabled)
              , ARIA.role "slider"
              , ARIA.valueNow (show props.value)
              , ARIA.valueMin (show props.min)
              , ARIA.valueMax (show props.max)
              , ARIA.label props.ariaLabel
              ]
              ( if props.showTooltip
                  then [ tooltip props.value ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else HH.text ""
      ]

-- | Range slider (dual thumbs)
rangeSlider :: forall w i. Array (SliderProp i) -> HH.HTML w i
rangeSlider propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isVertical = props.orientation == Vertical
    minPercent = toPercent props.min props.max props.rangeValue.min
    maxPercent = toPercent props.min props.max props.rangeValue.max
    
    trackClasses = 
      if isVertical 
      then "relative w-2 h-full rounded-full bg-secondary"
      else "relative h-2 w-full rounded-full bg-secondary"
    
    rangeClasses =
      if isVertical
      then "absolute w-full rounded-full bg-primary"
      else "absolute h-full rounded-full bg-primary"
    
    rangeStyle =
      if isVertical
      then "bottom: " <> show minPercent <> "%; height: " <> show (maxPercent - minPercent) <> "%"
      else "left: " <> show minPercent <> "%; width: " <> show (maxPercent - minPercent) <> "%"
    
    thumbClasses =
      "absolute block h-5 w-5 rounded-full border-2 border-primary bg-background ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50"
    
    minThumbStyle =
      if isVertical
      then "left: 50%; transform: translate(-50%, 50%); bottom: " <> show minPercent <> "%"
      else "top: 50%; transform: translate(-50%, -50%); left: " <> show minPercent <> "%"
    
    maxThumbStyle =
      if isVertical
      then "left: 50%; transform: translate(-50%, 50%); bottom: " <> show maxPercent <> "%"
      else "top: 50%; transform: translate(-50%, -50%); left: " <> show maxPercent <> "%"
    
    containerClasses =
      if isVertical
      then "relative flex h-full w-5 touch-none select-none flex-col items-center"
      else "relative flex w-full touch-none select-none items-center"
  in
    HH.div
      [ cls [ containerClasses, props.className ]
      , HP.attr (HH.AttrName "data-orientation") (if isVertical then "vertical" else "horizontal")
      ]
      [ HH.div
          [ cls [ trackClasses ] ]
          [ HH.div
              [ cls [ rangeClasses ]
              , HP.attr (HH.AttrName "style") rangeStyle
              ]
              []
          -- Min thumb
          , HH.div
              [ cls [ thumbClasses ]
              , HP.attr (HH.AttrName "style") minThumbStyle
              , HP.attr (HH.AttrName "data-thumb") "min"
              , HP.tabIndex (if props.disabled then (-1) else 0)
              , ARIA.disabled (show props.disabled)
              , ARIA.role "slider"
              , ARIA.valueNow (show props.rangeValue.min)
              , ARIA.valueMin (show props.min)
              , ARIA.valueMax (show props.rangeValue.max)
              , ARIA.label props.ariaLabelMin
              ]
              ( if props.showTooltip
                  then [ tooltip props.rangeValue.min ]
                  else []
              )
          -- Max thumb
          , HH.div
              [ cls [ thumbClasses ]
              , HP.attr (HH.AttrName "style") maxThumbStyle
              , HP.attr (HH.AttrName "data-thumb") "max"
              , HP.tabIndex (if props.disabled then (-1) else 0)
              , ARIA.disabled (show props.disabled)
              , ARIA.role "slider"
              , ARIA.valueNow (show props.rangeValue.max)
              , ARIA.valueMin (show props.rangeValue.min)
              , ARIA.valueMax (show props.max)
              , ARIA.label props.ariaLabelMax
              ]
              ( if props.showTooltip
                  then [ tooltip props.rangeValue.max ]
                  else []
              )
          ]
      , if props.showTicks
          then renderTicks props
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tooltip display
tooltip :: forall w i. Number -> HH.HTML w i
tooltip val =
  HH.div
    [ cls 
        [ "absolute -top-8 left-1/2 -translate-x-1/2 px-2 py-1 bg-popover text-popover-foreground text-xs rounded shadow-md"
        , "opacity-0 group-hover:opacity-100 group-focus-visible:opacity-100 transition-opacity"
        ]
    ]
    [ HH.text (show (round val)) ]

-- | Render tick marks
renderTicks :: forall w i. SliderProps i -> HH.HTML w i
renderTicks props =
  let
    isVertical = props.orientation == Vertical
    numSteps = round ((props.max - props.min) / props.step)
    ticks = range 0 numSteps
    
    tickContainerClasses =
      if isVertical
      then "absolute left-full ml-2 h-full flex flex-col justify-between"
      else "absolute top-full mt-2 w-full flex justify-between"
  in
    HH.div
      [ cls [ tickContainerClasses ] ]
      (map renderTick ticks)
  where
    renderTick :: Int -> HH.HTML w i
    renderTick _ =
      HH.div
        [ cls [ "w-0.5 h-1 bg-muted-foreground" ] ]
        []
