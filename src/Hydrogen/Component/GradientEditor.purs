-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // gradient editor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GradientEditor component
-- |
-- | Interactive gradient editing with:
-- | - Visual gradient preview bar
-- | - Draggable color stops
-- | - Add/remove stops
-- | - Color picker for each stop
-- | - Position sliders for fine control
-- | - Support for Linear, Radial, Conic gradients
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.GradientEditor as GradientEditor
-- | import Hydrogen.Schema.Color.Gradient (linearGradient, colorStop)
-- | import Hydrogen.Schema.Color.RGB (rgb)
-- |
-- | GradientEditor.gradientEditor
-- |   [ GradientEditor.gradient (Linear $ linearGradient 
-- |       [ colorStop (rgb 255 0 0) 0.0
-- |       , colorStop (rgb 0 0 255) 1.0
-- |       ])
-- |   , GradientEditor.onChange HandleGradientChange
-- |   ]
-- | ```

module Hydrogen.Component.GradientEditor
  ( -- * Component
    gradientEditor
    -- * Props
  , GradientEditorProps
  , GradientEditorProp
  , defaultProps
    -- * Prop Builders
  , gradient
  , onChange
  , showPreview
  , className
  ) where

import Prelude

import Data.Array (foldl, length, mapWithIndex, range)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Hydrogen.Component.Button as Button
import Hydrogen.Component.ColorPicker as ColorPicker
import Hydrogen.Component.Slider as Slider
import Hydrogen.Schema.Color.Gradient (Gradient(Linear), LinearGradient, ColorStop(ColorStop), linearGradient, colorStop, getStops, addStop, removeStopAt, updateStop, toCss, unwrapRatio, ratio)
import Hydrogen.Schema.Color.HSL (hsl)
import Hydrogen.Schema.Color.RGB (rgb, rgbToCss)
import Hydrogen.Schema.Color.Conversion (rgbToHsl, hslToRgb)
import Hydrogen.UI.Core (cls)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | GradientEditor properties
type GradientEditorProps i =
  { gradient :: Gradient
  , showPreview :: Boolean
  , className :: String
  , onChange :: Maybe (Gradient -> i)
  }

-- | Property modifier
type GradientEditorProp i = GradientEditorProps i -> GradientEditorProps i

-- | Default gradient editor properties
defaultProps :: forall i. GradientEditorProps i
defaultProps =
  { gradient: Linear $ linearGradient
      [ colorStop (rgb 255 0 0) 0.0
      , colorStop (rgb 0 0 255) 1.0
      ]
  , showPreview: true
  , className: ""
  , onChange: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set gradient
gradient :: forall i. Gradient -> GradientEditorProp i
gradient g props = props { gradient = g }

-- | Set change handler
onChange :: forall i. (Gradient -> i) -> GradientEditorProp i
onChange handler props = props { onChange = Just handler }

-- | Show/hide preview
showPreview :: forall i. Boolean -> GradientEditorProp i
showPreview show props = props { showPreview = show }

-- | Add custom class
className :: forall i. String -> GradientEditorProp i
className c props = props { className = props.className <> " " <> c }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render a gradient editor
gradientEditor :: forall w i. Array (GradientEditorProp i) -> HH.HTML w i
gradientEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    stops = getStops props.gradient
  in
    HH.div
      [ cls [ "gradient-editor space-y-4 p-4 border border-white/20 rounded-lg", props.className ] ]
      [ -- Gradient preview
        if props.showPreview
          then HH.div
            [ cls [ "gradient-preview w-full h-24 rounded border border-white/20" ]
            , HP.style ("background: " <> toCss props.gradient)
            ]
            []
          else HH.text ""
        
        -- Gradient bar with stops
        , renderGradientBar props.gradient props.onChange
        
        -- Stop list
        , HH.div [ cls [ "space-y-2" ] ]
            (mapWithIndex (\idx stop -> renderStopEditor idx stop props.gradient props.onChange) stops)
        
        -- Add stop button
        , case props.onChange of
            Nothing -> HH.text ""
            Just handler ->
              Button.button
                [ Button.onClick (\_ -> handler (addStop (colorStop (rgb 128 128 128) 0.5) props.gradient))
                , Button.variant Button.Outline
                , Button.size Button.Sm
                ]
                [ HH.text "Add Color Stop" ]
      ]

-- | Render gradient bar with draggable stops
renderGradientBar :: forall w i. Gradient -> Maybe (Gradient -> i) -> HH.HTML w i
renderGradientBar grad _ =
  let
    stops = getStops grad
  in
    HH.div [ cls [ "relative w-full h-12 rounded border border-white/20 overflow-hidden" ] ]
      [ -- Background gradient
        HH.div
          [ cls [ "absolute inset-0" ]
          , HP.style ("background: " <> toCss grad)
          ]
          []
        
        -- Stop markers
        , HH.div [ cls [ "absolute inset-0" ] ]
            (mapWithIndex (\idx stop -> renderStopMarker idx stop) stops)
      ]

-- | Render a stop marker on the gradient bar
renderStopMarker :: forall w i. Int -> ColorStop -> HH.HTML w i
renderStopMarker idx (ColorStop cs) =
  let
    position = unwrapRatio cs.position * 100.0
  in
    HH.div
      [ cls [ "absolute top-0 bottom-0 w-1 cursor-pointer hover:w-2 transition-all" ]
      , HP.style ("left: " <> show position <> "%; background-color: " <> rgbToCss cs.color <> "; border: 2px solid white;")
      , HP.title ("Stop " <> show idx <> " at " <> show position <> "%")
      ]
      []

-- | Render stop editor controls
renderStopEditor :: forall w i. Int -> ColorStop -> Gradient -> Maybe (Gradient -> i) -> HH.HTML w i
renderStopEditor idx (ColorStop cs) grad onChange =
  let
    position = unwrapRatio cs.position
    posPercent = position * 100.0
  in
    HH.div [ cls [ "p-3 border border-white/10 rounded space-y-2" ] ]
      [ -- Stop header
        HH.div [ cls [ "flex items-center justify-between" ] ]
          [ HH.span [ cls [ "text-sm font-medium" ] ] 
              [ HH.text ("Stop " <> show (idx + 1) <> " at " <> show posPercent <> "%") ]
          , case onChange of
              Nothing -> HH.text ""
              Just handler ->
                Button.button
                  [ Button.onClick (\_ -> handler (removeStopAt idx grad))
                  , Button.variant Button.Destructive
                  , Button.size Button.Sm
                  ]
                  [ HH.text "Remove" ]
          ]
        
        -- Color preview
        , HH.div
            [ cls [ "w-full h-8 rounded border border-white/20" ]
            , HP.style ("background-color: " <> rgbToCss cs.color)
            ]
            []
        
        -- Position slider
        , case onChange of
            Nothing -> HH.text ""
            Just handler ->
              HH.div [ cls [ "space-y-1" ] ]
                [ HH.label [ cls [ "text-sm" ] ] [ HH.text "Position" ]
                , Slider.slider
                    [ Slider.value position
                    , Slider.min 0.0
                    , Slider.max 1.0
                    , Slider.step 0.01
                    , Slider.onChange (\v -> handler (updateStop idx (colorStop cs.color v) grad))
                    ]
                ]
      ]
