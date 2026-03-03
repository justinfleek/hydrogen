-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // scraper // dashboard // app
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Root Halogen component for the brand scraper dashboard.
-- |
-- | Provides the A:B comparison interface:
-- |   - Left panel: Original PNG screenshot
-- |   - Right panel: Hydrogen Element reconstruction
-- |   - Controls: URL input, scrape trigger, layer inspector
-- |
-- | DEPENDENCIES:
-- |   - Scraper.Layer.Types (LayerStack)
-- |   - Scraper.Dashboard.State (application state)
-- |   - Scraper.Dashboard.View (render functions)
-- |
-- | DEPENDENTS:
-- |   - Scraper.Main (mounts this component)

module Scraper.Dashboard.App
  ( component
  , Query
  , Input
  , Output
  ) where

import Prelude
  ( Unit
  , Void
  , bind
  , discard
  , pure
  , unit
  , map
  , show
  , ($)
  , (<>)
  )

import Data.Const (Const)
import Data.Maybe (Maybe(Nothing, Just))

import Effect.Aff.Class (class MonadAff)

import Halogen (Component, ComponentHTML, HalogenM)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Data.Array (length)

import Scraper.Layer.Types (Layer, LayerStack, stackLayers, stackCount, layerId, layerZIndex, layerBounds, boxX, boxY, boxWidth, boxHeight)
import Scraper.Dashboard.State (State, Action(Initialize, SetUrl, TriggerScrape, SelectLayer), initialState)

-- | No external queries.
type Query :: forall k. k -> Type
type Query = Const Void

-- | No input required.
type Input = Unit

-- | No output events.
type Output = Void

-- | Root dashboard component.
component :: forall m. MonadAff m => Component Query Input Output m
component = H.mkComponent
  { initialState: \_ -> initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Render the dashboard.
render :: forall m. State -> ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "scraper-dashboard") ]
    [ renderHeader state
    , renderComparison state
    , renderLayerInspector state
    ]

-- | Render header with URL input and scrape button.
renderHeader :: forall m. State -> ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "scraper-header") ]
    [ HH.input
        [ HP.type_ HP.InputUrl
        , HP.placeholder "https://example.com"
        , HP.value state.targetUrl
        , HE.onValueInput SetUrl
        ]
    , HH.button
        [ HE.onClick (\_ -> TriggerScrape)
        , HP.disabled state.scraping
        ]
        [ HH.text (if state.scraping then "Scraping..." else "Scrape") ]
    ]

-- | Render A:B comparison panels.
renderComparison :: forall m. State -> ComponentHTML Action () m
renderComparison state =
  let
    visibleLayers = stackLayers state.layers
    visibleCount = length visibleLayers
  in
    HH.div
      [ HP.class_ (H.ClassName "scraper-comparison") ]
      [ HH.div
          [ HP.class_ (H.ClassName "panel-original") ]
          [ HH.text "Original Screenshot" ]
      , HH.div
          [ HP.class_ (H.ClassName "panel-reconstruction") ]
          [ HH.text ("Hydrogen Reconstruction (" <> show visibleCount <> " layers)") ]
      ]

-- | Render layer inspector panel.
renderLayerInspector :: forall m. State -> ComponentHTML Action () m
renderLayerInspector state =
  let
    layers = stackLayers state.layers
    count = stackCount state.layers
  in
    HH.aside
      [ HP.class_ (H.ClassName "layer-inspector") ]
      [ HH.h3_ [ HH.text ("Layers (" <> show count <> ")") ]
      , HH.ul
          [ HP.class_ (H.ClassName "layer-list") ]
          (map renderLayerItem layers)
      ]

-- | Render a single layer item in the inspector.
renderLayerItem :: forall m. Layer -> ComponentHTML Action () m
renderLayerItem layer =
  let
    uuid = layerId layer
    z = layerZIndex layer
    bounds = layerBounds layer
    x = boxX bounds
    y = boxY bounds
    w = boxWidth bounds
    h = boxHeight bounds
  in
    HH.li
      [ HP.class_ (H.ClassName "layer-item")
      , HE.onClick (\_ -> SelectLayer (Just uuid))
      ]
      [ HH.span
          [ HP.class_ (H.ClassName "layer-z") ]
          [ HH.text ("z:" <> show z) ]
      , HH.span
          [ HP.class_ (H.ClassName "layer-bounds") ]
          [ HH.text (show x <> "," <> show y <> " " <> show w <> "x" <> show h) ]
      ]

-- | Handle actions.
handleAction :: forall m. MonadAff m => Action -> HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    pure unit
  
  SetUrl url -> do
    H.modify_ \s -> s { targetUrl = url }
  
  TriggerScrape -> do
    H.modify_ \s -> s { scraping = true }
    -- ZMQ call to Haskell backend will go here
    H.modify_ \s -> s { scraping = false }
  
  SelectLayer maybeId -> do
    H.modify_ \s -> s { selectedLayer = maybeId }
