-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // scraper // dashboard // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Application state for the brand scraper dashboard.
-- |
-- | Tracks:
-- |   - Target URL being scraped
-- |   - Scrape operation status
-- |   - Original screenshot data
-- |   - Extracted layer stack
-- |   - Selected layer for inspection
-- |
-- | DEPENDENCIES:
-- |   - Scraper.Layer.Types (LayerStack, UUID5)
-- |
-- | DEPENDENTS:
-- |   - Scraper.Dashboard.App (uses state)
-- |   - Scraper.Dashboard.View (renders state)

module Scraper.Dashboard.State
  ( -- * State
    State
  , initialState
  , Screenshot
  
  -- * Actions
  , Action
      ( Initialize
      , SetUrl
      , TriggerScrape
      , ScrapeComplete
      , ScrapeError
      , SelectLayer
      , ToggleLayerVisibility
      )
  ) where

import Prelude (Unit)

import Data.Maybe (Maybe(Nothing))

import Scraper.Layer.Types (LayerStack, UUID5, emptyStack)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Dashboard application state.
type State =
  { targetUrl :: String            -- URL to scrape
  , scraping :: Boolean            -- Whether scrape is in progress
  , screenshot :: Maybe Screenshot -- Original PNG data
  , layers :: LayerStack           -- Extracted z-indexed layers
  , selectedLayer :: Maybe UUID5   -- Currently selected layer for inspection
  , errorMessage :: Maybe String   -- Last error message
  }

-- | Screenshot data from original page capture.
type Screenshot =
  { width :: Int      -- Width in pixels
  , height :: Int     -- Height in pixels
  , dataUrl :: String -- PNG as data URL
  }

-- | Initial state with empty values.
initialState :: State
initialState =
  { targetUrl: ""
  , scraping: false
  , screenshot: Nothing
  , layers: emptyStack
  , selectedLayer: Nothing
  , errorMessage: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Actions the dashboard can perform.
data Action
  = Initialize                           -- Component mounted
  | SetUrl String                        -- User typed URL
  | TriggerScrape                        -- User clicked scrape button
  | ScrapeComplete Screenshot LayerStack -- Scrape finished successfully
  | ScrapeError String                   -- Scrape failed with error
  | SelectLayer (Maybe UUID5)            -- User selected a layer
  | ToggleLayerVisibility UUID5          -- User toggled layer visibility
