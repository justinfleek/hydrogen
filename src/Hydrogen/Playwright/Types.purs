-- | Types for Playwright FFI bindings.
module Hydrogen.Playwright.Types
  ( BrowserType(..)
  , Browser
  , BrowserContext
  , Page
  , ElementHandle
  , Locator
  , LaunchOptions
  , ScreenshotOptions
  , PDFOptions
  , PDFMargin
  , LoadState(..)
  ) where

import Prelude

-- | Supported browser engines.
data BrowserType
  = Chromium
  | Firefox
  | Webkit

derive instance eqBrowserType :: Eq BrowserType
derive instance ordBrowserType :: Ord BrowserType

instance showBrowserType :: Show BrowserType where
  show Chromium = "Chromium"
  show Firefox = "Firefox"
  show Webkit = "Webkit"

-- | Page load states.
data LoadState
  = Load              -- ^ Wait for the load event
  | DOMContentLoaded  -- ^ Wait for DOMContentLoaded event
  | NetworkIdle       -- ^ Wait for network to be idle

derive instance eqLoadState :: Eq LoadState
derive instance ordLoadState :: Ord LoadState

instance showLoadState :: Show LoadState where
  show Load = "Load"
  show DOMContentLoaded = "DOMContentLoaded"
  show NetworkIdle = "NetworkIdle"

-- | Opaque type representing a Playwright Browser instance.
foreign import data Browser :: Type

-- | Opaque type representing a browser context.
foreign import data BrowserContext :: Type

-- | Opaque type representing a browser page/tab.
foreign import data Page :: Type

-- | Opaque type representing a DOM element handle.
foreign import data ElementHandle :: Type

-- | Opaque type representing a locator (lazy element query).
foreign import data Locator :: Type

-- | Options for launching a browser.
type LaunchOptions =
  { headless :: Boolean
  , slowMo :: Int        -- ^ Slow down operations by ms
  , timeout :: Int       -- ^ Maximum time in ms to wait for browser to start
  , devtools :: Boolean  -- ^ Open devtools (Chromium only)
  }

-- | Options for taking screenshots.
type ScreenshotOptions =
  { path :: String       -- ^ File path to save screenshot
  , fullPage :: Boolean  -- ^ Capture full scrollable page
  , type :: String       -- ^ "png" or "jpeg"
  , quality :: Int       -- ^ Quality for jpeg (0-100)
  }

-- | Margin for PDF generation.
type PDFMargin =
  { top :: String
  , right :: String
  , bottom :: String
  , left :: String
  }

-- | Options for generating PDFs.
type PDFOptions =
  { path :: String           -- ^ File path to save PDF
  , format :: String         -- ^ Paper format: "A4", "Letter", etc.
  , printBackground :: Boolean
  , margin :: PDFMargin
  }
