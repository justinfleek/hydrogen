-- | Playwright browser automation FFI bindings.
-- |
-- | This module provides PureScript bindings for Playwright, enabling
-- | browser automation, testing, and screenshot capture.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Playwright as PW
-- |
-- | main :: Effect Unit
-- | main = launchAff_ do
-- |   browser <- PW.launch PW.Chromium PW.defaultLaunchOptions
-- |   page <- PW.newPage browser
-- |   PW.goto page "https://example.com"
-- |   PW.screenshot page { path: "screenshot.png" }
-- |   PW.close browser
-- | ```
module Hydrogen.Playwright
  ( -- * Browser Types (re-exported from Hydrogen.Playwright.Types)
    module Types
  
    -- * Launch Options
  , defaultLaunchOptions
  
    -- * Browser Operations
  , launch
  , launchPersistentContext
  , close
  , newContext
  , newPage
  
    -- * Navigation
  , goto
  , goBack
  , goForward
  , reload
  , waitForLoadState
  
    -- * Selectors & Elements
  , locator
  , getByRole
  , getByText
  , getByTestId
  , getByLabel
  , getByPlaceholder
  , first
  , last
  , nth
  , count
  
    -- * Element Interactions
  , click
  , dblclick
  , fill
  , type_
  , press
  , check
  , uncheck
  , selectOption
  , hover
  , focus
  , blur
  
    -- * Element State
  , isVisible
  , isHidden
  , isEnabled
  , isDisabled
  , isChecked
  , textContent
  , innerText
  , innerHTML
  , getAttribute
  , inputValue
  
    -- * Waiting
  , waitForSelector
  , waitForTimeout
  , waitForURL
  , waitForFunction
  
    -- * Screenshots & PDF
  , defaultScreenshotOptions
  , screenshot
  , screenshotElement
  , defaultPDFOptions
  , pdf
  
    -- * Evaluation
  , evaluate
  , evaluateHandle
  
    -- * Page Info
  , url
  , title
  , content
  , setContent
  
  ) where

import Prelude


import Data.Nullable (Nullable)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Hydrogen.Playwright.Types (BrowserType(..), Browser, BrowserContext, Page, ElementHandle, Locator, LaunchOptions, ScreenshotOptions, PDFOptions, PDFMargin, LoadState(..)) as Types
import Hydrogen.Playwright.Types (BrowserType(..), Browser, BrowserContext, Page, ElementHandle, Locator, LaunchOptions, ScreenshotOptions, PDFOptions, LoadState(..))

-- =============================================================================
--                                                                     // launch
-- =============================================================================

-- | Launch a browser instance.
launch :: BrowserType -> LaunchOptions -> Aff Browser
launch bt opts = fromEffectFnAff $ launchImpl (browserTypeToString bt) opts

foreign import launchImpl :: String -> LaunchOptions -> EffectFnAff Browser

-- | Launch a persistent browser context (preserves cookies, localStorage).
launchPersistentContext :: BrowserType -> String -> LaunchOptions -> Aff BrowserContext
launchPersistentContext bt userDataDir opts = 
  fromEffectFnAff $ launchPersistentContextImpl (browserTypeToString bt) userDataDir opts

foreign import launchPersistentContextImpl :: String -> String -> LaunchOptions -> EffectFnAff BrowserContext

-- | Close the browser.
close :: Browser -> Aff Unit
close = fromEffectFnAff <<< closeImpl

foreign import closeImpl :: Browser -> EffectFnAff Unit

-- | Create a new browser context.
newContext :: Browser -> Aff BrowserContext
newContext = fromEffectFnAff <<< newContextImpl

foreign import newContextImpl :: Browser -> EffectFnAff BrowserContext

-- | Create a new page in the browser.
newPage :: Browser -> Aff Page
newPage = fromEffectFnAff <<< newPageImpl

foreign import newPageImpl :: Browser -> EffectFnAff Page

-- =============================================================================
--                                                                // navigation
-- =============================================================================

-- | Navigate to a URL.
goto :: Page -> String -> Aff Unit
goto page url' = fromEffectFnAff $ gotoImpl page url'

foreign import gotoImpl :: Page -> String -> EffectFnAff Unit

-- | Navigate back.
goBack :: Page -> Aff Unit
goBack = fromEffectFnAff <<< goBackImpl

foreign import goBackImpl :: Page -> EffectFnAff Unit

-- | Navigate forward.
goForward :: Page -> Aff Unit
goForward = fromEffectFnAff <<< goForwardImpl

foreign import goForwardImpl :: Page -> EffectFnAff Unit

-- | Reload the page.
reload :: Page -> Aff Unit
reload = fromEffectFnAff <<< reloadImpl

foreign import reloadImpl :: Page -> EffectFnAff Unit

-- | Wait for the page to reach a load state.
waitForLoadState :: Page -> LoadState -> Aff Unit
waitForLoadState page state = fromEffectFnAff $ waitForLoadStateImpl page (loadStateToString state)

foreign import waitForLoadStateImpl :: Page -> String -> EffectFnAff Unit

loadStateToString :: LoadState -> String
loadStateToString = case _ of
  Load -> "load"
  DOMContentLoaded -> "domcontentloaded"
  NetworkIdle -> "networkidle"

-- =============================================================================
--                                                                 // selectors
-- =============================================================================

-- | Create a locator for the given selector.
locator :: Page -> String -> Effect Locator
locator = locatorImpl

foreign import locatorImpl :: Page -> String -> Effect Locator

-- | Locate element by role.
getByRole :: Page -> String -> Effect Locator
getByRole = getByRoleImpl

foreign import getByRoleImpl :: Page -> String -> Effect Locator

-- | Locate element by text content.
getByText :: Page -> String -> Effect Locator
getByText = getByTextImpl

foreign import getByTextImpl :: Page -> String -> Effect Locator

-- | Locate element by test ID.
getByTestId :: Page -> String -> Effect Locator
getByTestId = getByTestIdImpl

foreign import getByTestIdImpl :: Page -> String -> Effect Locator

-- | Locate element by label.
getByLabel :: Page -> String -> Effect Locator
getByLabel = getByLabelImpl

foreign import getByLabelImpl :: Page -> String -> Effect Locator

-- | Locate element by placeholder.
getByPlaceholder :: Page -> String -> Effect Locator
getByPlaceholder = getByPlaceholderImpl

foreign import getByPlaceholderImpl :: Page -> String -> Effect Locator

-- | Get the first matching element.
first :: Locator -> Effect Locator
first = firstImpl

foreign import firstImpl :: Locator -> Effect Locator

-- | Get the last matching element.
last :: Locator -> Effect Locator
last = lastImpl

foreign import lastImpl :: Locator -> Effect Locator

-- | Get the nth matching element.
nth :: Locator -> Int -> Effect Locator
nth = nthImpl

foreign import nthImpl :: Locator -> Int -> Effect Locator

-- | Count matching elements.
count :: Locator -> Aff Int
count = fromEffectFnAff <<< countImpl

foreign import countImpl :: Locator -> EffectFnAff Int

-- =============================================================================
--                                                              // interactions
-- =============================================================================

-- | Click an element.
click :: Locator -> Aff Unit
click = fromEffectFnAff <<< clickImpl

foreign import clickImpl :: Locator -> EffectFnAff Unit

-- | Double-click an element.
dblclick :: Locator -> Aff Unit
dblclick = fromEffectFnAff <<< dblclickImpl

foreign import dblclickImpl :: Locator -> EffectFnAff Unit

-- | Fill an input with text (clears existing content first).
fill :: Locator -> String -> Aff Unit
fill loc text = fromEffectFnAff $ fillImpl loc text

foreign import fillImpl :: Locator -> String -> EffectFnAff Unit

-- | Type text into an element (character by character).
type_ :: Locator -> String -> Aff Unit
type_ loc text = fromEffectFnAff $ typeImpl loc text

foreign import typeImpl :: Locator -> String -> EffectFnAff Unit

-- | Press a key.
press :: Locator -> String -> Aff Unit
press loc key = fromEffectFnAff $ pressImpl loc key

foreign import pressImpl :: Locator -> String -> EffectFnAff Unit

-- | Check a checkbox or radio button.
check :: Locator -> Aff Unit
check = fromEffectFnAff <<< checkImpl

foreign import checkImpl :: Locator -> EffectFnAff Unit

-- | Uncheck a checkbox.
uncheck :: Locator -> Aff Unit
uncheck = fromEffectFnAff <<< uncheckImpl

foreign import uncheckImpl :: Locator -> EffectFnAff Unit

-- | Select an option from a dropdown.
selectOption :: Locator -> String -> Aff Unit
selectOption loc value = fromEffectFnAff $ selectOptionImpl loc value

foreign import selectOptionImpl :: Locator -> String -> EffectFnAff Unit

-- | Hover over an element.
hover :: Locator -> Aff Unit
hover = fromEffectFnAff <<< hoverImpl

foreign import hoverImpl :: Locator -> EffectFnAff Unit

-- | Focus an element.
focus :: Locator -> Aff Unit
focus = fromEffectFnAff <<< focusImpl

foreign import focusImpl :: Locator -> EffectFnAff Unit

-- | Blur an element.
blur :: Locator -> Aff Unit
blur = fromEffectFnAff <<< blurImpl

foreign import blurImpl :: Locator -> EffectFnAff Unit

-- =============================================================================
--                                                             // element state
-- =============================================================================

-- | Check if element is visible.
isVisible :: Locator -> Aff Boolean
isVisible = fromEffectFnAff <<< isVisibleImpl

foreign import isVisibleImpl :: Locator -> EffectFnAff Boolean

-- | Check if element is hidden.
isHidden :: Locator -> Aff Boolean
isHidden = fromEffectFnAff <<< isHiddenImpl

foreign import isHiddenImpl :: Locator -> EffectFnAff Boolean

-- | Check if element is enabled.
isEnabled :: Locator -> Aff Boolean
isEnabled = fromEffectFnAff <<< isEnabledImpl

foreign import isEnabledImpl :: Locator -> EffectFnAff Boolean

-- | Check if element is disabled.
isDisabled :: Locator -> Aff Boolean
isDisabled = fromEffectFnAff <<< isDisabledImpl

foreign import isDisabledImpl :: Locator -> EffectFnAff Boolean

-- | Check if checkbox/radio is checked.
isChecked :: Locator -> Aff Boolean
isChecked = fromEffectFnAff <<< isCheckedImpl

foreign import isCheckedImpl :: Locator -> EffectFnAff Boolean

-- | Get text content of an element.
textContent :: Locator -> Aff (Nullable String)
textContent = fromEffectFnAff <<< textContentImpl

foreign import textContentImpl :: Locator -> EffectFnAff (Nullable String)

-- | Get inner text of an element.
innerText :: Locator -> Aff String
innerText = fromEffectFnAff <<< innerTextImpl

foreign import innerTextImpl :: Locator -> EffectFnAff String

-- | Get inner HTML of an element.
innerHTML :: Locator -> Aff String
innerHTML = fromEffectFnAff <<< innerHTMLImpl

foreign import innerHTMLImpl :: Locator -> EffectFnAff String

-- | Get attribute value.
getAttribute :: Locator -> String -> Aff (Nullable String)
getAttribute loc attr = fromEffectFnAff $ getAttributeImpl loc attr

foreign import getAttributeImpl :: Locator -> String -> EffectFnAff (Nullable String)

-- | Get input value.
inputValue :: Locator -> Aff String
inputValue = fromEffectFnAff <<< inputValueImpl

foreign import inputValueImpl :: Locator -> EffectFnAff String

-- =============================================================================
--                                                                  // waiting
-- =============================================================================

-- | Wait for a selector to appear.
waitForSelector :: Page -> String -> Aff ElementHandle
waitForSelector page sel = fromEffectFnAff $ waitForSelectorImpl page sel

foreign import waitForSelectorImpl :: Page -> String -> EffectFnAff ElementHandle

-- | Wait for a timeout (milliseconds).
waitForTimeout :: Page -> Int -> Aff Unit
waitForTimeout page ms = fromEffectFnAff $ waitForTimeoutImpl page ms

foreign import waitForTimeoutImpl :: Page -> Int -> EffectFnAff Unit

-- | Wait for URL to match.
waitForURL :: Page -> String -> Aff Unit
waitForURL page url' = fromEffectFnAff $ waitForURLImpl page url'

foreign import waitForURLImpl :: Page -> String -> EffectFnAff Unit

-- | Wait for a function to return truthy.
waitForFunction :: Page -> String -> Aff Unit
waitForFunction page fn = fromEffectFnAff $ waitForFunctionImpl page fn

foreign import waitForFunctionImpl :: Page -> String -> EffectFnAff Unit

-- =============================================================================
--                                                           // screenshots/pdf
-- =============================================================================

-- | Default screenshot options.
defaultScreenshotOptions :: ScreenshotOptions
defaultScreenshotOptions =
  { path: ""
  , fullPage: false
  , type: "png"
  , quality: 100
  }

-- | Take a screenshot of the page.
screenshot :: Page -> ScreenshotOptions -> Aff Unit
screenshot page opts = fromEffectFnAff $ screenshotImpl page opts

foreign import screenshotImpl :: Page -> ScreenshotOptions -> EffectFnAff Unit

-- | Take a screenshot of an element.
screenshotElement :: Locator -> ScreenshotOptions -> Aff Unit
screenshotElement loc opts = fromEffectFnAff $ screenshotElementImpl loc opts

foreign import screenshotElementImpl :: Locator -> ScreenshotOptions -> EffectFnAff Unit

-- | Default PDF options.
defaultPDFOptions :: PDFOptions
defaultPDFOptions =
  { path: ""
  , format: "A4"
  , printBackground: true
  , margin: { top: "0", right: "0", bottom: "0", left: "0" }
  }

-- | Generate a PDF of the page (Chromium only).
pdf :: Page -> PDFOptions -> Aff Unit
pdf page opts = fromEffectFnAff $ pdfImpl page opts

foreign import pdfImpl :: Page -> PDFOptions -> EffectFnAff Unit

-- =============================================================================
--                                                               // evaluation
-- =============================================================================

-- | Evaluate JavaScript in the page context.
evaluate :: Page -> String -> Aff String
evaluate page script = fromEffectFnAff $ evaluateImpl page script

foreign import evaluateImpl :: Page -> String -> EffectFnAff String

-- | Evaluate JavaScript and return a handle.
evaluateHandle :: Page -> String -> Aff ElementHandle
evaluateHandle page script = fromEffectFnAff $ evaluateHandleImpl page script

foreign import evaluateHandleImpl :: Page -> String -> EffectFnAff ElementHandle

-- =============================================================================
--                                                                 // page info
-- =============================================================================

-- | Get the current URL.
url :: Page -> Effect String
url = urlImpl

foreign import urlImpl :: Page -> Effect String

-- | Get the page title.
title :: Page -> Aff String
title = fromEffectFnAff <<< titleImpl

foreign import titleImpl :: Page -> EffectFnAff String

-- | Get the full HTML content.
content :: Page -> Aff String
content = fromEffectFnAff <<< contentImpl

foreign import contentImpl :: Page -> EffectFnAff String

-- | Set the page content.
setContent :: Page -> String -> Aff Unit
setContent page html = fromEffectFnAff $ setContentImpl page html

foreign import setContentImpl :: Page -> String -> EffectFnAff Unit

-- =============================================================================
--                                                                  // internal
-- =============================================================================

browserTypeToString :: BrowserType -> String
browserTypeToString = case _ of
  Chromium -> "chromium"
  Firefox -> "firefox"
  Webkit -> "webkit"

-- | Default launch options.
defaultLaunchOptions :: LaunchOptions
defaultLaunchOptions =
  { headless: true
  , slowMo: 0
  , timeout: 30000
  , devtools: false
  }
