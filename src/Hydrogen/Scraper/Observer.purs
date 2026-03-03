-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // scraper // observer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Observation Protocol for behavioral visual extraction.
-- |
-- | This is the HARD PART of brand scraping. Instead of parsing CSS,
-- | we observe actual behavior:
-- |
-- | 1. Load page, wait for JS execution
-- | 2. Capture initial state of all visible elements
-- | 3. Hover each interactive element, record state change
-- | 4. Click elements that respond, record state change  
-- | 5. Focus form elements, record state change
-- | 6. Scroll through page, capture scroll-triggered animations
-- | 7. Wait for auto-playing animations
-- |
-- | Total observation time: 10-20 seconds per page.
-- |
-- | ## Output
-- |
-- | All states are captured as Hydrogen atoms (OKLCH, Pixel, Transform, etc.)
-- | State transitions include timing (duration, easing, delay).
-- |
-- | ## Dependencies
-- | - Hydrogen.Playwright (browser automation)
-- | - Hydrogen.Scraper.Capture (state extraction)
-- | - Hydrogen.Scraper.Types.State (InteractionState, StateDiff)

module Hydrogen.Scraper.Observer
  ( -- * Observation
    observe
  , observeWithOptions
  , observeSafe
  , observeWithOptionsSafe
  
  -- * Options
  , ObserveOptions
  , defaultObserveOptions
  
  -- * Results
  , PageObservation
  , ElementObservation
  , ObservedTransition
  , ObserveError(..)
  , emptyPageObservation
  
  -- * Element Discovery
  , discoverInteractiveElements
  , ElementSelector
  ) where

import Prelude

import Data.Array (filter, length, range) as Array
import Data.Array as Array
import Data.Either (Either(Left, Right))
import Data.Int (floor, toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Traversable (traverse)
import Effect.Aff (Aff, attempt, delay)
import Effect.Class (liftEffect)
import Effect.Exception (Error, message)
import Hydrogen.Playwright as PW
import Hydrogen.Playwright (BrowserType(Chromium), LoadState(NetworkIdle), Page, Locator)
import Hydrogen.Scraper.Capture (CapturedState, captureElementState, captureAllElements)
import Hydrogen.Scraper.Types.State (InteractionState)
import Hydrogen.Scraper.Wire.Parse as Parse
import Data.Time.Duration (Milliseconds(Milliseconds))

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // observe options
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for page observation
type ObserveOptions =
  { -- Viewport
    viewportWidth :: Int
  , viewportHeight :: Int
  
    -- Timing
  , hoverDuration :: Int           -- ^ How long to hover (ms) to trigger transitions
  , clickWaitDuration :: Int       -- ^ How long to wait after click (ms)
  , focusWaitDuration :: Int       -- ^ How long to wait after focus (ms)
  , scrollIncrement :: Int         -- ^ Pixels to scroll per step
  , animationWaitDuration :: Int   -- ^ How long to wait for auto-animations (ms)
  , maxObservationTime :: Int      -- ^ Maximum total observation time (ms)
  
    -- Behavior
  , captureScreenshots :: Boolean  -- ^ Take element screenshots (expensive)
  , captureAnimations :: Boolean   -- ^ Extract animation data
  , scrollFullPage :: Boolean      -- ^ Scroll through entire page
  
    -- Limits
  , maxElements :: Int             -- ^ Max elements to observe (prevent runaway)
  }

-- | Default observation options (10-15 second observation)
defaultObserveOptions :: ObserveOptions
defaultObserveOptions =
  { viewportWidth: 1920
  , viewportHeight: 1080
  , hoverDuration: 300            -- 300ms hover to trigger CSS transitions
  , clickWaitDuration: 500        -- 500ms after click
  , focusWaitDuration: 200        -- 200ms after focus
  , scrollIncrement: 200          -- 200px scroll steps
  , animationWaitDuration: 3000   -- 3s for auto-playing animations
  , maxObservationTime: 20000     -- 20s max total
  , captureScreenshots: false     -- Off by default (expensive)
  , captureAnimations: true       -- On by default
  , scrollFullPage: true          -- On by default
  , maxElements: 500              -- Don't process more than 500 elements
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // results
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Selector for an element (CSS selector path)
type ElementSelector = String

-- | Observed transition between states
type ObservedTransition =
  { fromState :: InteractionState
  , toState :: InteractionState
  , before :: CapturedState
  , after :: CapturedState
  , durationMs :: Int              -- Observed duration
  , selector :: ElementSelector
  }

-- | Complete observation of a single element
type ElementObservation =
  { selector :: ElementSelector
  , tagName :: String
  , isInteractive :: Boolean
  , defaultState :: CapturedState
  , hoverState :: Maybe CapturedState
  , focusState :: Maybe CapturedState
  , activeState :: Maybe CapturedState
  , transitions :: Array ObservedTransition
  }

-- | Complete observation of a page
type PageObservation =
  { url :: String
  , title :: String
  , observationTimeMs :: Int
  , viewportWidth :: Int
  , viewportHeight :: Int
  , pageHeight :: Int              -- Total scrollable height
  , elementCount :: Int
  , interactiveCount :: Int
  , elements :: Array ElementObservation
  , scrollTriggeredElements :: Array ElementSelector  -- Elements that changed on scroll
  }

-- | Error types for observation failures
-- |
-- | These capture the different ways browser automation can fail:
-- | - BrowserLaunchFailed: Playwright couldn't start the browser (missing libs, sandbox issues)
-- | - NavigationFailed: Page load failed (network error, timeout, invalid URL)
-- | - ObservationFailed: Error during element probing
data ObserveError
  = BrowserLaunchFailed String   -- ^ Browser binary couldn't start (e.g., missing libglib-2.0.so)
  | NavigationFailed String      -- ^ Page navigation failed
  | ObservationFailed String     -- ^ Error during observation protocol

-- | Empty page observation (for error cases)
-- |
-- | Returns a valid PageObservation with zero elements, useful when
-- | browser launch fails but we want to return a valid structure.
emptyPageObservation :: String -> PageObservation
emptyPageObservation url =
  { url: url
  , title: ""
  , observationTimeMs: 0
  , viewportWidth: 0
  , viewportHeight: 0
  , pageHeight: 0
  , elementCount: 0
  , interactiveCount: 0
  , elements: []
  , scrollTriggeredElements: []
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // element discovery
-- ═══════════════════════════════════════════════════════════════════════════════

-- | JavaScript to discover all interactive elements
-- | Returns array of CSS selector paths
discoverInteractiveJS :: String
discoverInteractiveJS = """
(() => {
  const interactive = [];
  const seen = new Set();
  
  // Interactive tags
  const interactiveTags = ['A', 'BUTTON', 'INPUT', 'SELECT', 'TEXTAREA', 'DETAILS', 'SUMMARY'];
  
  // Find all potentially interactive elements
  const candidates = document.querySelectorAll('*');
  
  for (const el of candidates) {
    // Skip invisible
    const style = getComputedStyle(el);
    if (style.display === 'none' || style.visibility === 'hidden') continue;
    if (el.offsetWidth === 0 && el.offsetHeight === 0) continue;
    
    let isInteractive = false;
    
    // Check tag
    if (interactiveTags.includes(el.tagName)) {
      isInteractive = true;
    }
    
    // Check role
    const role = el.getAttribute('role');
    if (['button', 'link', 'checkbox', 'radio', 'slider', 'switch', 'tab', 'menuitem'].includes(role)) {
      isInteractive = true;
    }
    
    // Check cursor
    if (style.cursor === 'pointer') {
      isInteractive = true;
    }
    
    // Check for event listeners (heuristic: has onclick or tabindex)
    if (el.hasAttribute('onclick') || el.hasAttribute('tabindex')) {
      isInteractive = true;
    }
    
    // Check for transitions/animations on hover (via CSS)
    if (style.transition !== 'none' && style.transition !== '' && style.transition !== 'all 0s ease 0s') {
      isInteractive = true;
    }
    
    if (isInteractive) {
      // Generate unique selector
      const selector = getUniqueSelector(el);
      if (!seen.has(selector)) {
        seen.add(selector);
        interactive.push({
          selector: selector,
          tagName: el.tagName,
          hasTransition: style.transition !== 'none' && style.transition !== ''
        });
      }
    }
  }
  
  return JSON.stringify(interactive);
  
  function getUniqueSelector(el) {
    if (el.id) return '#' + CSS.escape(el.id);
    
    const path = [];
    while (el && el.nodeType === Node.ELEMENT_NODE) {
      let selector = el.tagName.toLowerCase();
      if (el.id) {
        selector = '#' + CSS.escape(el.id);
        path.unshift(selector);
        break;
      } else {
        let sibling = el;
        let nth = 1;
        while (sibling = sibling.previousElementSibling) {
          if (sibling.tagName === el.tagName) nth++;
        }
        if (nth > 1) selector += ':nth-of-type(' + nth + ')';
      }
      path.unshift(selector);
      el = el.parentElement;
    }
    return path.join(' > ');
  }
})()
"""

-- | Discovered interactive element info
type DiscoveredElement =
  { selector :: String
  , tagName :: String
  , hasTransition :: Boolean
  }

-- | Discover all interactive elements on the page
discoverInteractiveElements :: Page -> Aff (Array DiscoveredElement)
discoverInteractiveElements page = do
  resultJson <- PW.evaluate page discoverInteractiveJS
  -- Parse JSON result
  pure (parseDiscoveredElements resultJson)

-- | Parse discovered elements from JSON
-- |
-- | Uses Wire.Parse surgical extraction to parse the JSON array
-- | returned by discoverInteractiveJS.
-- |
-- | Expected format: [{"selector": "...", "tagName": "...", "hasTransition": true}, ...]
parseDiscoveredElements :: String -> Array DiscoveredElement
parseDiscoveredElements json =
  let elementJsons = Parse.extractArrayElements json
  in Array.mapMaybe parseDiscoveredElement elementJsons
  where
    -- | Parse a single discovered element from its JSON string
    parseDiscoveredElement :: String -> Maybe DiscoveredElement
    parseDiscoveredElement elementJson = do
      selector <- Parse.extractString "selector" elementJson
      tagName <- Parse.extractString "tagName" elementJson
      let hasTransition = case Parse.extractBoolean "hasTransition" elementJson of
            Just b -> b
            Nothing -> false
      Just { selector, tagName, hasTransition }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // observation protocol
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Observe a URL with default options
observe :: String -> Aff PageObservation
observe url = observeWithOptions url defaultObserveOptions

-- | Observe a URL with custom options
-- |
-- | This is the main observation protocol:
-- | 1. Load page
-- | 2. Discover interactive elements
-- | 3. Capture initial state of each
-- | 4. Probe each element (hover, focus, click)
-- | 5. Record state changes with timing
-- | 6. Scroll and detect scroll-triggered changes
observeWithOptions :: String -> ObserveOptions -> Aff PageObservation
observeWithOptions url opts = do
  -- Launch browser
  browser <- PW.launch Chromium PW.defaultLaunchOptions
  page <- PW.newPage browser
  
  -- Navigate and wait
  PW.goto page url
  PW.waitForLoadState page NetworkIdle
  
  -- Get page info
  pageTitle <- PW.title page
  pageHeightStr <- PW.evaluate page "document.documentElement.scrollHeight"
  
  -- Discover interactive elements
  discovered <- discoverInteractiveElements page
  let limitedDiscovered = Array.filter (\_ -> true) discovered  -- TODO: limit
  
  -- Capture all elements' initial state
  initialStates <- captureAllElements page
  
  -- Observe each interactive element
  observations <- traverse (observeElement page opts) limitedDiscovered
  
  -- Scroll through page and detect changes
  scrollTriggered <- if opts.scrollFullPage
    then scrollAndObserve page opts
    else pure []
  
  -- Wait for auto-playing animations
  delay (Milliseconds (Int.toNumber opts.animationWaitDuration))
  
  -- Close browser
  PW.close browser
  
  pure
    { url: url
    , title: pageTitle
    , observationTimeMs: opts.maxObservationTime  -- TODO: actual timing
    , viewportWidth: opts.viewportWidth
    , viewportHeight: opts.viewportHeight
    , pageHeight: parseIntOrZero pageHeightStr
    , elementCount: Array.length initialStates
    , interactiveCount: Array.length discovered
    , elements: observations
    , scrollTriggeredElements: scrollTriggered
    }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // safe observation (no crash)
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Safe observation with default options (returns Either instead of crashing)
-- |
-- | Use this when Playwright may not be available or browser binaries
-- | may be missing (e.g., NixOS without proper library paths).
observeSafe :: String -> Aff (Either ObserveError PageObservation)
observeSafe url = observeWithOptionsSafe url defaultObserveOptions

-- | Safe observation with custom options
-- |
-- | Wraps browser launch in `attempt` to catch failures like:
-- | - Missing shared libraries (libglib-2.0.so, etc.)
-- | - Sandbox permission errors
-- | - Browser binary not found
-- |
-- | Returns `Left ObserveError` on failure instead of throwing.
observeWithOptionsSafe :: String -> ObserveOptions -> Aff (Either ObserveError PageObservation)
observeWithOptionsSafe url opts = do
  -- Attempt to launch browser (this is where NixOS fails)
  browserResult <- attempt (PW.launch Chromium PW.defaultLaunchOptions)
  
  case browserResult of
    Left err -> 
      -- Browser launch failed (missing libs, sandbox issues, etc.)
      pure (Left (BrowserLaunchFailed (message err)))
    
    Right browser -> do
      -- Browser launched successfully, continue with observation
      pageResult <- attempt do
        page <- PW.newPage browser
        
        -- Navigate and wait
        PW.goto page url
        PW.waitForLoadState page NetworkIdle
        
        -- Get page info
        pageTitle <- PW.title page
        pageHeightStr <- PW.evaluate page "document.documentElement.scrollHeight"
        
        -- Discover interactive elements
        discovered <- discoverInteractiveElements page
        let limitedDiscovered = Array.filter (\_ -> true) discovered
        
        -- Capture all elements' initial state
        initialStates <- captureAllElements page
        
        -- Observe each interactive element
        observations <- traverse (observeElement page opts) limitedDiscovered
        
        -- Scroll through page and detect changes
        scrollTriggered <- if opts.scrollFullPage
          then scrollAndObserve page opts
          else pure []
        
        -- Wait for auto-playing animations
        delay (Milliseconds (Int.toNumber opts.animationWaitDuration))
        
        pure
          { url: url
          , title: pageTitle
          , observationTimeMs: opts.maxObservationTime
          , viewportWidth: opts.viewportWidth
          , viewportHeight: opts.viewportHeight
          , pageHeight: parseIntOrZero pageHeightStr
          , elementCount: Array.length initialStates
          , interactiveCount: Array.length discovered
          , elements: observations
          , scrollTriggeredElements: scrollTriggered
          }
      
      -- Always close the browser, even on error
      _ <- attempt (PW.close browser)
      
      case pageResult of
        Left err -> pure (Left (ObservationFailed (message err)))
        Right obs -> pure (Right obs)

-- | Observe a single element through all interaction states
observeElement :: Page -> ObserveOptions -> DiscoveredElement -> Aff ElementObservation
observeElement page opts discovered = do
  let sel = discovered.selector
  
  -- Get locator
  loc <- liftEffect $ PW.locator page sel
  
  -- Check visibility
  visible <- PW.isVisible loc
  
  if not visible
    then pure (emptyObservation discovered)
    else do
      -- Capture default state
      defaultState <- captureElementState page sel
      
      -- Hover and capture
      hoverState <- probeHover page loc opts sel
      
      -- Focus (if focusable) and capture
      focusState <- probeFocus page loc opts sel discovered.tagName
      
      -- We don't click by default (could navigate away)
      -- activeState <- probeClick page loc opts sel
      
      pure
        { selector: sel
        , tagName: discovered.tagName
        , isInteractive: true
        , defaultState: defaultState
        , hoverState: hoverState
        , focusState: focusState
        , activeState: Nothing
        , transitions: []  -- TODO: compute from state diffs
        }

-- | Probe hover state
probeHover :: Page -> Locator -> ObserveOptions -> ElementSelector -> Aff (Maybe CapturedState)
probeHover page loc opts sel = do
  -- Hover
  PW.hover loc
  
  -- Wait for transition
  delay (Milliseconds (Int.toNumber opts.hoverDuration))
  
  -- Capture state
  state <- captureElementState page sel
  
  -- Move mouse away (reset)
  _ <- PW.evaluate page "document.body.dispatchEvent(new MouseEvent('mousemove', {clientX: 0, clientY: 0}))"
  
  pure (Just state)

-- | Probe focus state (for form elements)
probeFocus :: Page -> Locator -> ObserveOptions -> ElementSelector -> String -> Aff (Maybe CapturedState)
probeFocus page loc opts sel tagName = do
  -- Only focus form elements
  if isFocusable tagName
    then do
      PW.focus loc
      delay (Milliseconds (Int.toNumber opts.focusWaitDuration))
      state <- captureElementState page sel
      PW.blur loc
      pure (Just state)
    else pure Nothing
  where
    isFocusable :: String -> Boolean
    isFocusable t = t == "INPUT" || t == "TEXTAREA" || t == "SELECT" || t == "BUTTON" || t == "A"

-- | Scroll through page and detect elements that change
scrollAndObserve :: Page -> ObserveOptions -> Aff (Array ElementSelector)
scrollAndObserve page opts = do
  -- Get page height
  heightStr <- PW.evaluate page "document.documentElement.scrollHeight"
  let totalHeight = parseIntOrZero heightStr
  let steps = totalHeight / opts.scrollIncrement
  
  -- TODO: For each scroll position, check for elements entering viewport
  -- and capture any scroll-triggered animations
  
  -- For now, just scroll through
  _ <- traverse (scrollToPosition page opts.scrollIncrement) (Array.range 0 (min steps 50))
  
  -- Scroll back to top
  _ <- PW.evaluate page "window.scrollTo(0, 0)"
  
  pure []  -- TODO: return elements that changed

-- | Scroll to a position
scrollToPosition :: Page -> Int -> Int -> Aff Unit
scrollToPosition page increment step = do
  let y = step * increment
  _ <- PW.evaluate page ("window.scrollTo(0, " <> show y <> ")")
  delay (Milliseconds 100.0)  -- Brief pause to let animations trigger

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty observation for invisible elements
emptyObservation :: DiscoveredElement -> ElementObservation
emptyObservation discovered =
  { selector: discovered.selector
  , tagName: discovered.tagName
  , isInteractive: false
  , defaultState: emptyCapturedState
  , hoverState: Nothing
  , focusState: Nothing
  , activeState: Nothing
  , transitions: []
  }

-- | Empty captured state placeholder
-- |
-- | Contains all fields for the complete CapturedState type with default values.
emptyCapturedState :: CapturedState
emptyCapturedState =
  { -- Identity
    tagName: ""
  , elementId: ""
  , className: ""
  , selector: ""
  
  -- DOM Tree Structure
  , index: 0
  , parentIndex: -1
  , childIndices: []
  , depth: 0
  
  -- Accessibility
  , role: ""
  , ariaLabel: ""
  , ariaDescribedBy: ""
  , tabIndex: -1
  
  -- Content
  , textContent: ""
  
  -- Geometry
  , x: 0.0
  , y: 0.0
  , width: 0.0
  , height: 0.0
  , boundingBox: Nothing
  
  -- Colors
  , backgroundColor: Nothing
  , color: Nothing
  , borderColor: Nothing
  
  -- Typography
  , fontFamily: "sans-serif"
  , fontSize: 16.0
  , fontWeight: 400
  , lineHeight: 19.2
  , letterSpacing: 0.0
  , textAlign: "start"
  , textDecoration: "none"
  , textTransform: "none"
  
  -- Spacing - Margins
  , marginTop: 0.0
  , marginRight: 0.0
  , marginBottom: 0.0
  , marginLeft: 0.0
  
  -- Spacing - Paddings
  , paddingTop: 0.0
  , paddingRight: 0.0
  , paddingBottom: 0.0
  , paddingLeft: 0.0
  
  -- Borders - Widths
  , borderTopWidth: 0.0
  , borderRightWidth: 0.0
  , borderBottomWidth: 0.0
  , borderLeftWidth: 0.0
  
  -- Borders - Radii
  , borderTopLeftRadius: 0.0
  , borderTopRightRadius: 0.0
  , borderBottomRightRadius: 0.0
  , borderBottomLeftRadius: 0.0
  
  -- Borders - Styles
  , borderTopStyle: "none"
  , borderRightStyle: "none"
  , borderBottomStyle: "none"
  , borderLeftStyle: "none"
  
  -- Elevation
  , boxShadow: Nothing
  , zIndex: 0
  
  -- Transform
  , transform: Nothing
  
  -- Display properties
  , opacity: 1.0
  , visibility: "visible"
  , display: "block"
  , overflow: "visible"
  , position: "static"
  
  -- Flex/Grid Layout
  , flexDirection: "row"
  , justifyContent: "normal"
  , alignItems: "normal"
  , gap: 0.0
  
  -- Interactivity
  , cursor: "auto"
  , pointerEvents: "auto"
  
  -- Transition info
  , transitionDuration: "0s"
  , transitionTimingFunction: "ease"
  , transitionDelay: "0s"
  , transitionProperty: "all"
  }

-- | Parse int or return 0
-- |
-- | Uses Wire.Parse to extract a number from a JSON string value,
-- | then converts to Int. Returns 0 on parse failure.
parseIntOrZero :: String -> Int
parseIntOrZero str = 
  case Parse.parseJSONNumber str of
    Just n -> Int.floor n
    Nothing -> 0

-- | Minimum of two ints
min :: Int -> Int -> Int
min a b = if a < b then a else b
