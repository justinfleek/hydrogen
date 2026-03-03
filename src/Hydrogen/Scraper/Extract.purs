-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // scraper // extract
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Playwright-based extraction for 1:1 visual parity.
-- |
-- | This is the main entry point for scraping. It orchestrates:
-- | 1. Observer - 10-20 second behavioral observation protocol
-- | 2. Capture - State extraction with computed styles
-- | 3. Transition - Timing and easing detection
-- | 4. Animation - Lottie, CSS keyframes, scroll-linked extraction
-- |
-- | The output is a ScrapedPage with ExtractedElements containing
-- | Hydrogen Schema atoms - no strings, no CSS, fully typed.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | result <- scrapeUrlFull "https://example.com" defaultScrapeOptions
-- | -- result.tree contains the full element tree with Schema atoms
-- | -- result.observations contains interaction state transitions
-- | -- result.animations contains detected animations
-- | ```

module Hydrogen.Scraper.Extract
  ( -- * Full Extraction (recommended)
    scrapeUrlFull
  , scrapeUrlFullSafe
  , FullScrapeResult
  , ScrapeError(..)
  , emptyFullScrapeResult
  
  -- * Simple Extraction (legacy)
  , scrapeUrl
  , scrapeUrlSafe
  , screenshotUrl
  
  -- * Options
  , ScrapeOptions
  , defaultScrapeOptions
  
  -- * Schema Wiring (Scraper → Schema atoms)
  , capturedToExtracted
  , capturedTransformToSchema
  , capturedColorToOKLCHA
  , capturedColorToOKLCH
  , easingFunctionToSchema
  
  -- * Types (re-exported for consumer convenience)
  , ScrapeResult
  , module ReExportTransition
  , module ReExportTypes
  ) where

import Prelude

import Data.Array (filter, index, length, mapMaybe, range, zip, zipWith) as Array
import Data.Either (Either(Left, Right))
import Data.Int (floor, toNumber) as Int
import Data.Map (Map)
import Data.Map (fromFoldable, lookup) as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (fromString) as Number
import Data.Tuple (Tuple(Tuple))
import Effect.Aff (Aff, attempt)
import Effect.Exception (message)
import Hydrogen.Playwright as PW
import Hydrogen.Playwright (BrowserType(Chromium), LoadState(NetworkIdle, Load))
import Hydrogen.Schema.Color.Alpha (OKLCHA, oklcha)
import Hydrogen.Schema.Color.OKLCH (OKLCH, oklch)
import Hydrogen.Schema.Dimension.Device (Pixel, px)
import Hydrogen.Schema.Color.Conversion.Modern (oklchToRgb) as ColorConv
import Hydrogen.Schema.Color.RGB (RGBA, rgba, toRecord) as RGB
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow, boxShadow, layered, noShadow) as Shadow
import Hydrogen.Schema.Elevation.ZIndex (ZIndex)
import Hydrogen.Schema.Elevation.ZIndex (auto, z) as ZIndex
import Hydrogen.Schema.Geometry.Angle (degrees) as Angle
import Hydrogen.Schema.Geometry.Radius (Corners)
import Hydrogen.Schema.Geometry.Radius (Radius, corners, px) as Radius
import Hydrogen.Schema.Geometry.Transform 
  ( Transform2D
  , transform2D
  , scale
  , scaleXY
  , translate
  , rotate
  , originCenter
  ) as SchemaTransform
import Hydrogen.Schema.Temporal.Easing (Easing) as SchemaEasing
import Hydrogen.Schema.Temporal.Easing 
  ( linearEasing
  , cubicEasing
  , stepsEasing
  , springEasing
  ) as EasingCtors
import Hydrogen.Schema.Temporal.CubicBezierEasing (cubicBezierFromNumbers) as CubicBezier
import Hydrogen.Schema.Temporal.StepEasing (steps, StepPosition(JumpEnd)) as StepEasing
import Hydrogen.Schema.Temporal.SpringConfig (springConfig) as SpringConfig
import Hydrogen.Schema.Temporal.Spring (mass, stiffness, damping) as Spring
import Hydrogen.Schema.Typography.FontFamily (FontFamily, fontFamily)
import Hydrogen.Schema.Typography.FontSize (FontSize, fontSize) as FontSize
import Hydrogen.Schema.Typography.FontWeight (FontWeight, fontWeight) as FontWeight
import Hydrogen.Schema.Typography.LineHeight (LineHeight, lineHeight) as LineHeight
import Hydrogen.Schema.Typography.LetterSpacing (LetterSpacing, letterSpacing) as LetterSpacing
import Hydrogen.Scraper.Animation (DetectedAnimation, EasingFunction, detectAnimations)
import Hydrogen.Scraper.Animation 
  ( EasingFunction(Linear, Ease, EaseIn, EaseOut, EaseInOut, CubicBezier, Steps, Spring)
  ) as Anim
import Hydrogen.Scraper.Capture (CapturedState, CapturedColor, CapturedTransform, CapturedShadow, captureAllElements)
import Hydrogen.Scraper.Observer 
  ( PageObservation
  , ObserveOptions
  , ObserveError(..)
  , defaultObserveOptions
  , observeWithOptions
  , observeWithOptionsSafe
  , emptyPageObservation
  )
import Hydrogen.Scraper.Transition (ObservedTransition, TransitionConfig, detectTransitions) as ReExportTransition
import Hydrogen.Scraper.Transition (TransitionConfig, detectTransitions)
import Hydrogen.Scraper.Types 
  ( ScrapedPage
  , ExtractedElement(..)
  , ExtractedElementData
  , emptyExtractedElementData
  , emptyScrapedPage
  ) as ReExportTypes
import Hydrogen.Scraper.Types 
  ( ScrapedPage
  , ExtractedElement(..)
  , ExtractedElementData
  , emptyExtractedElementData
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // scrape options
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Options for scraping
type ScrapeOptions =
  { viewportWidth :: Int
  , viewportHeight :: Int
  , screenshotPath :: Maybe String
  , waitForNetworkIdle :: Boolean
  , timeout :: Int  -- ^ milliseconds
  , observeInteractions :: Boolean  -- ^ Run full observation protocol
  , captureAnimations :: Boolean    -- ^ Extract Lottie/CSS animations
  }

-- | Default scrape options (1920x1080, wait for network idle)
defaultScrapeOptions :: ScrapeOptions
defaultScrapeOptions =
  { viewportWidth: 1920
  , viewportHeight: 1080
  , screenshotPath: Nothing
  , waitForNetworkIdle: true
  , timeout: 30000
  , observeInteractions: true
  , captureAnimations: true
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // scrape result
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Simple result of a scrape operation (legacy)
type ScrapeResult =
  { url :: String
  , title :: String
  , screenshotPath :: Maybe String
  , viewportWidth :: Pixel
  , viewportHeight :: Pixel
  , rawHtml :: String
  , elementCount :: Int
  }

-- | Full scrape result with observation data, element tree, animations
-- |
-- | This is the recommended output type for production use.
type FullScrapeResult =
  { -- Page metadata
    page :: ScrapedPage
    
  -- Observation data (from Observer)
  , observation :: PageObservation
  
  -- Detected transitions (from Transition)
  , transitions :: Array { selector :: String, config :: Array TransitionConfig }
  
  -- Detected animations (from Animation)
  , animations :: Array DetectedAnimation
  
  -- Raw captured states for all elements
  , capturedStates :: Array CapturedState
  
  -- Summary stats
  , elementCount :: Int
  }

-- | Error types for scraping failures
-- |
-- | Wraps the underlying ObserveError from the observer module
-- | and adds scrape-specific failure modes.
data ScrapeError
  = ScrapeObserveError ObserveError   -- ^ Error from observation protocol
  | ScrapeBrowserError String         -- ^ Browser automation error during extraction

-- | Empty full scrape result (for error recovery)
-- |
-- | Returns a valid FullScrapeResult with zero elements.
emptyFullScrapeResult :: String -> FullScrapeResult
emptyFullScrapeResult url =
  { page:
      { url: url
      , title: ""
      , viewportWidth: px 0.0
      , viewportHeight: px 0.0
      , tree: ExtractedElement { element: emptyExtractedElementData, children: [] }
      , layers: []
      , screenshotPath: Nothing
      }
  , observation: emptyPageObservation url
  , transitions: []
  , animations: []
  , capturedStates: []
  , elementCount: 0
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // full extraction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scrape a URL with full observation protocol
-- |
-- | This is the main entry point. It:
-- | 1. Navigates to the URL
-- | 2. Runs the 10-20 second observation protocol (hover, click, focus, scroll)
-- | 3. Captures all element states
-- | 4. Detects transitions and animations
-- | 5. Converts everything to Hydrogen Schema atoms
-- |
-- | Total scrape time: 10-30 seconds depending on page complexity.
scrapeUrlFull :: String -> ScrapeOptions -> Aff FullScrapeResult
scrapeUrlFull url opts = do
  -- Convert scrape options to observe options
  let observeOpts = toObserveOptions opts
  
  -- Run the full observation protocol
  -- This navigates, probes interactions, and captures everything
  observation <- observeWithOptions url observeOpts
  
  -- Launch browser again for additional extraction
  -- (Observer closes browser when done)
  browser <- PW.launch Chromium PW.defaultLaunchOptions
  page <- PW.newPage browser
  PW.goto page url
  PW.waitForLoadState page NetworkIdle
  
  -- Capture all element states
  capturedStates <- captureAllElements page
  
  -- Detect transitions
  transitions <- detectTransitions page
  
  -- Detect animations
  animations <- if opts.captureAnimations
    then detectAnimations page
    else pure []
  
  -- Screenshot if requested
  case opts.screenshotPath of
    Just path -> PW.screenshot page 
      { path: path, fullPage: true, type: "png", quality: 100 }
    Nothing -> pure unit
  
  -- Get page title
  pageTitle <- PW.title page
  
  PW.close browser
  
  -- Build the element tree from captured states
  let elementTree = buildElementTree capturedStates
      elementCount = Array.length capturedStates
  
  -- Build the ScrapedPage
  let scrapedPage = 
        { url: url
        , title: pageTitle
        , viewportWidth: px (Int.toNumber opts.viewportWidth)
        , viewportHeight: px (Int.toNumber opts.viewportHeight)
        , tree: elementTree
        , layers: []  -- TODO: group by z-index
        , screenshotPath: opts.screenshotPath
        }
  
  pure
    { page: scrapedPage
    , observation: observation
    , transitions: transitions
    , animations: animations
    , capturedStates: capturedStates
    , elementCount: elementCount
    }

-- | Convert ScrapeOptions to ObserveOptions
toObserveOptions :: ScrapeOptions -> ObserveOptions
toObserveOptions opts = defaultObserveOptions
  { viewportWidth = opts.viewportWidth
  , viewportHeight = opts.viewportHeight
  , maxObservationTime = opts.timeout
  , captureAnimations = opts.captureAnimations
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // safe full extraction
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Safe scrape with full observation protocol
-- |
-- | Returns `Either ScrapeError FullScrapeResult` instead of crashing.
-- | Use this when Playwright may not be available (e.g., NixOS, CI without browsers).
-- |
-- | On failure, returns a descriptive error:
-- | - `ScrapeObserveError (BrowserLaunchFailed msg)` - Browser binary couldn't start
-- | - `ScrapeObserveError (NavigationFailed msg)` - Page load failed
-- | - `ScrapeBrowserError msg` - Error during extraction phase
scrapeUrlFullSafe :: String -> ScrapeOptions -> Aff (Either ScrapeError FullScrapeResult)
scrapeUrlFullSafe url opts = do
  -- Convert scrape options to observe options
  let observeOpts = toObserveOptions opts
  
  -- Run the safe observation protocol (catches browser launch failures)
  observeResult <- observeWithOptionsSafe url observeOpts
  
  case observeResult of
    Left obsErr -> 
      -- Observation failed (browser launch, navigation, etc.)
      pure (Left (ScrapeObserveError obsErr))
    
    Right observation -> do
      -- Observation succeeded, now do additional extraction
      extractResult <- attempt do
        -- Launch browser again for additional extraction
        browser <- PW.launch Chromium PW.defaultLaunchOptions
        page <- PW.newPage browser
        PW.goto page url
        PW.waitForLoadState page NetworkIdle
        
        -- Capture all element states
        capturedStates <- captureAllElements page
        
        -- Detect transitions
        transitions <- detectTransitions page
        
        -- Detect animations
        animations <- if opts.captureAnimations
          then detectAnimations page
          else pure []
        
        -- Screenshot if requested
        case opts.screenshotPath of
          Just path -> PW.screenshot page 
            { path: path, fullPage: true, type: "png", quality: 100 }
          Nothing -> pure unit
        
        -- Get page title
        pageTitle <- PW.title page
        
        PW.close browser
        
        -- Build the element tree from captured states
        let elementTree = buildElementTree capturedStates
            elementCount = Array.length capturedStates
        
        -- Build the ScrapedPage
        let scrapedPage = 
              { url: url
              , title: pageTitle
              , viewportWidth: px (Int.toNumber opts.viewportWidth)
              , viewportHeight: px (Int.toNumber opts.viewportHeight)
              , tree: elementTree
              , layers: []
              , screenshotPath: opts.screenshotPath
              }
        
        pure
          { page: scrapedPage
          , observation: observation
          , transitions: transitions
          , animations: animations
          , capturedStates: capturedStates
          , elementCount: elementCount
          }
      
      case extractResult of
        Left err -> pure (Left (ScrapeBrowserError (message err)))
        Right result -> pure (Right result)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // element tree building
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Build element tree from captured states
-- |
-- | Reconstructs the DOM tree structure using parent/child indices.
-- | Each CapturedState has `index`, `parentIndex`, and `childIndices`.
-- | We build the tree bottom-up, then find the root.
buildElementTree :: Array CapturedState -> ExtractedElement
buildElementTree states =
  let
    -- First pass: convert all states to ExtractedElement (without children)
    flatElements = map capturedToExtractedLeaf states
    
    -- Build index map
    indexedElements = Array.zip (Array.range 0 (Array.length states - 1)) flatElements
    elementMap = Map.fromFoldable indexedElements
    
    -- Second pass: attach children to parents
    attachChildren :: ExtractedElement -> CapturedState -> ExtractedElement
    attachChildren (ExtractedElement el) captured =
      let childElements = Array.mapMaybe (\idx -> Map.lookup idx elementMap) captured.childIndices
      in ExtractedElement (el { children = childElements })
    
    -- Build elements with children
    elementsWithChildren = Array.zipWith attachChildren flatElements states
    
    -- Pair elements with their states to find roots
    elementsWithStates = Array.zip elementsWithChildren states
    
    -- Find root elements (those with parentIndex == -1)
    rootElementsWithStates = Array.filter (\(Tuple _ state) -> state.parentIndex == (-1)) elementsWithStates
    rootElements = map (\(Tuple el _) -> el) rootElementsWithStates
  in
    -- Return a synthetic root containing all top-level elements
    ExtractedElement
      { element: rootElementData
      , children: rootElements
      }
  where
    rootElementData :: ExtractedElementData
    rootElementData = emptyExtractedElementData
      { tagName = "DOCUMENT"
      , elementId = "root"
      , className = ""
      }

-- | Convert CapturedState to ExtractedElement (leaf - children added later)
capturedToExtractedLeaf :: CapturedState -> ExtractedElement
capturedToExtractedLeaf captured = ExtractedElement
  { element: elementData
  , children: []  -- Populated by buildElementTree
  }
  where
    elementData :: ExtractedElementData
    elementData = emptyExtractedElementData
      { -- Identity
        tagName = captured.tagName
      , elementId = captured.elementId
      , className = captured.className
      
      -- Geometry
      , x = px captured.x
      , y = px captured.y
      , width = px captured.width
      , height = px captured.height
      
      -- Colors converted to OKLCH Schema atoms
      , colors =
          { background: capturedColorToOKLCH captured.backgroundColor
          , foreground: capturedColorToOKLCH captured.color
          , border: capturedColorToOKLCH captured.borderColor
          }
      
      -- Typography
      , typography = 
          { family: fontFamily captured.fontFamily
          , size: fontSizeFromPx captured.fontSize
          , weight: fontWeightFromInt captured.fontWeight
          , lineHeight: lineHeightFromPx captured.lineHeight captured.fontSize
          , letterSpacing: letterSpacingFromPx captured.letterSpacing captured.fontSize
          }
      
      -- Spacing
      , spacing =
          { marginTop: px captured.marginTop
          , marginRight: px captured.marginRight
          , marginBottom: px captured.marginBottom
          , marginLeft: px captured.marginLeft
          , paddingTop: px captured.paddingTop
          , paddingRight: px captured.paddingRight
          , paddingBottom: px captured.paddingBottom
          , paddingLeft: px captured.paddingLeft
          }
      
      -- Elevation
      , elevation =
          { shadow: capturedShadowToSchema captured.boxShadow
          , zIndex: zIndexFromInt captured.zIndex
          }
      
      -- Border
      , border =
          { topWidth: px captured.borderTopWidth
          , rightWidth: px captured.borderRightWidth
          , bottomWidth: px captured.borderBottomWidth
          , leftWidth: px captured.borderLeftWidth
          , corners: cornersFromCapture 
              captured.borderTopLeftRadius
              captured.borderTopRightRadius
              captured.borderBottomRightRadius
              captured.borderBottomLeftRadius
          }
      }

-- | Convert CapturedState to ExtractedElement (legacy - delegates to leaf version)
capturedToExtracted :: CapturedState -> ExtractedElement
capturedToExtracted = capturedToExtractedLeaf

-- | Convert CapturedColor to OKLCHA Schema atom (with alpha)
-- |
-- | CapturedColor has { l, c, h, a } where:
-- | - l: Lightness (0.0-1.0)
-- | - c: Chroma (0.0-0.4 typical)
-- | - h: Hue as Number (degrees 0-360)
-- | - a: Alpha (0.0-1.0)
-- |
-- | OKLCHA expects h as Int and a as Number (0.0-1.0).
capturedColorToOKLCHA :: Maybe CapturedColor -> Maybe OKLCHA
capturedColorToOKLCHA maybeColor = case maybeColor of
  Nothing -> Nothing
  Just c -> 
    -- oklcha takes l, c, h, a all as Numbers
    Just (oklcha c.l c.c c.h c.a)

-- | Convert CapturedColor to OKLCH Schema atom (opaque, drops alpha)
-- |
-- | For cases where alpha is not needed. Uses oklch which expects
-- | hue as Int (0-359).
capturedColorToOKLCH :: Maybe CapturedColor -> Maybe OKLCH
capturedColorToOKLCH maybeColor = case maybeColor of
  Nothing -> Nothing
  Just c -> 
    -- Convert hue from Number to Int (round to nearest degree)
    let hueInt = Int.floor c.h
    in Just (oklch c.l c.c hueInt)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // schema conversion helpers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert font size from pixels to FontSize Schema atom
-- |
-- | FontSize.fontSize takes a Number representing pixels.
fontSizeFromPx :: Number -> FontSize.FontSize
fontSizeFromPx n = FontSize.fontSize n

-- | Convert font weight from Int to FontWeight Schema atom
-- |
-- | FontWeight.fontWeight takes an Int (1-1000, typically 100-900).
fontWeightFromInt :: Int -> FontWeight.FontWeight
fontWeightFromInt n = FontWeight.fontWeight n

-- | Convert line height from pixels to ratio-based LineHeight Schema atom
-- |
-- | CSS computed lineHeight is in pixels. We convert to a ratio by dividing
-- | by the font size. LineHeight.lineHeight takes a unitless ratio (e.g., 1.5).
-- | If fontSize is 0 or negative, defaults to 1.5 (normal line height).
lineHeightFromPx :: Number -> Number -> LineHeight.LineHeight
lineHeightFromPx lineHeightPx fontSizePx = 
  let ratio = if fontSizePx > 0.0 
              then lineHeightPx / fontSizePx 
              else 1.5
  in LineHeight.lineHeight ratio

-- | Convert letter spacing from pixels to per-mille LetterSpacing Schema atom
-- |
-- | CSS computed letterSpacing is in pixels. We convert to per-mille (thousandths
-- | of an em) by: (letterSpacing_px / fontSize_px) * 1000.
-- | LetterSpacing.letterSpacing takes an Int in per-mille units.
-- | If fontSize is 0 or negative, defaults to 0 (normal spacing).
letterSpacingFromPx :: Number -> Number -> LetterSpacing.LetterSpacing
letterSpacingFromPx letterSpacingPx fontSizePx =
  let perMille = if fontSizePx > 0.0 
                 then (letterSpacingPx / fontSizePx) * 1000.0
                 else 0.0
  in LetterSpacing.letterSpacing (Int.floor perMille)

-- | Convert z-index from Int to ZIndex Schema atom
zIndexFromInt :: Int -> ZIndex
zIndexFromInt n = ZIndex.z n

-- | Convert captured shadow to LayeredShadow Schema atom
-- |
-- | Converts CapturedShadow's OKLCH color to RGBA for BoxShadow,
-- | preserving alpha channel. Returns noShadow if no shadow captured.
capturedShadowToSchema :: Maybe CapturedShadow -> Shadow.LayeredShadow
capturedShadowToSchema Nothing = Shadow.noShadow
capturedShadowToSchema (Just shadow) =
  let
    -- Convert captured OKLCH color to OKLCH Schema type
    capturedOklch = oklch shadow.color.l shadow.color.c (Int.floor shadow.color.h)
    
    -- Convert OKLCH to RGB
    rgb = ColorConv.oklchToRgb capturedOklch
    rgbRec = RGB.toRecord rgb
    
    -- Convert alpha from 0.0-1.0 to 0-100 percentage
    alphaPercent = Int.floor (shadow.color.a * 100.0)
    
    -- Build RGBA with alpha
    shadowColor = RGB.rgba rgbRec.r rgbRec.g rgbRec.b alphaPercent
    
    -- Build BoxShadow
    box = Shadow.boxShadow
      { offsetX: shadow.offsetX
      , offsetY: shadow.offsetY
      , blur: shadow.blurRadius
      , spread: shadow.spreadRadius
      , color: shadowColor
      , inset: shadow.inset
      }
  in Shadow.layered [ box ]

-- | Build Corners Schema atom from border radii (in pixels)
cornersFromCapture :: Number -> Number -> Number -> Number -> Corners
cornersFromCapture tl tr br bl = 
  Radius.corners
    (Radius.px tl)
    (Radius.px tr)
    (Radius.px br)
    (Radius.px bl)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // screenshot
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Take a screenshot of a URL
screenshotUrl :: String -> String -> Aff Unit
screenshotUrl url path = do
  browser <- PW.launch Chromium PW.defaultLaunchOptions
  page <- PW.newPage browser
  PW.goto page url
  PW.waitForLoadState page NetworkIdle
  PW.screenshot page { path: path, fullPage: true, type: "png", quality: 100 }
  PW.close browser

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // simple scrape
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Scrape a URL and extract basic info (legacy API)
-- |
-- | For full extraction with observation protocol, use `scrapeUrlFull`.
scrapeUrl :: String -> ScrapeOptions -> Aff ScrapeResult
scrapeUrl url opts = do
  browser <- PW.launch Chromium PW.defaultLaunchOptions
  page <- PW.newPage browser
  
  -- Navigate
  PW.goto page url
  
  -- Wait for load
  if opts.waitForNetworkIdle
    then PW.waitForLoadState page NetworkIdle
    else PW.waitForLoadState page Load
  
  -- Screenshot if requested
  case opts.screenshotPath of
    Just path -> PW.screenshot page 
      { path: path, fullPage: true, type: "png", quality: 100 }
    Nothing -> pure unit
  
  -- Get basic info
  pageTitle <- PW.title page
  html <- PW.content page
  
  -- Count elements via JS
  countStr <- PW.evaluate page "document.querySelectorAll('*').length"
  
  PW.close browser
  
  pure
    { url: url
    , title: pageTitle
    , screenshotPath: opts.screenshotPath
    , viewportWidth: px (Int.toNumber opts.viewportWidth)
    , viewportHeight: px (Int.toNumber opts.viewportHeight)
    , rawHtml: html
    , elementCount: parseCount countStr
    }

-- | Safe version of scrapeUrl (returns Either instead of crashing)
-- |
-- | Use when Playwright may not be available.
scrapeUrlSafe :: String -> ScrapeOptions -> Aff (Either ScrapeError ScrapeResult)
scrapeUrlSafe url opts = do
  result <- attempt do
    browser <- PW.launch Chromium PW.defaultLaunchOptions
    page <- PW.newPage browser
    
    -- Navigate
    PW.goto page url
    
    -- Wait for load
    if opts.waitForNetworkIdle
      then PW.waitForLoadState page NetworkIdle
      else PW.waitForLoadState page Load
    
    -- Screenshot if requested
    case opts.screenshotPath of
      Just path -> PW.screenshot page 
        { path: path, fullPage: true, type: "png", quality: 100 }
      Nothing -> pure unit
    
    -- Get basic info
    pageTitle <- PW.title page
    html <- PW.content page
    
    -- Count elements via JS
    countStr <- PW.evaluate page "document.querySelectorAll('*').length"
    
    PW.close browser
    
    pure
      { url: url
      , title: pageTitle
      , screenshotPath: opts.screenshotPath
      , viewportWidth: px (Int.toNumber opts.viewportWidth)
      , viewportHeight: px (Int.toNumber opts.viewportHeight)
      , rawHtml: html
      , elementCount: parseCount countStr
      }
  
  case result of
    Left err -> pure (Left (ScrapeBrowserError (message err)))
    Right r -> pure (Right r)

-- | Parse count from JS result
-- |
-- | JavaScript returns a string representation of the number.
parseCount :: String -> Int
parseCount str = case Number.fromString str of
  Just n -> Int.floor n
  Nothing -> 0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // schema wiring: transform
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert CapturedTransform to Schema Transform2D
-- |
-- | CapturedTransform stores the CSS matrix components (a, b, c, d, e, f).
-- | We decompose this into Scale, Translate, Rotate, Skew for Schema.
-- |
-- | CSS matrix: [a c e]   Scale: [sx  0]   Rotate: [cos -sin]   Skew: [1  tan(ax)]
-- |             [b d f]          [0  sy]           [sin  cos]         [tan(ay) 1]
-- |
-- | Decomposition (assuming no skew for simplicity):
-- |   scaleX = sqrt(a² + b²)
-- |   scaleY = sqrt(c² + d²)  
-- |   rotation = atan2(b, a)
-- |   translateX = e
-- |   translateY = f
capturedTransformToSchema :: CapturedTransform -> SchemaTransform.Transform2D
capturedTransformToSchema ct =
  let
    -- Decompose 2D matrix into components
    -- a = scaleX * cos(rotation), b = scaleX * sin(rotation)
    -- c = -scaleY * sin(rotation), d = scaleY * cos(rotation)
    scaleX = sqrt (ct.a * ct.a + ct.b * ct.b)
    scaleY = sqrt (ct.c * ct.c + ct.d * ct.d)
    
    -- Rotation in degrees
    rotationRad = atan2Impl ct.b ct.a
    rotationDeg = rotationRad * 180.0 / 3.14159265358979
    
    -- Detect sign of scaleY (if matrix is mirrored)
    -- det = a*d - b*c, negative means Y is flipped
    det = ct.a * ct.d - ct.b * ct.c
    scaleYSigned = if det < 0.0 then negate scaleY else scaleY
    
    -- Build Schema atoms
    schemaScale = if scaleX == scaleYSigned
      then Just (SchemaTransform.scale scaleX)
      else Just (SchemaTransform.scaleXY scaleX scaleYSigned)
    
    schemaTranslate = if ct.e == 0.0 && ct.f == 0.0
      then Nothing
      else Just (SchemaTransform.translate ct.e ct.f)
    
    schemaRotate = if rotationDeg == 0.0
      then Nothing
      else Just (SchemaTransform.rotate (Angle.degrees rotationDeg))
    
    -- Skew detection would require more complex decomposition
    -- For now, we don't extract skew from matrix
    schemaSkew = Nothing
    
  in SchemaTransform.transform2D 
       schemaTranslate 
       schemaRotate 
       schemaScale 
       schemaSkew 
       SchemaTransform.originCenter

-- | Pure atan2 implementation (no FFI)
-- |
-- | atan2(y, x) returns angle in radians from -π to π
atan2Impl :: Number -> Number -> Number
atan2Impl y x =
  let 
    -- Polynomial approximation of atan
    atanApprox :: Number -> Number
    atanApprox z = z / (1.0 + 0.28 * z * z)
  in
    if x > 0.0 
      then atanApprox (y / x)
    else if x < 0.0 && y >= 0.0 
      then atanApprox (y / x) + 3.14159265358979
    else if x < 0.0 && y < 0.0 
      then atanApprox (y / x) - 3.14159265358979
    else if x == 0.0 && y > 0.0 
      then 1.5707963267948966  -- π/2
    else if x == 0.0 && y < 0.0 
      then (-1.5707963267948966)
    else 0.0

-- | Pure sqrt implementation using Newton's method
-- |
-- | Converges quickly for positive numbers
sqrt :: Number -> Number
sqrt n
  | n < 0.0 = 0.0
  | n == 0.0 = 0.0
  | otherwise = newtonSqrt n (n / 2.0) 10
  where
    newtonSqrt :: Number -> Number -> Int -> Number
    newtonSqrt _ guess 0 = guess
    newtonSqrt val guess iter =
      let nextGuess = (guess + val / guess) / 2.0
      in newtonSqrt val nextGuess (iter - 1)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // schema wiring: easing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert Animation EasingFunction to Schema Easing
-- |
-- | Maps the Scraper's EasingFunction (extracted from CSS) to
-- | Hydrogen Schema's unified Easing type.
easingFunctionToSchema :: EasingFunction -> SchemaEasing.Easing
easingFunctionToSchema ef = case ef of
  Anim.Linear -> 
    EasingCtors.linearEasing
  
  Anim.Ease -> 
    EasingCtors.cubicEasing (CubicBezier.cubicBezierFromNumbers 0.25 0.1 0.25 1.0)
  
  Anim.EaseIn -> 
    EasingCtors.cubicEasing (CubicBezier.cubicBezierFromNumbers 0.42 0.0 1.0 1.0)
  
  Anim.EaseOut -> 
    EasingCtors.cubicEasing (CubicBezier.cubicBezierFromNumbers 0.0 0.0 0.58 1.0)
  
  Anim.EaseInOut -> 
    EasingCtors.cubicEasing (CubicBezier.cubicBezierFromNumbers 0.42 0.0 0.58 1.0)
  
  Anim.CubicBezier x1 y1 x2 y2 -> 
    EasingCtors.cubicEasing (CubicBezier.cubicBezierFromNumbers x1 y1 x2 y2)
  
  Anim.Steps n _jumpTerm -> 
    -- Convert Int to bounded Steps, use JumpEnd as default
    stepsToEasing n
  
  Anim.Spring massVal stiffnessVal dampingVal -> 
    EasingCtors.springEasing 
      (SpringConfig.springConfig 
        (Spring.mass massVal) 
        (Spring.stiffness stiffnessVal) 
        (Spring.damping dampingVal))

-- | Helper to convert step count to Easing
-- |
-- | Uses Schema's steps constructor which clamps to minimum of 1
stepsToEasing :: Int -> SchemaEasing.Easing
stepsToEasing n = 
  let stepsVal = StepEasing.steps n
  in EasingCtors.stepsEasing stepsVal StepEasing.JumpEnd

-- ═══════════════════════════════════════════════════════════════════════════════
--                                              // schema wiring: interaction state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | InteractionState → Schema mapping documentation
-- |
-- | The Scraper's InteractionState (CSS pseudo-classes) maps to Schema's
-- | Gestural module concepts as follows:
-- |
-- | ```
-- | InteractionState    │ Schema Module              │ Concept
-- | ────────────────────┼────────────────────────────┼───────────────────
-- | Default             │ -                          │ Rest state (no gesture)
-- | Hover               │ Gestural.Hover.HoverPhase  │ HoverActive
-- | Focus               │ Gestural.Focus.FocusState  │ hasFocus = true
-- | FocusVisible        │ Gestural.Focus.FocusOrigin │ FocusKeyboard
-- | FocusWithin         │ Gestural.Focus.FocusState  │ focusWithin = true
-- | Active              │ Gestural.Pointer           │ Pressed/down state
-- | Visited             │ -                          │ Link state (browser-only)
-- | Disabled            │ -                          │ Disabled attribute
-- | Checked             │ -                          │ Form input state
-- | Indeterminate       │ -                          │ Form input state
-- | ```
-- |
-- | The Scraper captures CSS pseudo-class visual changes, while Schema's
-- | Gestural module models the underlying interaction mechanics (intent
-- | detection, pointer tracking, focus management).
-- |
-- | For full fidelity, use both:
-- | - InteractionState captures WHAT visually changes
-- | - Schema.Gestural modules model HOW to detect/respond to interaction
