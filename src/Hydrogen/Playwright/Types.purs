-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // playwright // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure data types for browser automation.
-- |
-- | This module defines test actions as DATA, not effects. A TestScript is
-- | a description of what to do — the Haskell runtime interprets it against
-- | actual browsers.
-- |
-- | ## Architecture
-- |
-- | ```
-- | PureScript (TestScript data)
-- |     ↓ serialize
-- | Haskell Runtime
-- |     ↓ interpret
-- | Browser (Chromium/Firefox/WebKit)
-- | ```
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Test scripts are pure data. Agents can compose, diff, serialize, and
-- | reason about tests algebraically. No opaque handles. No FFI. No JavaScript.

module Hydrogen.Playwright.Types
  ( -- * Browser Configuration
    BrowserType(..)
  , BrowserConfig
  , browserConfig
  , defaultBrowserConfig
  
    -- * Viewport Configuration
  , ViewportSize
  , viewportSize
  , defaultViewport
  
    -- * Timeout Configuration
  , Timeout
  , timeout
  , timeoutMs
  , defaultTimeout
  , defaultNavigationTimeout
  , timeoutBounds
  
    -- * Selectors
  , Selector(..)
  , SelectorIndex
  , selectorIndex
  , selectorIndexBounds
  
    -- * Load States
  , LoadState(..)
  
    -- * Screenshot Configuration
  , ImageFormat(..)
  , ImageQuality
  , imageQuality
  , imageQualityBounds
  , ScreenshotConfig
  , screenshotConfig
  , defaultScreenshotConfig
  
    -- * PDF Configuration
  , PaperFormat(..)
  , PDFMargin
  , pdfMargin
  , defaultPDFMargin
  , PDFConfig
  , pdfConfig
  , defaultPDFConfig
  
    -- * Input Types
  , KeyboardKey(..)
  , MouseButton(..)
  , Point2D
  , point2D
  
    -- * Test Actions
  , TestAction(..)
  
    -- * Test Scripts
  , TestScript
  , testScript
  , scriptName
  , scriptActions
  , appendAction
  , prependAction
  
    -- * Assertions
  , Assertion(..)
  , TextMatch(..)
  
    -- * Test Results
  , ActionResult(..)
  , TestResult
  , testResult
  , resultScript
  , resultOutcomes
  , allPassed
  
    -- * Session References (for scraper integration)
  , SessionId
  , sessionId
  , sessionIdValue
  , PageRef
  , pageRef
  , pageRefSession
  , pageRefIndex
  
    -- * Legacy Compatibility (deprecated, use TestScript instead)
  , Page
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , map
  , (<>)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (==)
  )

import Data.Array ((:))
import Data.Array (snoc) as Array
import Data.Foldable (all)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded as Bounded

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // browser configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Supported browser engines.
-- |
-- | Each engine has different rendering characteristics. Tests should pass
-- | on all three for cross-browser compatibility.
data BrowserType
  = Chromium  -- ^ Google Chrome / Microsoft Edge engine
  | Firefox   -- ^ Mozilla Firefox engine
  | WebKit    -- ^ Apple Safari engine

derive instance eqBrowserType :: Eq BrowserType
derive instance ordBrowserType :: Ord BrowserType

instance showBrowserType :: Show BrowserType where
  show Chromium = "Chromium"
  show Firefox = "Firefox"
  show WebKit = "WebKit"

-- | Browser launch configuration.
-- |
-- | All fields are bounded and validated at construction.
type BrowserConfig =
  { browserType :: BrowserType
  , headless :: Boolean
  , slowMo :: Timeout        -- ^ Slow down actions by this amount
  , timeout :: Timeout       -- ^ Default timeout for operations
  , devtools :: Boolean      -- ^ Open devtools (Chromium only)
  , viewport :: ViewportSize -- ^ Initial viewport size
  }

-- | Create a browser configuration.
browserConfig 
  :: BrowserType 
  -> Boolean 
  -> Timeout 
  -> Timeout 
  -> Boolean 
  -> ViewportSize 
  -> BrowserConfig
browserConfig bt headless' slowMo' timeout' devtools' viewport' =
  { browserType: bt
  , headless: headless'
  , slowMo: slowMo'
  , timeout: timeout'
  , devtools: devtools'
  , viewport: viewport'
  }

-- | Default browser configuration.
-- |
-- | - Chromium, headless
-- | - No slowMo
-- | - 30 second timeout
-- | - Devtools closed
-- | - 1280x720 viewport
defaultBrowserConfig :: BrowserConfig
defaultBrowserConfig =
  { browserType: Chromium
  , headless: true
  , slowMo: timeout 0
  , timeout: defaultTimeout
  , devtools: false
  , viewport: defaultViewport
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // viewport configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Viewport dimensions in pixels.
-- |
-- | Width and height are bounded to reasonable screen sizes.
-- | Min: 320x200 (minimum usable viewport)
-- | Max: 7680x4320 (8K resolution)
type ViewportSize =
  { width :: Int
  , height :: Int
  }

-- | Create a viewport size, clamping to valid bounds.
viewportSize :: Int -> Int -> ViewportSize
viewportSize w h =
  { width: Bounded.clampInt 320 7680 w
  , height: Bounded.clampInt 200 4320 h
  }

-- | Default viewport (1280x720, 720p).
defaultViewport :: ViewportSize
defaultViewport = viewportSize 1280 720

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // timeout configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Timeout in milliseconds.
-- |
-- | Bounded: 0ms to 300000ms (5 minutes).
-- | Tests that take longer than 5 minutes are architectural failures.
newtype Timeout = Timeout Int

derive instance eqTimeout :: Eq Timeout
derive instance ordTimeout :: Ord Timeout

instance showTimeout :: Show Timeout where
  show (Timeout ms) = show ms <> "ms"

-- | Create a timeout, clamping to valid range.
timeout :: Int -> Timeout
timeout ms = Timeout (Bounded.clampInt 0 300000 ms)

-- | Extract milliseconds from timeout.
timeoutMs :: Timeout -> Int
timeoutMs (Timeout ms) = ms

-- | Default operation timeout (30 seconds).
defaultTimeout :: Timeout
defaultTimeout = timeout 30000

-- | Default navigation timeout (30 seconds).
defaultNavigationTimeout :: Timeout
defaultNavigationTimeout = timeout 30000

-- | Bounds documentation for Timeout.
timeoutBounds :: Bounded.IntBounds
timeoutBounds = Bounded.intBounds 0 300000 Bounded.Clamps 
  "timeout" "Operation timeout in milliseconds (0-300000)"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // selectors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Element selector — pure data describing how to find an element.
-- |
-- | No CSS selector strings. Each selector type is explicit and bounded.
-- | The runtime interprets these against the actual DOM.
data Selector
  = ByRole String                    -- ^ ARIA role (button, textbox, etc.)
  | ByText TextMatch                 -- ^ Text content match
  | ByTestId String                  -- ^ data-testid attribute
  | ByLabel String                   -- ^ Associated label text
  | ByPlaceholder String             -- ^ Placeholder attribute
  | ByAltText String                 -- ^ Alt text for images
  | ByTitle String                   -- ^ Title attribute
  | First Selector                   -- ^ First matching element
  | Last Selector                    -- ^ Last matching element
  | Nth Selector SelectorIndex       -- ^ Nth matching element (0-indexed)
  | Filter Selector Assertion        -- ^ Filter by assertion
  | Chain Selector Selector          -- ^ Chained selector (within)

derive instance eqSelector :: Eq Selector

instance showSelector :: Show Selector where
  show (ByRole r) = "ByRole(" <> r <> ")"
  show (ByText tm) = "ByText(" <> show tm <> ")"
  show (ByTestId tid) = "ByTestId(" <> tid <> ")"
  show (ByLabel l) = "ByLabel(" <> l <> ")"
  show (ByPlaceholder p) = "ByPlaceholder(" <> p <> ")"
  show (ByAltText a) = "ByAltText(" <> a <> ")"
  show (ByTitle t) = "ByTitle(" <> t <> ")"
  show (First s) = "First(" <> show s <> ")"
  show (Last s) = "Last(" <> show s <> ")"
  show (Nth s i) = "Nth(" <> show s <> ", " <> show i <> ")"
  show (Filter s a) = "Filter(" <> show s <> ", " <> show a <> ")"
  show (Chain s1 s2) = "Chain(" <> show s1 <> ", " <> show s2 <> ")"

-- | Selector index for Nth — bounded 0-999.
-- |
-- | If you have more than 1000 matching elements, your selector is wrong.
newtype SelectorIndex = SelectorIndex Int

derive instance eqSelectorIndex :: Eq SelectorIndex
derive instance ordSelectorIndex :: Ord SelectorIndex

instance showSelectorIndex :: Show SelectorIndex where
  show (SelectorIndex i) = show i

-- | Create a selector index, clamping to valid range.
selectorIndex :: Int -> SelectorIndex
selectorIndex i = SelectorIndex (Bounded.clampInt 0 999 i)

-- | Bounds for selector index.
selectorIndexBounds :: Bounded.IntBounds
selectorIndexBounds = Bounded.intBounds 0 999 Bounded.Clamps
  "selectorIndex" "Element index for Nth selector (0-999)"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // load states
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page load states for navigation.
data LoadState
  = Load            -- ^ Wait for 'load' event
  | DOMContentLoaded -- ^ Wait for 'DOMContentLoaded' event
  | NetworkIdle     -- ^ Wait for network to be idle

derive instance eqLoadState :: Eq LoadState
derive instance ordLoadState :: Ord LoadState

instance showLoadState :: Show LoadState where
  show Load = "Load"
  show DOMContentLoaded = "DOMContentLoaded"
  show NetworkIdle = "NetworkIdle"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // screenshot configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Image format for screenshots.
data ImageFormat
  = PNG   -- ^ Lossless, larger file size
  | JPEG  -- ^ Lossy, smaller file size

derive instance eqImageFormat :: Eq ImageFormat
derive instance ordImageFormat :: Ord ImageFormat

instance showImageFormat :: Show ImageFormat where
  show PNG = "PNG"
  show JPEG = "JPEG"

-- | Image quality for JPEG (0-100).
-- |
-- | Ignored for PNG format.
newtype ImageQuality = ImageQuality Int

derive instance eqImageQuality :: Eq ImageQuality
derive instance ordImageQuality :: Ord ImageQuality

instance showImageQuality :: Show ImageQuality where
  show (ImageQuality q) = show q <> "%"

-- | Create image quality, clamping to valid range.
imageQuality :: Int -> ImageQuality
imageQuality q = ImageQuality (Bounded.clampInt 0 100 q)

-- | Bounds for image quality.
imageQualityBounds :: Bounded.IntBounds
imageQualityBounds = Bounded.intBounds 0 100 Bounded.Clamps
  "imageQuality" "JPEG quality percentage (0-100)"

-- | Screenshot configuration.
type ScreenshotConfig =
  { path :: String           -- ^ File path to save screenshot
  , fullPage :: Boolean      -- ^ Capture full scrollable page
  , format :: ImageFormat    -- ^ PNG or JPEG
  , quality :: ImageQuality  -- ^ Quality for JPEG
  , selector :: Maybe Selector -- ^ Capture specific element
  }

-- | Create screenshot configuration.
screenshotConfig 
  :: String 
  -> Boolean 
  -> ImageFormat 
  -> ImageQuality 
  -> Maybe Selector 
  -> ScreenshotConfig
screenshotConfig path' fullPage' format' quality' selector' =
  { path: path'
  , fullPage: fullPage'
  , format: format'
  , quality: quality'
  , selector: selector'
  }

-- | Default screenshot configuration.
defaultScreenshotConfig :: ScreenshotConfig
defaultScreenshotConfig =
  { path: ""
  , fullPage: false
  , format: PNG
  , quality: imageQuality 100
  , selector: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // pdf configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Standard paper formats for PDF generation.
data PaperFormat
  = A4         -- ^ 210 × 297 mm
  | A3         -- ^ 297 × 420 mm
  | Letter     -- ^ 8.5 × 11 inches
  | Legal      -- ^ 8.5 × 14 inches
  | Tabloid    -- ^ 11 × 17 inches

derive instance eqPaperFormat :: Eq PaperFormat
derive instance ordPaperFormat :: Ord PaperFormat

instance showPaperFormat :: Show PaperFormat where
  show A4 = "A4"
  show A3 = "A3"
  show Letter = "Letter"
  show Legal = "Legal"
  show Tabloid = "Tabloid"

-- | PDF margin in millimeters.
-- |
-- | All margins bounded 0-100mm.
type PDFMargin =
  { top :: Int
  , right :: Int
  , bottom :: Int
  , left :: Int
  }

-- | Create PDF margin, clamping values to valid range.
pdfMargin :: Int -> Int -> Int -> Int -> PDFMargin
pdfMargin t r b l =
  { top: Bounded.clampInt 0 100 t
  , right: Bounded.clampInt 0 100 r
  , bottom: Bounded.clampInt 0 100 b
  , left: Bounded.clampInt 0 100 l
  }

-- | Default PDF margin (0mm all sides).
defaultPDFMargin :: PDFMargin
defaultPDFMargin = pdfMargin 0 0 0 0

-- | PDF generation configuration.
type PDFConfig =
  { path :: String
  , format :: PaperFormat
  , printBackground :: Boolean
  , margin :: PDFMargin
  }

-- | Create PDF configuration.
pdfConfig :: String -> PaperFormat -> Boolean -> PDFMargin -> PDFConfig
pdfConfig path' format' printBg margin' =
  { path: path'
  , format: format'
  , printBackground: printBg
  , margin: margin'
  }

-- | Default PDF configuration.
defaultPDFConfig :: PDFConfig
defaultPDFConfig =
  { path: ""
  , format: A4
  , printBackground: true
  , margin: defaultPDFMargin
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // input types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Keyboard keys for press/type actions.
-- |
-- | Explicit enumeration — no arbitrary key strings.
data KeyboardKey
  = KeyEnter
  | KeyTab
  | KeyEscape
  | KeyBackspace
  | KeyDelete
  | KeyArrowUp
  | KeyArrowDown
  | KeyArrowLeft
  | KeyArrowRight
  | KeyHome
  | KeyEnd
  | KeyPageUp
  | KeyPageDown
  | KeySpace
  | KeyF1 | KeyF2 | KeyF3 | KeyF4 | KeyF5 | KeyF6
  | KeyF7 | KeyF8 | KeyF9 | KeyF10 | KeyF11 | KeyF12
  | KeyA | KeyB | KeyC | KeyD | KeyE | KeyF | KeyG | KeyH | KeyI
  | KeyJ | KeyK | KeyL | KeyM | KeyN | KeyO | KeyP | KeyQ | KeyR
  | KeyS | KeyT | KeyU | KeyV | KeyW | KeyX | KeyY | KeyZ
  | Key0 | Key1 | Key2 | Key3 | Key4 | Key5 | Key6 | Key7 | Key8 | Key9
  | KeyShift
  | KeyControl
  | KeyAlt
  | KeyMeta

derive instance eqKeyboardKey :: Eq KeyboardKey
derive instance ordKeyboardKey :: Ord KeyboardKey

instance showKeyboardKey :: Show KeyboardKey where
  show KeyEnter = "Enter"
  show KeyTab = "Tab"
  show KeyEscape = "Escape"
  show KeyBackspace = "Backspace"
  show KeyDelete = "Delete"
  show KeyArrowUp = "ArrowUp"
  show KeyArrowDown = "ArrowDown"
  show KeyArrowLeft = "ArrowLeft"
  show KeyArrowRight = "ArrowRight"
  show KeyHome = "Home"
  show KeyEnd = "End"
  show KeyPageUp = "PageUp"
  show KeyPageDown = "PageDown"
  show KeySpace = "Space"
  show KeyF1 = "F1"
  show KeyF2 = "F2"
  show KeyF3 = "F3"
  show KeyF4 = "F4"
  show KeyF5 = "F5"
  show KeyF6 = "F6"
  show KeyF7 = "F7"
  show KeyF8 = "F8"
  show KeyF9 = "F9"
  show KeyF10 = "F10"
  show KeyF11 = "F11"
  show KeyF12 = "F12"
  show KeyA = "a"
  show KeyB = "b"
  show KeyC = "c"
  show KeyD = "d"
  show KeyE = "e"
  show KeyF = "f"
  show KeyG = "g"
  show KeyH = "h"
  show KeyI = "i"
  show KeyJ = "j"
  show KeyK = "k"
  show KeyL = "l"
  show KeyM = "m"
  show KeyN = "n"
  show KeyO = "o"
  show KeyP = "p"
  show KeyQ = "q"
  show KeyR = "r"
  show KeyS = "s"
  show KeyT = "t"
  show KeyU = "u"
  show KeyV = "v"
  show KeyW = "w"
  show KeyX = "x"
  show KeyY = "y"
  show KeyZ = "z"
  show Key0 = "0"
  show Key1 = "1"
  show Key2 = "2"
  show Key3 = "3"
  show Key4 = "4"
  show Key5 = "5"
  show Key6 = "6"
  show Key7 = "7"
  show Key8 = "8"
  show Key9 = "9"
  show KeyShift = "Shift"
  show KeyControl = "Control"
  show KeyAlt = "Alt"
  show KeyMeta = "Meta"

-- | Mouse button for click actions.
data MouseButton
  = LeftButton
  | RightButton
  | MiddleButton

derive instance eqMouseButton :: Eq MouseButton
derive instance ordMouseButton :: Ord MouseButton

instance showMouseButton :: Show MouseButton where
  show LeftButton = "left"
  show RightButton = "right"
  show MiddleButton = "middle"

-- | 2D point for mouse positioning.
-- |
-- | Coordinates bounded to reasonable viewport range.
type Point2D =
  { x :: Int
  , y :: Int
  }

-- | Create a 2D point, clamping to valid range.
point2D :: Int -> Int -> Point2D
point2D x' y' =
  { x: Bounded.clampInt 0 7680 x'
  , y: Bounded.clampInt 0 4320 y'
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // test actions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Test action — pure data describing a single browser operation.
-- |
-- | No effects. No handles. Just data describing what to do.
-- | The Haskell runtime interprets these against actual browsers.
data TestAction
  -- Navigation
  = Navigate String LoadState          -- ^ Navigate to URL, wait for load state
  | GoBack                             -- ^ Navigate back
  | GoForward                          -- ^ Navigate forward  
  | Reload LoadState                   -- ^ Reload page
  
  -- Element Interactions
  | Click Selector MouseButton         -- ^ Click element
  | DoubleClick Selector               -- ^ Double-click element
  | Fill Selector String               -- ^ Fill input with text (clears first)
  | Type Selector String               -- ^ Type text character by character
  | Press Selector KeyboardKey         -- ^ Press a key
  | Check Selector                     -- ^ Check checkbox/radio
  | Uncheck Selector                   -- ^ Uncheck checkbox
  | SelectOption Selector String       -- ^ Select dropdown option by value
  | Hover Selector                     -- ^ Hover over element
  | Focus Selector                     -- ^ Focus element
  | Blur Selector                      -- ^ Blur element
  
  -- Mouse Actions
  | MouseMove Point2D                  -- ^ Move mouse to position
  | MouseDown MouseButton              -- ^ Press mouse button
  | MouseUp MouseButton                -- ^ Release mouse button
  
  -- Keyboard Actions  
  | KeyDown KeyboardKey                -- ^ Press key down
  | KeyUp KeyboardKey                  -- ^ Release key
  
  -- Waiting
  | WaitForSelector Selector Timeout   -- ^ Wait for element to appear
  | WaitForTimeout Timeout             -- ^ Wait for fixed time
  | WaitForLoadState LoadState         -- ^ Wait for page load state
  
  -- Assertions
  | Assert Selector Assertion          -- ^ Assert condition on element
  
  -- Screenshots/PDF
  | Screenshot ScreenshotConfig        -- ^ Take screenshot
  | PDF PDFConfig                      -- ^ Generate PDF
  
  -- Scraping / Evaluation
  | Evaluate String                    -- ^ Evaluate script, return result as string
  | CaptureStyles Selector             -- ^ Capture computed styles for element

derive instance eqTestAction :: Eq TestAction

instance showTestAction :: Show TestAction where
  show (Navigate url ls) = "Navigate(" <> url <> ", " <> show ls <> ")"
  show GoBack = "GoBack"
  show GoForward = "GoForward"
  show (Reload ls) = "Reload(" <> show ls <> ")"
  show (Click s mb) = "Click(" <> show s <> ", " <> show mb <> ")"
  show (DoubleClick s) = "DoubleClick(" <> show s <> ")"
  show (Fill s t) = "Fill(" <> show s <> ", " <> t <> ")"
  show (Type s t) = "Type(" <> show s <> ", " <> t <> ")"
  show (Press s k) = "Press(" <> show s <> ", " <> show k <> ")"
  show (Check s) = "Check(" <> show s <> ")"
  show (Uncheck s) = "Uncheck(" <> show s <> ")"
  show (SelectOption s v) = "SelectOption(" <> show s <> ", " <> v <> ")"
  show (Hover s) = "Hover(" <> show s <> ")"
  show (Focus s) = "Focus(" <> show s <> ")"
  show (Blur s) = "Blur(" <> show s <> ")"
  show (MouseMove p) = "MouseMove(" <> show p.x <> ", " <> show p.y <> ")"
  show (MouseDown mb) = "MouseDown(" <> show mb <> ")"
  show (MouseUp mb) = "MouseUp(" <> show mb <> ")"
  show (KeyDown k) = "KeyDown(" <> show k <> ")"
  show (KeyUp k) = "KeyUp(" <> show k <> ")"
  show (WaitForSelector s t) = "WaitForSelector(" <> show s <> ", " <> show t <> ")"
  show (WaitForTimeout t) = "WaitForTimeout(" <> show t <> ")"
  show (WaitForLoadState ls) = "WaitForLoadState(" <> show ls <> ")"
  show (Assert s a) = "Assert(" <> show s <> ", " <> show a <> ")"
  show (Screenshot _) = "Screenshot(...)"
  show (PDF _) = "PDF(...)"
  show (Evaluate script) = "Evaluate(" <> script <> ")"
  show (CaptureStyles s) = "CaptureStyles(" <> show s <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // test scripts
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Test script — a named sequence of actions.
-- |
-- | Pure data. Composable. Serializable. Diffable.
newtype TestScript = TestScript
  { name :: String
  , actions :: Array TestAction
  }

derive instance eqTestScript :: Eq TestScript

instance showTestScript :: Show TestScript where
  show (TestScript s) = "TestScript(" <> s.name <> ", " <> show s.actions <> ")"

-- | Create a test script.
testScript :: String -> Array TestAction -> TestScript
testScript name' actions' = TestScript { name: name', actions: actions' }

-- | Get the script name.
scriptName :: TestScript -> String
scriptName (TestScript s) = s.name

-- | Get the script actions.
scriptActions :: TestScript -> Array TestAction
scriptActions (TestScript s) = s.actions

-- | Append an action to the script.
appendAction :: TestAction -> TestScript -> TestScript
appendAction action (TestScript s) = 
  TestScript { name: s.name, actions: Array.snoc s.actions action }

-- | Prepend an action to the script.
prependAction :: TestAction -> TestScript -> TestScript
prependAction action (TestScript s) =
  TestScript { name: s.name, actions: action : s.actions }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // assertions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Text matching strategy for assertions.
data TextMatch
  = Exact String           -- ^ Exact match
  | Contains String        -- ^ Contains substring
  | StartsWith String      -- ^ Starts with prefix
  | EndsWith String        -- ^ Ends with suffix
  | MatchesPattern String  -- ^ Matches regex pattern

derive instance eqTextMatch :: Eq TextMatch

instance showTextMatch :: Show TextMatch where
  show (Exact s) = "Exact(" <> s <> ")"
  show (Contains s) = "Contains(" <> s <> ")"
  show (StartsWith s) = "StartsWith(" <> s <> ")"
  show (EndsWith s) = "EndsWith(" <> s <> ")"
  show (MatchesPattern s) = "MatchesPattern(" <> s <> ")"

-- | Assertion — condition to check on an element.
data Assertion
  = IsVisible
  | IsHidden
  | IsEnabled
  | IsDisabled
  | IsChecked
  | IsUnchecked
  | HasText TextMatch
  | HasValue TextMatch
  | HasAttribute String TextMatch
  | HasCount Int           -- ^ Element count matches

derive instance eqAssertion :: Eq Assertion

instance showAssertion :: Show Assertion where
  show IsVisible = "IsVisible"
  show IsHidden = "IsHidden"
  show IsEnabled = "IsEnabled"
  show IsDisabled = "IsDisabled"
  show IsChecked = "IsChecked"
  show IsUnchecked = "IsUnchecked"
  show (HasText tm) = "HasText(" <> show tm <> ")"
  show (HasValue tm) = "HasValue(" <> show tm <> ")"
  show (HasAttribute attr tm) = "HasAttribute(" <> attr <> ", " <> show tm <> ")"
  show (HasCount n) = "HasCount(" <> show n <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // test results
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Result of executing a single action.
data ActionResult
  = Passed                  -- ^ Action succeeded
  | Failed String           -- ^ Action failed with message
  | Skipped String          -- ^ Action skipped with reason

derive instance eqActionResult :: Eq ActionResult

instance showActionResult :: Show ActionResult where
  show Passed = "Passed"
  show (Failed msg) = "Failed(" <> msg <> ")"
  show (Skipped reason) = "Skipped(" <> reason <> ")"

-- | Result of executing a test script.
-- |
-- | Pairs each action with its result for traceability.
newtype TestResult = TestResult
  { script :: TestScript
  , outcomes :: Array { action :: TestAction, result :: ActionResult }
  }

derive instance eqTestResult :: Eq TestResult

instance showTestResult :: Show TestResult where
  show (TestResult r) = "TestResult(" <> scriptName r.script <> ")"

-- | Create a test result.
testResult 
  :: TestScript 
  -> Array { action :: TestAction, result :: ActionResult } 
  -> TestResult
testResult script' outcomes' = TestResult { script: script', outcomes: outcomes' }

-- | Get the original script.
resultScript :: TestResult -> TestScript
resultScript (TestResult r) = r.script

-- | Get the outcomes.
resultOutcomes :: TestResult -> Array { action :: TestAction, result :: ActionResult }
resultOutcomes (TestResult r) = r.outcomes

-- | Check if all actions passed.
allPassed :: TestResult -> Boolean
allPassed (TestResult r) = all (\o -> o.result == Passed) r.outcomes

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // session references
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Session identifier — pure data reference to a browser session.
-- |
-- | This is NOT an opaque handle. It's a bounded identifier that the
-- | Haskell runtime resolves to an actual browser session.
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Sessions are identified by deterministic IDs. Multiple agents can
-- | reference the same session by ID. The runtime manages session lifecycle.
newtype SessionId = SessionId String

derive instance eqSessionId :: Eq SessionId
derive instance ordSessionId :: Ord SessionId

instance showSessionId :: Show SessionId where
  show (SessionId sid) = "Session(" <> sid <> ")"

-- | Create a session ID.
sessionId :: String -> SessionId
sessionId = SessionId

-- | Extract the session ID value.
sessionIdValue :: SessionId -> String
sessionIdValue (SessionId sid) = sid

-- | Page reference — pure data reference to a page within a session.
-- |
-- | This is NOT an opaque handle. It's a pair of (session, page index)
-- | that the Haskell runtime resolves to an actual browser page.
-- |
-- | ## For Scraper Integration
-- |
-- | Scrapers reference pages by PageRef. The runtime provides actual
-- | page access. Scrapers describe WHAT to capture, not HOW to access.
newtype PageRef = PageRef
  { session :: SessionId
  , index :: Int
  }

derive instance eqPageRef :: Eq PageRef
derive instance ordPageRef :: Ord PageRef

instance showPageRef :: Show PageRef where
  show (PageRef p) = "Page(" <> show p.session <> ", " <> show p.index <> ")"

-- | Create a page reference.
pageRef :: SessionId -> Int -> PageRef
pageRef sess idx = PageRef { session: sess, index: Bounded.clampInt 0 999 idx }

-- | Get the session ID from a page reference.
pageRefSession :: PageRef -> SessionId
pageRefSession (PageRef p) = p.session

-- | Get the page index from a page reference.
pageRefIndex :: PageRef -> Int
pageRefIndex (PageRef p) = p.index

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // legacy compatibility
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page — alias for PageRef.
-- |
-- | **DEPRECATED**: This type exists for backward compatibility with code
-- | that imported `Page` from the old FFI-based Playwright module.
-- |
-- | Old code:
-- | ```purescript
-- | import Hydrogen.Playwright (Page)
-- | scrape :: Page -> Aff Result
-- | ```
-- |
-- | New code should use TestScript for test automation and PageRef for
-- | runtime page references.
type Page = PageRef
