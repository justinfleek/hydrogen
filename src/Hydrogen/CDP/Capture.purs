-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // cdp // capture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Temporal capture state machine for website scraping.
-- |
-- | This module defines the capture system as a pure state machine that
-- | records website state over time at 60fps. Used for extracting:
-- | - CSS animations and transitions
-- | - Dynamic color schemes
-- | - Layout behavior
-- | - Interaction patterns
-- |
-- | ## Architecture
-- |
-- | ```
-- | CaptureState × CaptureInput → CaptureState × [CaptureCommand]
-- | ```
-- |
-- | Frames are pure data. The runtime captures actual pixels/styles.
-- |
-- | ## Output Format
-- |
-- | Capture produces SIGIL frames containing Hydrogen Schema atoms:
-- | - OKLCH colors (not hex strings)
-- | - Pixel positions (bounded)
-- | - Duration values (milliseconds)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Captures are deterministic. Same website state produces same frames.
-- | Agents can share capture data, diff animations, and compose designs
-- | from scraped websites algebraically.

module Hydrogen.CDP.Capture
  ( -- * Configuration
    CaptureConfig
  , captureConfig
  , defaultCaptureConfig
  , configDuration
  , configFrameRate
  , configViewport
  
    -- * Frame Types
  , FrameIndex
  , frameIndex
  , frameIndexValue
  , frameIndexBounds
  
  , Timestamp
  , timestamp
  , timestampMs
  
  , Frame
  , frameIndex'
  , frameTimestamp
  , frameElements
  , frameStyles
  
    -- * Captured Elements
  , CapturedElement
  , elementSelector
  , elementBounds
  , elementStyles
  
  , ElementBounds
  , boundsX
  , boundsY
  , boundsWidth
  , boundsHeight
  
  , StylePair
  
    -- * Capture State Machine
  , CapturePhase(Idle, Preparing, Capturing, Processing, Complete, Failed)
  , CaptureState
  , captureStateInitial
  , capturePhase
  , captureFrames
  , captureProgress
  
    -- * Commands and Events
  , CaptureCommand(StartCapture, CaptureFrame, StopCapture, ProcessFrames)
  , CaptureEvent(CaptureReady, FrameCaptured, CaptureComplete, CaptureError)
  , CaptureInput(StartInput, FrameInput, StopInput, ErrorInput)
  
    -- * Transition
  , CaptureResult
  , captureTransition
  
    -- * Frame Rate
  , FrameRate
  , frameRate
  , frameRateValue
  , fps60
  , fps30
  , fps24
  , frameDuration
  
    -- * HydrogenM API (graded monad integration)
  , CaptureM
  , runCaptureM
  , startCaptureM
  , captureFrameM
  , processCaptureM
  , getCaptureProgress
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , pure
  , (==)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (>=)
  )

import Data.Array (length, snoc, foldl) as Array
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)

import Hydrogen.Playwright.Types (Selector, ViewportSize, viewportSize)
import Hydrogen.Effect.Grade (Grade, NetOnly, Pure)
import Hydrogen.Effect.Graded 
  ( HydrogenM(HydrogenM)
  , HydrogenResult
  , HydrogenGrade
  , HydrogenCoEffect
  , HydrogenProvenance
  , emptyGrade
  , emptyCoEffect
  , emptyProvenance
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // frame rate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame rate in frames per second.
-- |
-- | Bounded: 1-120 fps. Higher rates increase data volume without
-- | proportional quality improvement for most animations.
newtype FrameRate = FrameRate Int

derive instance eqFrameRate :: Eq FrameRate
derive instance ordFrameRate :: Ord FrameRate

instance showFrameRate :: Show FrameRate where
  show (FrameRate n) = show n <> "fps"

-- | Create a frame rate, clamping to valid range.
frameRate :: Int -> FrameRate
frameRate n
  | n < 1 = FrameRate 1
  | n > 120 = FrameRate 120
  | otherwise = FrameRate n

-- | Extract numeric value.
frameRateValue :: FrameRate -> Int
frameRateValue (FrameRate n) = n

-- | 60 frames per second (standard smooth animation).
fps60 :: FrameRate
fps60 = FrameRate 60

-- | 30 frames per second (acceptable for most UI).
fps30 :: FrameRate
fps30 = FrameRate 30

-- | 24 frames per second (cinematic).
fps24 :: FrameRate
fps24 = FrameRate 24

-- | Duration between frames in milliseconds.
frameDuration :: FrameRate -> Number
frameDuration (FrameRate n) = 1000.0 / Int.toNumber n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Capture configuration.
-- |
-- | Defines the parameters for a temporal capture session.
type CaptureConfig =
  { duration :: Int          -- ^ Capture duration in milliseconds (max 60000)
  , frameRate :: FrameRate   -- ^ Frames per second
  , viewport :: ViewportSize -- ^ Viewport dimensions
  , selectors :: Array Selector -- ^ Elements to capture (empty = full page)
  }

-- | Create capture configuration with bounds enforcement.
captureConfig :: Int -> FrameRate -> ViewportSize -> Array Selector -> CaptureConfig
captureConfig dur fr vp sels =
  { duration: clampDuration dur
  , frameRate: fr
  , viewport: vp
  , selectors: sels
  }
  where
  clampDuration d
    | d < 100 = 100       -- Minimum 100ms
    | d > 60000 = 60000   -- Maximum 60 seconds
    | otherwise = d

-- | Default capture configuration.
-- |
-- | - 30 seconds at 60fps
-- | - 1280x720 viewport
-- | - Full page capture
defaultCaptureConfig :: CaptureConfig
defaultCaptureConfig =
  { duration: 30000
  , frameRate: fps60
  , viewport: viewportSize 1280 720
  , selectors: []
  }

-- | Get capture duration.
configDuration :: CaptureConfig -> Int
configDuration c = c.duration

-- | Get frame rate.
configFrameRate :: CaptureConfig -> FrameRate
configFrameRate c = c.frameRate

-- | Get viewport.
configViewport :: CaptureConfig -> ViewportSize
configViewport c = c.viewport

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // frame types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frame index (0-indexed).
-- |
-- | Bounded based on max duration and frame rate.
-- | At 60fps for 60 seconds: max 3600 frames.
newtype FrameIndex = FrameIndex Int

derive instance eqFrameIndex :: Eq FrameIndex
derive instance ordFrameIndex :: Ord FrameIndex

instance showFrameIndex :: Show FrameIndex where
  show (FrameIndex n) = "Frame(" <> show n <> ")"

-- | Create frame index with bounds.
frameIndex :: Int -> FrameIndex
frameIndex n
  | n < 0 = FrameIndex 0
  | n > 7200 = FrameIndex 7200  -- Max: 120fps × 60s
  | otherwise = FrameIndex n

-- | Extract numeric value.
frameIndexValue :: FrameIndex -> Int
frameIndexValue (FrameIndex n) = n

-- | Frame index bounds documentation.
frameIndexBounds :: { min :: Int, max :: Int, description :: String }
frameIndexBounds =
  { min: 0
  , max: 7200
  , description: "Frame index (0-7200, max 120fps × 60s)"
  }

-- | Timestamp in milliseconds from capture start.
newtype Timestamp = Timestamp Number

derive instance eqTimestamp :: Eq Timestamp
derive instance ordTimestamp :: Ord Timestamp

instance showTimestamp :: Show Timestamp where
  show (Timestamp ms) = show ms <> "ms"

-- | Create a timestamp.
timestamp :: Number -> Timestamp
timestamp ms
  | ms < 0.0 = Timestamp 0.0
  | ms > 60000.0 = Timestamp 60000.0
  | otherwise = Timestamp ms

-- | Extract milliseconds.
timestampMs :: Timestamp -> Number
timestampMs (Timestamp ms) = ms

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // captured elements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding box of an element.
type ElementBounds =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- | Get bounds X.
boundsX :: ElementBounds -> Number
boundsX b = b.x

-- | Get bounds Y.
boundsY :: ElementBounds -> Number
boundsY b = b.y

-- | Get bounds width.
boundsWidth :: ElementBounds -> Number
boundsWidth b = b.width

-- | Get bounds height.
boundsHeight :: ElementBounds -> Number
boundsHeight b = b.height

-- | Captured element at a point in time.
-- |
-- | Contains all visual properties needed to reconstruct the element.
type CapturedElement =
  { selector :: Selector              -- ^ How this element was selected
  , bounds :: ElementBounds           -- ^ Position and size
  , computedStyles :: Array StylePair -- ^ Computed CSS values
  , visible :: Boolean                -- ^ Is element visible
  , opacity :: Number                 -- ^ Current opacity (0-1)
  }

-- | Style key-value pair.
-- |
-- | Represents a computed CSS property.
type StylePair =
  { property :: String  -- ^ CSS property name
  , value :: String     -- ^ Computed value
  }

-- | Get element selector.
elementSelector :: CapturedElement -> Selector
elementSelector e = e.selector

-- | Get element bounds.
elementBounds :: CapturedElement -> ElementBounds
elementBounds e = e.bounds

-- | Get element styles.
elementStyles :: CapturedElement -> Array StylePair
elementStyles e = e.computedStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // frames
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single captured frame.
-- |
-- | Contains the state of all tracked elements at one point in time.
type Frame =
  { index :: FrameIndex               -- ^ Frame number
  , timestamp :: Timestamp            -- ^ Time from capture start
  , elements :: Array CapturedElement -- ^ Captured element states
  , screenshot :: Maybe String        -- ^ Optional base64 screenshot
  }

-- | Get frame index.
frameIndex' :: Frame -> FrameIndex
frameIndex' f = f.index

-- | Get frame timestamp.
frameTimestamp :: Frame -> Timestamp
frameTimestamp f = f.timestamp

-- | Get frame elements.
frameElements :: Frame -> Array CapturedElement
frameElements f = f.elements

-- | Get frame styles (flattened from all elements).
-- |
-- | Uses pure Data.Array.foldl — no FFI required.
frameStyles :: Frame -> Array StylePair
frameStyles f = flattenStyles f.elements
  where
  flattenStyles :: Array CapturedElement -> Array StylePair
  flattenStyles elems = 
    -- Concatenate all computed styles from all elements
    Array.foldl (\acc e -> acc <> e.computedStyles) [] elems

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // capture state machine
-- ═════════════════════════════════════════════════════════════════════════════

-- | Capture lifecycle phases.
data CapturePhase
  = Idle         -- ^ Ready to start capture
  | Preparing    -- ^ Setting up capture (navigating, waiting for load)
  | Capturing    -- ^ Actively capturing frames
  | Processing   -- ^ Processing captured frames (delta encoding, etc.)
  | Complete     -- ^ Capture finished successfully
  | Failed       -- ^ Capture failed with error

derive instance eqCapturePhase :: Eq CapturePhase
derive instance ordCapturePhase :: Ord CapturePhase

instance showCapturePhase :: Show CapturePhase where
  show Idle = "Idle"
  show Preparing = "Preparing"
  show Capturing = "Capturing"
  show Processing = "Processing"
  show Complete = "Complete"
  show Failed = "Failed"

-- | Capture state.
type CaptureState =
  { phase :: CapturePhase
  , config :: CaptureConfig
  , frames :: Array Frame
  , currentFrame :: FrameIndex
  , totalFrames :: Int
  , errorMessage :: Maybe String
  }

-- | Initial capture state.
captureStateInitial :: CaptureConfig -> CaptureState
captureStateInitial cfg =
  { phase: Idle
  , config: cfg
  , frames: []
  , currentFrame: frameIndex 0
  , totalFrames: calculateTotalFrames cfg
  , errorMessage: Nothing
  }
  where
  calculateTotalFrames :: CaptureConfig -> Int
  calculateTotalFrames c = 
    (c.duration * frameRateValue c.frameRate) / 1000

-- | Get capture phase.
capturePhase :: CaptureState -> CapturePhase
capturePhase s = s.phase

-- | Get captured frames.
captureFrames :: CaptureState -> Array Frame
captureFrames s = s.frames

-- | Get capture progress (0.0 to 1.0).
captureProgress :: CaptureState -> Number
captureProgress s
  | s.totalFrames == 0 = 0.0
  | otherwise = Int.toNumber (frameIndexValue s.currentFrame) / Int.toNumber s.totalFrames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // commands and events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Commands emitted by the state machine.
data CaptureCommand
  = StartCapture CaptureConfig     -- ^ Begin capture with config
  | CaptureFrame FrameIndex        -- ^ Capture frame at index
  | StopCapture                    -- ^ Stop capturing
  | ProcessFrames (Array Frame)    -- ^ Process captured frames

derive instance eqCaptureCommand :: Eq CaptureCommand

instance showCaptureCommand :: Show CaptureCommand where
  show (StartCapture _) = "StartCapture"
  show (CaptureFrame idx) = "CaptureFrame(" <> show idx <> ")"
  show StopCapture = "StopCapture"
  show (ProcessFrames fs) = "ProcessFrames(" <> show (Array.length fs) <> " frames)"

-- | Events received from the runtime.
data CaptureEvent
  = CaptureReady                   -- ^ Ready to begin capturing
  | FrameCaptured Frame            -- ^ Frame was captured
  | CaptureComplete (Array Frame)  -- ^ All frames captured
  | CaptureError String            -- ^ Error during capture

derive instance eqCaptureEvent :: Eq CaptureEvent

instance showCaptureEvent :: Show CaptureEvent where
  show CaptureReady = "CaptureReady"
  show (FrameCaptured f) = "FrameCaptured(" <> show (frameIndex' f) <> ")"
  show (CaptureComplete fs) = "CaptureComplete(" <> show (Array.length fs) <> " frames)"
  show (CaptureError msg) = "CaptureError(" <> msg <> ")"

-- | Input to the capture state machine.
data CaptureInput
  = StartInput                     -- ^ User wants to start capture
  | FrameInput Frame               -- ^ Frame was captured
  | StopInput                      -- ^ User wants to stop
  | ErrorInput String              -- ^ Error occurred

derive instance eqCaptureInput :: Eq CaptureInput

instance showCaptureInput :: Show CaptureInput where
  show StartInput = "Start"
  show (FrameInput f) = "Frame(" <> show (frameIndex' f) <> ")"
  show StopInput = "Stop"
  show (ErrorInput msg) = "Error(" <> msg <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition result.
type CaptureResult =
  { nextState :: CaptureState
  , commands :: Array CaptureCommand
  }

-- | Core transition function.
-- |
-- | Pure: CaptureState × CaptureInput → CaptureState × [CaptureCommand]
captureTransition :: CaptureState -> CaptureInput -> CaptureResult
captureTransition s input = case s.phase, input of
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- IDLE: waiting for start
  -- ═══════════════════════════════════════════════════════════════════════════
  
  Idle, StartInput ->
    { nextState: s { phase = Preparing }
    , commands: [StartCapture s.config]
    }
  
  Idle, _ ->
    { nextState: s, commands: [] }
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- PREPARING: setting up
  -- ═══════════════════════════════════════════════════════════════════════════
  
  Preparing, FrameInput _ ->
    -- Ready signal comes as first frame
    { nextState: s { phase = Capturing }
    , commands: [CaptureFrame (frameIndex 0)]
    }
  
  Preparing, ErrorInput msg ->
    { nextState: s { phase = Failed, errorMessage = Just msg }
    , commands: []
    }
  
  Preparing, _ ->
    { nextState: s, commands: [] }
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- CAPTURING: recording frames
  -- ═══════════════════════════════════════════════════════════════════════════
  
  Capturing, FrameInput frame ->
    let
      newFrames = Array.snoc s.frames frame
      nextIdx = frameIndex (frameIndexValue s.currentFrame + 1)
      done = frameIndexValue nextIdx >= s.totalFrames
    in
      if done then
        { nextState: s 
            { phase = Processing
            , frames = newFrames
            , currentFrame = nextIdx
            }
        , commands: [ProcessFrames newFrames]
        }
      else
        { nextState: s
            { frames = newFrames
            , currentFrame = nextIdx
            }
        , commands: [CaptureFrame nextIdx]
        }
  
  Capturing, StopInput ->
    { nextState: s { phase = Processing }
    , commands: [ProcessFrames s.frames]
    }
  
  Capturing, ErrorInput msg ->
    { nextState: s { phase = Failed, errorMessage = Just msg }
    , commands: [StopCapture]
    }
  
  Capturing, _ ->
    { nextState: s, commands: [] }
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- PROCESSING: finalizing
  -- ═══════════════════════════════════════════════════════════════════════════
  
  Processing, FrameInput _ ->
    -- Processing complete signal
    { nextState: s { phase = Complete }
    , commands: []
    }
  
  Processing, ErrorInput msg ->
    { nextState: s { phase = Failed, errorMessage = Just msg }
    , commands: []
    }
  
  Processing, _ ->
    { nextState: s, commands: [] }
  
  -- ═══════════════════════════════════════════════════════════════════════════
  -- COMPLETE/FAILED: terminal
  -- ═══════════════════════════════════════════════════════════════════════════
  
  Complete, _ ->
    { nextState: s, commands: [] }
  
  Failed, _ ->
    { nextState: s, commands: [] }

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // HydrogenM API (graded monad)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Capture monad: HydrogenM specialized for temporal capture operations.
-- |
-- | ## Grade Semantics
-- |
-- | - `CaptureM Pure a`: Pure query (progress, state inspection)
-- | - `CaptureM NetOnly a`: Network operation (screenshot capture, DOM queries)
-- |
-- | ## 60fps Streaming
-- |
-- | At 60fps, each frame has ~16.67ms budget. The graded monad tracks:
-- | - Frame capture latency
-- | - Screenshot encoding time
-- | - DOM query overhead
-- |
-- | This enables real-time optimization: if frame capture exceeds budget,
-- | the system can reduce quality or skip frames deterministically.
-- |
-- | ## Deterministic Capture
-- |
-- | Same website state + same capture config = same frame sequence.
-- | Agents can share capture data, diff animations algebraically.
type CaptureM (g :: Grade) a = HydrogenM g a

-- | Run a capture computation.
runCaptureM :: forall g a. CaptureM g a -> Effect (HydrogenResult a)
runCaptureM (HydrogenM m) = m

-- | Start a capture session.
-- |
-- | Grade: NetOnly (requires browser connection)
-- |
-- | ## Semantics
-- |
-- | Transitions capture state from Idle → Preparing.
-- | Emits StartCapture command for runtime to:
-- | 1. Navigate to target URL
-- | 2. Wait for page load
-- | 3. Initialize frame buffer
startCaptureM :: CaptureConfig -> CaptureState -> CaptureM NetOnly CaptureResult
startCaptureM config s = HydrogenM (pure
  { result: captureTransition s StartInput
  , grade: emptyGrade { providerCalls = 1 }
  , coeffect: emptyCoEffect
  , provenance: emptyProvenance { providersUsed = ["chrome-devtools-protocol"] }
  })

-- | Capture a single frame.
-- |
-- | Grade: NetOnly (requires screenshot + DOM query)
-- |
-- | ## Timing Budget
-- |
-- | At 60fps: 16.67ms per frame
-- | At 30fps: 33.33ms per frame
-- |
-- | Frame capture includes:
-- | - Page.captureScreenshot (CDP)
-- | - DOM.getDocument + querySelectorAll (CDP)
-- | - getComputedStyle for each tracked element
-- |
-- | Latency is tracked in HydrogenGrade.latencyMs for optimization.
captureFrameM :: Frame -> CaptureState -> CaptureM NetOnly CaptureResult
captureFrameM frame s = HydrogenM (pure
  { result: captureTransition s (FrameInput frame)
  , grade: emptyGrade 
      { providerCalls = 1
      , latencyMs = 16  -- Target frame budget (will be measured at runtime)
      }
  , coeffect: emptyCoEffect
  , provenance: emptyProvenance { providersUsed = ["chrome-devtools-protocol"] }
  })

-- | Process captured frames (delta encoding, SIGIL conversion).
-- |
-- | Grade: Pure (CPU-only, no network)
-- |
-- | ## Processing Steps
-- |
-- | 1. Delta encode frame sequence (temporal compression)
-- | 2. Convert CSS values → Hydrogen Schema atoms (OKLCH, Pixel, etc.)
-- | 3. Generate SIGIL frame descriptors
-- | 4. Compute deterministic UUIDs for each frame
-- |
-- | Output is pure data suitable for serialization and agent sharing.
processCaptureM :: CaptureState -> CaptureM Pure CaptureResult
processCaptureM s = HydrogenM (pure
  { result: captureTransition s StopInput
  , grade: emptyGrade
  , coeffect: emptyCoEffect
  , provenance: emptyProvenance
  })

-- | Get capture progress without effects.
-- |
-- | Grade: Pure
-- |
-- | Returns: 0.0 (not started) to 1.0 (complete)
getCaptureProgress :: CaptureState -> CaptureM Pure Number
getCaptureProgress s = HydrogenM (pure
  { result: captureProgress s
  , grade: emptyGrade
  , coeffect: emptyCoEffect
  , provenance: emptyProvenance
  })
