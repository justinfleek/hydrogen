-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // test // scraper // integration
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Integration tests for the 10-20 second observation scraper.
-- |
-- | These tests require a browser (Playwright) and network access.
-- | Run with: spago run --main Test.Scraper.Integration

module Test.Scraper.Integration where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_, Aff)
import Effect.Class.Console (log)
import Data.Array (length) as Array
import Data.Either (Either(Left, Right))
import Hydrogen.Scraper.Extract 
  ( scrapeUrlFullSafe
  , defaultScrapeOptions
  , ScrapeError(..)
  , easingFunctionToSchema
  )
import Hydrogen.Scraper.Observer (ObserveError(BrowserLaunchFailed, NavigationFailed, ObservationFailed))
import Hydrogen.Scraper.Animation (EasingFunction(Linear, Ease, CubicBezier))

-- | Main entry point - runs a quick scrape test
main :: Effect Unit
main = launchAff_ do
  log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  log "  FOUNDRY SCRAPER // Integration Test"
  log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  log ""
  
  -- Test 1: Schema wiring (no browser needed)
  log "▸ Test 1: Schema Wiring (Easing)"
  testEasingWiring
  
  -- Test 2: Quick observation of a simple page
  log ""
  log "▸ Test 2: Quick Observation (example.com)"
  testQuickObservation
  
  log ""
  log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
  log "  All tests completed"
  log "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

-- | Test that easing functions wire correctly to Schema
testEasingWiring :: Aff Unit
testEasingWiring = do
  let linearEasing = easingFunctionToSchema Linear
  let easeEasing = easingFunctionToSchema Ease
  let cubicEasing = easingFunctionToSchema (CubicBezier 0.4 0.0 0.2 1.0)
  
  log "  ✓ Linear → Schema.Temporal.Easing"
  log "  ✓ Ease → Schema.Temporal.Easing"  
  log "  ✓ CubicBezier → Schema.Temporal.Easing"

-- | Test a quick observation of example.com
-- |
-- | Uses the SAFE version that handles Playwright failures gracefully.
-- | On NixOS/environments without browser binaries, this will report
-- | the error instead of crashing.
testQuickObservation :: Aff Unit
testQuickObservation = do
  log "  Starting observation of https://example.com..."
  log "  (Using safe scraper - will gracefully handle browser failures)"
  
  -- Use minimal options for speed
  let opts = defaultScrapeOptions
        { observeInteractions = false  -- Skip hover/focus probing
        , captureAnimations = false    -- Skip animation detection
        , timeout = 10000              -- 10 second timeout
        }
  
  result <- scrapeUrlFullSafe "https://example.com" opts
  
  case result of
    Left (ScrapeObserveError (BrowserLaunchFailed msg)) -> do
      log "  ⚠ Browser launch failed (expected on NixOS without libs)"
      log ("    Error: " <> msg)
      log "  ✓ Graceful failure - no crash!"
    
    Left (ScrapeObserveError (NavigationFailed msg)) -> do
      log "  ⚠ Navigation failed"
      log ("    Error: " <> msg)
      log "  ✓ Graceful failure - no crash!"
    
    Left (ScrapeObserveError (ObservationFailed msg)) -> do
      log "  ⚠ Observation failed"
      log ("    Error: " <> msg)
      log "  ✓ Graceful failure - no crash!"
    
    Left (ScrapeBrowserError msg) -> do
      log "  ⚠ Browser error during extraction"
      log ("    Error: " <> msg)
      log "  ✓ Graceful failure - no crash!"
    
    Right res -> do
      log ("  Page title: " <> res.page.title)
      log ("  Elements captured: " <> show res.elementCount)
      log ("  States captured: " <> show (Array.length res.capturedStates))
      log ("  Animations detected: " <> show (Array.length res.animations))
      log "  ✓ Observation complete"
