-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // scraper // main
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand Scraper Dashboard entry point.
-- |
-- | Initializes the WebGPU context, establishes ZMQ connection to Haskell
-- | backend, and mounts the comparison dashboard.
-- |
-- | DEPENDENCIES:
-- |   - Scraper.Dashboard.App (Halogen application)
-- |   - Scraper.Protocol.ZMQ (backend communication)
-- |
-- | DEPENDENTS:
-- |   - HTML entry point (index.html)

module Scraper.Main
  ( main
  ) where

import Prelude (Unit, bind, discard, pure)

import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log)

import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)

import Scraper.Dashboard.App (component)

-- | Application entry point.
-- |
-- | Sequence:
-- |   1. Log initialization
-- |   2. Await DOM body
-- |   3. Mount Halogen component
main :: Effect Unit
main = runHalogenAff do
  liftEffect (log "foundry-scraper: initializing")
  body <- awaitBody
  runUI component unit body
  liftEffect (log "foundry-scraper: mounted")
