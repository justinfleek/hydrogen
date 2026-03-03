-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // extension // main
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Entry point for the Foundry browser extension popup.
-- |
-- | Mounts the Halogen popup component to the DOM.

module Main
  ( main
  ) where

import Prelude (Unit, bind, discard, unit)

import Effect (Effect)
import Effect.Class (liftEffect)
import Effect.Console (log)

import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.VDom.Driver (runUI)

import Extension.Popup (component)

-- | Entry point
main :: Effect Unit
main = runHalogenAff do
  liftEffect (log "[Foundry] Popup initializing")
  body <- awaitBody
  _ <- runUI component unit body
  liftEffect (log "[Foundry] Popup mounted")
