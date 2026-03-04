-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // debounce
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Rate limiting configuration atoms.
-- |
-- | Debounce delays execution until after a period of inactivity.
-- | Throttle limits execution to at most once per interval.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.Debounce as Debounce
-- |
-- | searchConfig :: DebounceConfig
-- | searchConfig = Debounce.debounceSearch
-- |
-- | customConfig :: DebounceConfig
-- | customConfig = Debounce.debounceTrailing (Duration.fromMilliseconds 500.0)
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Temporal.Debounce
-- | - Hydrogen.Schema.Temporal.Duration
-- |
-- | ## Dependents
-- | - Input elements with debounced validation
-- | - Scroll-linked animations
-- | - Resize handlers

module Hydrogen.Util.Debounce
  ( module Schema
  ) where

import Hydrogen.Schema.Temporal.Debounce
  ( DebounceConfig
  , debounceConfig
  , debounceTrailing
  , debounceLeading
  , debounceBoth
  , ThrottleConfig
  , throttleConfig
  , throttleLeading
  , throttleTrailing
  , throttleBoth
  , debounceWait
  , debounceIsLeading
  , debounceIsTrailing
  , throttleWait
  , throttleIsLeading
  , throttleIsTrailing
  , isDebounceLeadingOnly
  , isDebounceTrailingOnly
  , isDebounceBothEdges
  , isThrottleLeadingOnly
  , isThrottleTrailingOnly
  , isThrottleBothEdges
  , debounceSearch
  , debounceResize
  , debounceValidation
  , throttleScroll
  , throttleMouseMove
  , throttleApiCall
  ) as Schema
