-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // temporal // debounce
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Debounce and Throttle — Rate-limiting temporal configuration atoms.
-- |
-- | ## Debounce
-- |
-- | Debouncing delays execution until after a period of inactivity:
-- | - **leading: false, trailing: true** (default): Execute after silence
-- | - **leading: true, trailing: false**: Execute immediately, ignore subsequent
-- | - **leading: true, trailing: true**: Execute on both edges
-- |
-- | Use cases:
-- | - Search input (wait for user to stop typing)
-- | - Window resize handlers
-- | - Form validation
-- |
-- | ## Throttle
-- |
-- | Throttling limits execution to at most once per interval:
-- | - Scroll handlers
-- | - Mouse move events
-- | - Rate-limited API calls
-- |
-- | ## Design Philosophy
-- |
-- | Both configurations use Duration for wait time, ensuring type-safe
-- | temporal semantics. The leading/trailing flags determine edge behavior
-- | without ambiguity.
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Temporal.Duration (wait period)
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Event handlers in Hydrogen.Runtime
-- | - Input validation molecules
-- | - Scroll-linked animation triggers

module Hydrogen.Schema.Temporal.Debounce
  ( -- * Debounce Configuration
    DebounceConfig
  , debounceConfig
  , debounceTrailing
  , debounceLeading
  , debounceBoth
  
  -- * Throttle Configuration
  , ThrottleConfig
  , throttleConfig
  , throttleLeading
  , throttleTrailing
  , throttleBoth
  
  -- * Accessors
  , debounceWait
  , debounceIsLeading
  , debounceIsTrailing
  , throttleWait
  , throttleIsLeading
  , throttleIsTrailing
  
  -- * Predicates
  , isDebounceLeadingOnly
  , isDebounceTrailingOnly
  , isDebounceBothEdges
  , isThrottleLeadingOnly
  , isThrottleTrailingOnly
  , isThrottleBothEdges
  
  -- * Common Presets
  , debounceSearch
  , debounceResize
  , debounceValidation
  , throttleScroll
  , throttleMouseMove
  , throttleApiCall
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( not
  , (&&)
  )

import Hydrogen.Schema.Temporal.Duration (Duration)
import Hydrogen.Schema.Temporal.Duration (fromMilliseconds) as Duration

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // debounce // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for debounced execution.
-- |
-- | Debouncing delays function execution until after a period of inactivity.
-- | The leading and trailing flags control when execution occurs:
-- |
-- | - **leading: false, trailing: true**: Default. Execute after silence.
-- | - **leading: true, trailing: false**: Execute immediately, ignore rest.
-- | - **leading: true, trailing: true**: Execute on both edges.
-- | - **leading: false, trailing: false**: Invalid (no execution). Treated as trailing.
-- |
-- | ## Invariants
-- |
-- | At least one of leading or trailing must be true. If both are false,
-- | the configuration is normalized to trailing: true.
type DebounceConfig =
  { wait :: Duration
  , leading :: Boolean
  , trailing :: Boolean
  }

-- | Create a debounce configuration with explicit edge behavior.
-- |
-- | If both leading and trailing are false, defaults to trailing: true.
debounceConfig :: Duration -> Boolean -> Boolean -> DebounceConfig
debounceConfig w l t =
  { wait: w
  , leading: l
  , trailing: if not l && not t then true else t
  }

-- | Create trailing-edge debounce (most common).
-- |
-- | Executes after the wait period with no new calls.
-- | Classic use: search-as-you-type.
debounceTrailing :: Duration -> DebounceConfig
debounceTrailing w = debounceConfig w false true

-- | Create leading-edge debounce.
-- |
-- | Executes immediately on first call, ignores subsequent calls until silence.
-- | Use: button click handlers to prevent double-submission.
debounceLeading :: Duration -> DebounceConfig
debounceLeading w = debounceConfig w true false

-- | Create both-edges debounce.
-- |
-- | Executes immediately AND after silence ends.
-- | Use: real-time feedback with final confirmation.
debounceBoth :: Duration -> DebounceConfig
debounceBoth w = debounceConfig w true true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // throttle // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for throttled execution.
-- |
-- | Throttling limits execution to at most once per interval.
-- | The leading and trailing flags control timing:
-- |
-- | - **leading: true, trailing: true**: Default. Execute on both edges.
-- | - **leading: true, trailing: false**: Execute only at start of interval.
-- | - **leading: false, trailing: true**: Execute only at end of interval.
-- |
-- | ## Invariants
-- |
-- | At least one of leading or trailing must be true. If both are false,
-- | the configuration is normalized to leading: true.
type ThrottleConfig =
  { wait :: Duration
  , leading :: Boolean
  , trailing :: Boolean
  }

-- | Create a throttle configuration with explicit edge behavior.
-- |
-- | If both leading and trailing are false, defaults to leading: true.
throttleConfig :: Duration -> Boolean -> Boolean -> ThrottleConfig
throttleConfig w l t =
  { wait: w
  , leading: if not l && not t then true else l
  , trailing: t
  }

-- | Create leading-edge throttle.
-- |
-- | Executes immediately, then ignores calls for wait duration.
-- | Use: immediate response with rate limiting.
throttleLeading :: Duration -> ThrottleConfig
throttleLeading w = throttleConfig w true false

-- | Create trailing-edge throttle.
-- |
-- | Waits for interval to complete before executing.
-- | Use: batch operations at end of interval.
throttleTrailing :: Duration -> ThrottleConfig
throttleTrailing w = throttleConfig w false true

-- | Create both-edges throttle (most common).
-- |
-- | Executes immediately AND at end of interval if calls occurred.
-- | Use: scroll handlers needing immediate + final update.
throttleBoth :: Duration -> ThrottleConfig
throttleBoth w = throttleConfig w true true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get debounce wait duration.
debounceWait :: DebounceConfig -> Duration
debounceWait cfg = cfg.wait

-- | Is debounce leading-edge enabled?
debounceIsLeading :: DebounceConfig -> Boolean
debounceIsLeading cfg = cfg.leading

-- | Is debounce trailing-edge enabled?
debounceIsTrailing :: DebounceConfig -> Boolean
debounceIsTrailing cfg = cfg.trailing

-- | Get throttle wait duration.
throttleWait :: ThrottleConfig -> Duration
throttleWait cfg = cfg.wait

-- | Is throttle leading-edge enabled?
throttleIsLeading :: ThrottleConfig -> Boolean
throttleIsLeading cfg = cfg.leading

-- | Is throttle trailing-edge enabled?
throttleIsTrailing :: ThrottleConfig -> Boolean
throttleIsTrailing cfg = cfg.trailing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is debounce configured for leading-edge only?
isDebounceLeadingOnly :: DebounceConfig -> Boolean
isDebounceLeadingOnly cfg = cfg.leading && not cfg.trailing

-- | Is debounce configured for trailing-edge only?
isDebounceTrailingOnly :: DebounceConfig -> Boolean
isDebounceTrailingOnly cfg = not cfg.leading && cfg.trailing

-- | Is debounce configured for both edges?
isDebounceBothEdges :: DebounceConfig -> Boolean
isDebounceBothEdges cfg = cfg.leading && cfg.trailing

-- | Is throttle configured for leading-edge only?
isThrottleLeadingOnly :: ThrottleConfig -> Boolean
isThrottleLeadingOnly cfg = cfg.leading && not cfg.trailing

-- | Is throttle configured for trailing-edge only?
isThrottleTrailingOnly :: ThrottleConfig -> Boolean
isThrottleTrailingOnly cfg = not cfg.leading && cfg.trailing

-- | Is throttle configured for both edges?
isThrottleBothEdges :: ThrottleConfig -> Boolean
isThrottleBothEdges cfg = cfg.leading && cfg.trailing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Debounce preset for search input (300ms, trailing).
-- |
-- | Wait for user to stop typing before executing search.
debounceSearch :: DebounceConfig
debounceSearch = debounceTrailing (Duration.fromMilliseconds 300.0)

-- | Debounce preset for window resize (150ms, trailing).
-- |
-- | Recalculate layout after resize stabilizes.
debounceResize :: DebounceConfig
debounceResize = debounceTrailing (Duration.fromMilliseconds 150.0)

-- | Debounce preset for form validation (500ms, trailing).
-- |
-- | Validate after user pauses input.
debounceValidation :: DebounceConfig
debounceValidation = debounceTrailing (Duration.fromMilliseconds 500.0)

-- | Throttle preset for scroll handlers (16ms, both edges).
-- |
-- | ~60fps update rate for smooth scroll response.
throttleScroll :: ThrottleConfig
throttleScroll = throttleBoth (Duration.fromMilliseconds 16.0)

-- | Throttle preset for mouse move handlers (32ms, both edges).
-- |
-- | ~30fps update rate for mouse tracking.
throttleMouseMove :: ThrottleConfig
throttleMouseMove = throttleBoth (Duration.fromMilliseconds 32.0)

-- | Throttle preset for API calls (1000ms, leading).
-- |
-- | Allow immediate call, then enforce cooldown.
throttleApiCall :: ThrottleConfig
throttleApiCall = throttleLeading (Duration.fromMilliseconds 1000.0)
