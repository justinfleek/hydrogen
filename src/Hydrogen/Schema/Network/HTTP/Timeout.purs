-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                    // timeout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Request Timeout — Bounded timeout values for HTTP requests.
-- |
-- | Bounded to [0, 300000] ms (0 to 5 minutes). A timeout of 0 means
-- | "use default" rather than "instant timeout".

module Hydrogen.Schema.Network.HTTP.Timeout
  ( Timeout
  , timeoutMs
  , timeoutSeconds
  , unwrapTimeout
  , defaultTimeout
  , noTimeout
  , isExpired
  , timeoutBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (>=)
  , (>)
  , (&&)
  , (*)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // timeout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Request timeout in milliseconds.
-- |
-- | Bounded to [0, 300000] (0 to 5 minutes). A timeout of 0 means
-- | "use default" rather than "instant timeout".
newtype Timeout = Timeout Number

derive instance eqTimeout :: Eq Timeout
derive instance ordTimeout :: Ord Timeout

instance showTimeout :: Show Timeout where
  show (Timeout ms) = show ms <> "ms"

-- | Create a timeout from milliseconds.
-- |
-- | Clamps to [0, 300000] (5 minute maximum).
timeoutMs :: Number -> Timeout
timeoutMs ms = Timeout (Bounded.clampNumber 0.0 300000.0 ms)

-- | Create a timeout from seconds.
-- |
-- | Converts to milliseconds, then clamps.
timeoutSeconds :: Number -> Timeout
timeoutSeconds s = timeoutMs (s * 1000.0)

-- | Extract timeout in milliseconds.
unwrapTimeout :: Timeout -> Number
unwrapTimeout (Timeout ms) = ms

-- | Default timeout: 30 seconds.
-- |
-- | Standard timeout for most HTTP requests.
defaultTimeout :: Timeout
defaultTimeout = Timeout 30000.0

-- | No timeout (use system default).
-- |
-- | Represented as 0ms, meaning "defer to runtime default".
noTimeout :: Timeout
noTimeout = Timeout 0.0

-- | Check if elapsed time exceeds timeout.
isExpired :: Timeout -> Number -> Boolean
isExpired (Timeout limit) elapsed = 
  limit > 0.0 && elapsed >= limit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for request timeout [0, 300000] ms
-- |
-- | - 0ms: Use system default
-- | - 300000ms: 5 minute maximum (reasonable upper limit)
timeoutBounds :: Bounded.NumberBounds
timeoutBounds = Bounded.numberBounds 0.0 300000.0 Bounded.Clamps "timeout"
  "HTTP request timeout in milliseconds (0-300000, 0 = default)"
