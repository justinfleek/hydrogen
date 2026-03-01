-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // network // websocket // reconnect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Reconnection Strategy
-- |
-- | Bounded reconnection handling with:
-- | - Exponential backoff
-- | - Maximum attempt limits
-- | - Delay capping
-- | - Optional jitter

module Hydrogen.Schema.Network.WebSocket.Reconnect
  ( -- * Reconnection Strategy
    ReconnectStrategy
  , reconnectStrategy
  , defaultReconnect
  , noReconnect
  , exponentialBackoff
  , shouldReconnect
  , nextReconnectDelay
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (*)
  , (<)
  , (==)
  , (||)
  , (>)
  )

import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Math.Core (pow)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // reconnection strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reconnection strategy for WebSocket.
type ReconnectStrategy =
  { maxAttempts :: Int           -- ^ Maximum reconnection attempts (0 = infinite)
  , baseDelayMs :: Number        -- ^ Initial delay in milliseconds
  , maxDelayMs :: Number         -- ^ Maximum delay cap
  , attempt :: Int               -- ^ Current attempt number
  , jitter :: Boolean            -- ^ Add random jitter to delays
  }

-- | Create a reconnection strategy.
reconnectStrategy :: Int -> Number -> Number -> ReconnectStrategy
reconnectStrategy maxAttempts baseDelay maxDelay =
  { maxAttempts
  , baseDelayMs: clampNumber 100.0 60000.0 baseDelay
  , maxDelayMs: clampNumber 1000.0 300000.0 maxDelay
  , attempt: 0
  , jitter: true
  }

-- | Default reconnection strategy.
-- |
-- | - 5 attempts maximum
-- | - 1 second base delay
-- | - 30 second maximum delay
-- | - Exponential backoff with jitter
defaultReconnect :: ReconnectStrategy
defaultReconnect = reconnectStrategy 5 1000.0 30000.0

-- | No automatic reconnection.
noReconnect :: ReconnectStrategy
noReconnect =
  { maxAttempts: 0
  , baseDelayMs: 0.0
  , maxDelayMs: 0.0
  , attempt: 0
  , jitter: false
  }

-- | Create exponential backoff strategy.
exponentialBackoff :: Int -> Number -> ReconnectStrategy
exponentialBackoff attempts baseDelay =
  reconnectStrategy attempts baseDelay (baseDelay * 32.0)

-- | Should attempt reconnection?
shouldReconnect :: ReconnectStrategy -> Boolean
shouldReconnect s = 
  s.maxAttempts == 0 || s.attempt < s.maxAttempts

-- | Calculate next reconnection delay.
-- |
-- | Uses exponential backoff: delay = baseDelay * 2^attempt
-- | Capped at maxDelayMs.
nextReconnectDelay :: ReconnectStrategy -> Number
nextReconnectDelay s =
  let
    exponential = s.baseDelayMs * pow 2.0 (intToNumber s.attempt)
  in
    if exponential > s.maxDelayMs then s.maxDelayMs else exponential

-- | Convert an Int to a Number.
foreign import intToNumber :: Int -> Number
