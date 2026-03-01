-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // websocket // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Bounded Value Definitions
-- |
-- | Bounded types for WebSocket schema:
-- | - Close code bounds (RFC 6455)
-- | - Reconnection delay bounds

module Hydrogen.Schema.Network.WebSocket.Bounds
  ( -- * Bounds
    closeCodeBounds
  , reconnectDelayBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Bounded 
  ( IntBounds
  , NumberBounds
  , BoundsBehavior(Clamps)
  , intBounds
  , numberBounds
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for WebSocket close codes [1000, 4999]
-- |
-- | Per RFC 6455:
-- | - 1000-2999: Protocol reserved
-- | - 3000-3999: Library/framework use
-- | - 4000-4999: Application use
closeCodeBounds :: IntBounds
closeCodeBounds = intBounds 1000 4999 Clamps "closeCode"
  "WebSocket close code (1000-4999)"

-- | Bounds for reconnection delay [100, 300000] ms
-- |
-- | - 100ms: Minimum sensible delay
-- | - 300000ms: 5 minute maximum
reconnectDelayBounds :: NumberBounds
reconnectDelayBounds = numberBounds 100.0 300000.0 Clamps "reconnectDelay"
  "Reconnection delay in milliseconds (100-300000)"
