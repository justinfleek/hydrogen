-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // websocket // events
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Events
-- |
-- | Lifecycle events for WebSocket connections:
-- | - Connection states (connecting, open, closing, closed)
-- | - Message reception
-- | - Error handling
-- | - Reconnection tracking

module Hydrogen.Schema.Network.WebSocket.Events
  ( -- * WebSocket Events
    WebSocketEvent(WSConnecting, WSOpen, WSMessage, WSError, WSClose, WSReconnecting)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Network.WebSocket.Types (Protocol)
import Hydrogen.Schema.Network.WebSocket.Messages (WebSocketMessage)
import Hydrogen.Schema.Network.WebSocket.Close (CloseEvent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // websocket events
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket lifecycle events.
data WebSocketEvent
  = WSConnecting                    -- ^ Connection initiated
  | WSOpen Protocol                 -- ^ Connection established (with selected protocol)
  | WSMessage WebSocketMessage      -- ^ Message received
  | WSError String                  -- ^ Error occurred
  | WSClose CloseEvent              -- ^ Connection closed
  | WSReconnecting Int              -- ^ Attempting reconnection (attempt number)

derive instance eqWebSocketEvent :: Eq WebSocketEvent

instance showWebSocketEvent :: Show WebSocketEvent where
  show WSConnecting = "WSConnecting"
  show (WSOpen p) = "WSOpen(" <> show p <> ")"
  show (WSMessage m) = "WSMessage(" <> show m <> ")"
  show (WSError e) = "WSError(" <> e <> ")"
  show (WSClose c) = "WSClose(" <> show c.code <> ")"
  show (WSReconnecting n) = "WSReconnecting(" <> show n <> ")"
