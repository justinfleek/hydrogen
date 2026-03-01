-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // network // websocket // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Connection State
-- |
-- | Compound state type that combines:
-- | - Connection state machine
-- | - Protocol information
-- | - Connection timing
-- | - Reconnection tracking
-- | - Message statistics

module Hydrogen.Schema.Network.WebSocket.State
  ( -- * Connection State
    ConnectionState
  , initialState
  , connectedState
  , disconnectedState
  , reconnectingState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Network.WebSocket.Types 
  ( WebSocketState(Closed, Open, Connecting)
  , Protocol
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // connection state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete connection state.
-- |
-- | Combines WebSocket state with metadata for UI rendering.
type ConnectionState =
  { state :: WebSocketState
  , protocol :: Maybe Protocol
  , connectedAt :: Maybe Number
  , reconnectAttempt :: Int
  , lastError :: Maybe String
  , messagesSent :: Int
  , messagesReceived :: Int
  }

-- | Initial connection state.
initialState :: ConnectionState
initialState =
  { state: Closed
  , protocol: Nothing
  , connectedAt: Nothing
  , reconnectAttempt: 0
  , lastError: Nothing
  , messagesSent: 0
  , messagesReceived: 0
  }

-- | Connected state with protocol.
connectedState :: Protocol -> Number -> ConnectionState
connectedState proto timestamp =
  { state: Open
  , protocol: Just proto
  , connectedAt: Just timestamp
  , reconnectAttempt: 0
  , lastError: Nothing
  , messagesSent: 0
  , messagesReceived: 0
  }

-- | Disconnected state with optional error.
disconnectedState :: Maybe String -> ConnectionState
disconnectedState err =
  { state: Closed
  , protocol: Nothing
  , connectedAt: Nothing
  , reconnectAttempt: 0
  , lastError: err
  , messagesSent: 0
  , messagesReceived: 0
  }

-- | Reconnecting state.
reconnectingState :: Int -> ConnectionState
reconnectingState attempt =
  { state: Connecting
  , protocol: Nothing
  , connectedAt: Nothing
  , reconnectAttempt: attempt
  , lastError: Nothing
  , messagesSent: 0
  , messagesReceived: 0
  }
