-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // websocket // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Configuration
-- |
-- | Configuration types for WebSocket connections:
-- | - URL and protocol selection
-- | - Reconnection strategy
-- | - Binary type preference

module Hydrogen.Schema.Network.WebSocket.Config
  ( -- * WebSocket Configuration
    WebSocketConfig
  , config
  , defaultConfig
  , withProtocols
  , withReconnect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Network.WebSocket.Types (WebSocketURL, Protocol, BinaryType(ArrayBuffer))
import Hydrogen.Schema.Network.WebSocket.Reconnect (ReconnectStrategy, defaultReconnect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // websocket config
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket connection configuration.
type WebSocketConfig =
  { url :: WebSocketURL
  , protocols :: Array Protocol
  , reconnect :: Maybe ReconnectStrategy
  , binaryType :: BinaryType
  }

-- | Create a WebSocket configuration.
config :: WebSocketURL -> WebSocketConfig
config wsUrl =
  { url: wsUrl
  , protocols: []
  , reconnect: Nothing
  , binaryType: ArrayBuffer
  }

-- | Default configuration for a URL.
defaultConfig :: WebSocketURL -> WebSocketConfig
defaultConfig wsUrl =
  { url: wsUrl
  , protocols: []
  , reconnect: Just defaultReconnect
  , binaryType: ArrayBuffer
  }

-- | Add protocols to configuration.
withProtocols :: Array Protocol -> WebSocketConfig -> WebSocketConfig
withProtocols protocols cfg = cfg { protocols = protocols }

-- | Set reconnection strategy.
withReconnect :: ReconnectStrategy -> WebSocketConfig -> WebSocketConfig
withReconnect strategy cfg = cfg { reconnect = Just strategy }
