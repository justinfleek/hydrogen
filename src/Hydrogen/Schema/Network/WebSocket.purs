-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // network // websocket
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Schema — Pure data types for bidirectional communication.
-- |
-- | Models the WebSocket protocol state machine as algebraic data types.
-- | The runtime interprets these types to manage actual connections.
-- |
-- | ## Design Philosophy
-- |
-- | WebSocket at billion-agent scale requires:
-- | - Explicit state machine (no implicit connection states)
-- | - Type-safe message handling (text vs binary)
-- | - Bounded reconnection strategies
-- | - Deterministic close codes
-- |
-- | ## State Machine
-- |
-- | ```
-- |   ┌──────────┐
-- |   │Connecting│
-- |   └────┬─────┘
-- |        │ connected
-- |        ▼
-- |   ┌────────┐  close requested
-- |   │  Open  │─────────────────┐
-- |   └────┬───┘                 │
-- |        │ close received      ▼
-- |        │                ┌─────────┐
-- |        └───────────────►│ Closing │
-- |                         └────┬────┘
-- |                              │ closed
-- |                              ▼
-- |                         ┌────────┐
-- |                         │ Closed │
-- |                         └────────┘
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Network.WebSocket as WS
-- |
-- | config = WS.config (WS.wsURL "wss://api.example.com/ws")
-- |   { protocols = ["v1", "v2"]
-- |   , reconnect = Just WS.defaultReconnect
-- |   }
-- |
-- | -- Handle incoming messages
-- | case msg of
-- |   WS.TextMessage text -> handleText text
-- |   WS.BinaryMessage bytes -> handleBinary bytes
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from:
-- | - Types: Core types (WebSocketState, WebSocketURL, Protocol, Bytes)
-- | - Messages: Message types and operations
-- | - Close: Close codes and events (RFC 6455)
-- | - Reconnect: Reconnection strategy
-- | - Events: WebSocket lifecycle events
-- | - Config: Connection configuration
-- | - State: Connection state compound
-- | - Bounds: Bounded value definitions

module Hydrogen.Schema.Network.WebSocket
  ( module Types
  , module Messages
  , module Close
  , module Reconnect
  , module Events
  , module Config
  , module State
  , module Bounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Network.WebSocket.Types 
  ( BinaryType(ArrayBuffer, Blob)
  , Bytes
  , Protocol
  , WebSocketState(Connecting, Open, Closing, Closed)
  , WebSocketURL
  , bytes
  , bytesFromArray
  , bytesLength
  , canReceive
  , canSend
  , emptyBytes
  , isClosed
  , isClosing
  , isConnecting
  , isOpen
  , isSecure
  , protocol
  , unwrapBytes
  , unwrapProtocol
  , unwrapWebSocketURL
  , wsURL
  , wssURL
  ) as Types

import Hydrogen.Schema.Network.WebSocket.Messages 
  ( WebSocketMessage(TextMessage, BinaryMessage)
  , binaryMessage
  , isBinaryMessage
  , isTextMessage
  , messageSize
  , textMessage
  ) as Messages

import Hydrogen.Schema.Network.WebSocket.Close 
  ( CloseCode
  , CloseEvent
  , closeAbnormal
  , closeCode
  , closeEvent
  , closeGoingAway
  , closeInternalError
  , closeInvalidPayload
  , closeMessageTooBig
  , closeMissingExtension
  , closeNoStatus
  , closeNormal
  , closePolicyViolation
  , closeProtocolError
  , closeReason
  , closeServiceRestart
  , closeTryAgainLater
  , closeUnsupportedData
  , isErrorClose
  , isNormalClose
  , unwrapCloseCode
  , wasClean
  ) as Close

import Hydrogen.Schema.Network.WebSocket.Reconnect 
  ( ReconnectStrategy
  , defaultReconnect
  , exponentialBackoff
  , nextReconnectDelay
  , noReconnect
  , reconnectStrategy
  , shouldReconnect
  ) as Reconnect

import Hydrogen.Schema.Network.WebSocket.Events 
  ( WebSocketEvent(WSConnecting, WSOpen, WSMessage, WSError, WSClose, WSReconnecting)
  ) as Events

import Hydrogen.Schema.Network.WebSocket.Config 
  ( WebSocketConfig
  , config
  , defaultConfig
  , withProtocols
  , withReconnect
  ) as Config

import Hydrogen.Schema.Network.WebSocket.State 
  ( ConnectionState
  , connectedState
  , disconnectedState
  , initialState
  , reconnectingState
  ) as State

import Hydrogen.Schema.Network.WebSocket.Bounds 
  ( closeCodeBounds
  , reconnectDelayBounds
  ) as Bounds
