-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // network // websocket // messages
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Messages
-- |
-- | Message types for WebSocket communication:
-- | - Text messages (UTF-8 encoded)
-- | - Binary messages (raw bytes)

module Hydrogen.Schema.Network.WebSocket.Messages
  ( -- * Message Types
    WebSocketMessage(..)
  , textMessage
  , binaryMessage
  , messageSize
  , isTextMessage
  , isBinaryMessage
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

import Hydrogen.Schema.Network.WebSocket.Types (Bytes, bytesLength)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket message types.
-- |
-- | WebSocket supports two frame types: text (UTF-8) and binary.
data WebSocketMessage
  = TextMessage String    -- ^ UTF-8 text frame
  | BinaryMessage Bytes   -- ^ Binary data frame

derive instance eqWebSocketMessage :: Eq WebSocketMessage

instance showWebSocketMessage :: Show WebSocketMessage where
  show (TextMessage t) = "TextMessage(" <> show (stringLength t) <> " chars)"
  show (BinaryMessage b) = "BinaryMessage(" <> show (bytesLength b) <> " bytes)"

-- | Create a text message.
textMessage :: String -> WebSocketMessage
textMessage = TextMessage

-- | Create a binary message.
binaryMessage :: Bytes -> WebSocketMessage
binaryMessage = BinaryMessage

-- | Get approximate message size in bytes.
messageSize :: WebSocketMessage -> Int
messageSize (TextMessage t) = stringLength t  -- Approximation (UTF-8 varies)
messageSize (BinaryMessage b) = bytesLength b

-- | Is this a text message?
isTextMessage :: WebSocketMessage -> Boolean
isTextMessage (TextMessage _) = true
isTextMessage _ = false

-- | Is this a binary message?
isBinaryMessage :: WebSocketMessage -> Boolean
isBinaryMessage (BinaryMessage _) = true
isBinaryMessage _ = false

-- | Get the length of a string.
foreign import stringLength :: String -> Int
