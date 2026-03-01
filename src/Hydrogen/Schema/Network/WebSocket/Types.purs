-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // network // websocket // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WebSocket Core Types
-- |
-- | Foundational types for WebSocket communication:
-- | - Connection state machine
-- | - WebSocket URLs (ws:// and wss://)
-- | - Subprotocol identifiers
-- | - Binary data representation
-- | - Binary type selection

module Hydrogen.Schema.Network.WebSocket.Types
  ( -- * WebSocket State Machine
    WebSocketState(..)
  , isConnecting
  , isOpen
  , isClosing
  , isClosed
  , canSend
  , canReceive
  
  -- * WebSocket URL
  , WebSocketURL
  , wsURL
  , wssURL
  , unwrapWebSocketURL
  , isSecure
  
  -- * Subprotocols
  , Protocol
  , protocol
  , unwrapProtocol
  
  -- * Binary Type
  , BinaryType(..)
  
  -- * Binary Data
  , Bytes
  , bytes
  , bytesFromArray
  , unwrapBytes
  , bytesLength
  , emptyBytes
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , show
  , (<>)
  , (<=)
  )

import Data.Array (length) as Array
import Data.String.CodeUnits (length) as String
import Hydrogen.Schema.Bounded (clampInt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // websocket state machine
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket connection state machine.
-- |
-- | Mirrors the W3C WebSocket readyState values but as proper ADT.
data WebSocketState
  = Connecting  -- ^ Connection is being established (readyState 0)
  | Open        -- ^ Connection is open and ready (readyState 1)
  | Closing     -- ^ Connection is closing (readyState 2)
  | Closed      -- ^ Connection is closed (readyState 3)

derive instance eqWebSocketState :: Eq WebSocketState
derive instance ordWebSocketState :: Ord WebSocketState

instance showWebSocketState :: Show WebSocketState where
  show Connecting = "connecting"
  show Open = "open"
  show Closing = "closing"
  show Closed = "closed"

-- | Is the connection being established?
isConnecting :: WebSocketState -> Boolean
isConnecting Connecting = true
isConnecting _ = false

-- | Is the connection open and ready?
isOpen :: WebSocketState -> Boolean
isOpen Open = true
isOpen _ = false

-- | Is the connection closing?
isClosing :: WebSocketState -> Boolean
isClosing Closing = true
isClosing _ = false

-- | Is the connection closed?
isClosed :: WebSocketState -> Boolean
isClosed Closed = true
isClosed _ = false

-- | Can messages be sent in this state?
canSend :: WebSocketState -> Boolean
canSend Open = true
canSend _ = false

-- | Can messages be received in this state?
canReceive :: WebSocketState -> Boolean
canReceive Open = true
canReceive Closing = true  -- May still receive final messages
canReceive _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // websocket url
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket URL (ws:// or wss://)
newtype WebSocketURL = WebSocketURL String

derive instance eqWebSocketURL :: Eq WebSocketURL
derive instance ordWebSocketURL :: Ord WebSocketURL

instance showWebSocketURL :: Show WebSocketURL where
  show (WebSocketURL u) = u

-- | Create a non-secure WebSocket URL (ws://)
wsURL :: String -> WebSocketURL
wsURL host = WebSocketURL ("ws://" <> host)

-- | Create a secure WebSocket URL (wss://)
wssURL :: String -> WebSocketURL
wssURL host = WebSocketURL ("wss://" <> host)

-- | Extract the URL string.
unwrapWebSocketURL :: WebSocketURL -> String
unwrapWebSocketURL (WebSocketURL u) = u

-- | Is this a secure WebSocket (wss://)?
isSecure :: WebSocketURL -> Boolean
isSecure (WebSocketURL u) = startsWith "wss://" u
  where
  startsWith :: String -> String -> Boolean
  startsWith prefix s = String.length prefix <= String.length s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // protocols
-- ═════════════════════════════════════════════════════════════════════════════

-- | WebSocket subprotocol identifier.
-- |
-- | Used during handshake to negotiate application-level protocol.
newtype Protocol = Protocol String

derive instance eqProtocol :: Eq Protocol
derive instance ordProtocol :: Ord Protocol

instance showProtocol :: Show Protocol where
  show (Protocol p) = p

-- | Create a protocol identifier.
protocol :: String -> Protocol
protocol = Protocol

-- | Extract protocol string.
unwrapProtocol :: Protocol -> String
unwrapProtocol (Protocol p) = p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // binary type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Binary data format for received messages.
data BinaryType
  = ArrayBuffer   -- ^ Receive as ArrayBuffer
  | Blob          -- ^ Receive as Blob

derive instance eqBinaryType :: Eq BinaryType

instance showBinaryType :: Show BinaryType where
  show ArrayBuffer = "arraybuffer"
  show Blob = "blob"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // binary data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Binary data representation.
-- |
-- | Wraps an array of byte values [0-255].
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes
derive instance ordBytes :: Ord Bytes

instance showBytes :: Show Bytes where
  show b = "Bytes(" <> show (bytesLength b) <> ")"

-- | Create Bytes from a single byte value.
bytes :: Int -> Bytes
bytes b = Bytes [clampInt 0 255 b]

-- | Create Bytes from an array of byte values.
-- |
-- | Each value is clamped to [0, 255].
bytesFromArray :: Array Int -> Bytes
bytesFromArray arr = Bytes (clampBytes arr)
  where
  clampBytes :: Array Int -> Array Int
  clampBytes = map (clampInt 0 255)

-- | Extract the byte array.
unwrapBytes :: Bytes -> Array Int
unwrapBytes (Bytes arr) = arr

-- | Get the byte length.
bytesLength :: Bytes -> Int
bytesLength (Bytes arr) = Array.length arr

-- | Empty byte array.
emptyBytes :: Bytes
emptyBytes = Bytes []
