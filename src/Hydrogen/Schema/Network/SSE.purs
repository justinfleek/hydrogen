-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // sse
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Server-Sent Events Schema — Pure data types for server push streams.
-- |
-- | Models the EventSource API state machine as algebraic data types.
-- | SSE provides one-way server-to-client streaming over HTTP.
-- |
-- | ## Design Philosophy
-- |
-- | SSE at billion-agent scale requires:
-- | - Explicit connection states
-- | - Typed event handling
-- | - Automatic reconnection with last-event-id
-- | - Bounded retry intervals
-- |
-- | ## SSE vs WebSocket
-- |
-- | SSE is simpler than WebSocket when you only need server-to-client push:
-- | - Built on standard HTTP (works with proxies, load balancers)
-- | - Automatic reconnection with event ID tracking
-- | - Text-only (no binary support)
-- | - One-way: server pushes to client
-- |
-- | ## Protocol Format
-- |
-- | SSE messages are text with specific format:
-- | ```
-- | event: message-type
-- | data: payload line 1
-- | data: payload line 2
-- | id: event-id
-- |
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Network.SSE as SSE
-- |
-- | config = SSE.config (SSE.sseURL "https://api.example.com/events")
-- |   { withCredentials = true }
-- |
-- | case event of
-- |   SSE.SSEMessage e -> handleMessage e
-- |   SSE.SSEError err -> handleError err
-- |   SSE.SSEOpen -> handleOpen
-- | ```

module Hydrogen.Schema.Network.SSE
  ( -- * SSE State Machine
    SSEState(..)
  , isSSEConnecting
  , isSSEOpen
  , isSSEClosed
  , canReceiveSSE
  
  -- * SSE URL
  , SSEURL
  , sseURL
  , unwrapSSEURL
  
  -- * SSE Configuration
  , SSEConfig
  , config
  , defaultConfig
  , withCredentials
  , withRetry
  
  -- * Event Types
  , EventType
  , eventType
  , unwrapEventType
  , defaultEventType
  , isDefaultType
  
  -- * Event ID
  , EventId
  , eventId
  , unwrapEventId
  , noEventId
  , hasEventId
  
  -- * SSE Event
  , SSEEvent
  , sseEvent
  , eventData
  , eventLines
  , eventTypeOf
  , eventIdOf
  
  -- * SSE Result Events
  , SSEResult(..)
  , isSSEMessage
  , isSSEError
  , isSSEOpenEvent
  
  -- * Retry Interval
  , RetryInterval
  , retryMs
  , unwrapRetry
  , defaultRetry
  
  -- * Connection State (Compound)
  , SSEConnectionState
  , initialSSEState
  , connectedSSEState
  , disconnectedSSEState
  , lastEventId
  , eventCount
  
  -- * Bounds
  , retryBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.String (joinWith) as String
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sse state machine
-- ═════════════════════════════════════════════════════════════════════════════

-- | Server-Sent Events connection state.
-- |
-- | Mirrors the EventSource readyState values.
data SSEState
  = SSEConnecting   -- ^ Connection is being established (readyState 0)
  | SSEOpen         -- ^ Connection is open (readyState 1)
  | SSEClosed       -- ^ Connection is closed (readyState 2)

derive instance eqSSEState :: Eq SSEState
derive instance ordSSEState :: Ord SSEState

instance showSSEState :: Show SSEState where
  show SSEConnecting = "connecting"
  show SSEOpen = "open"
  show SSEClosed = "closed"

-- | Is the connection being established?
isSSEConnecting :: SSEState -> Boolean
isSSEConnecting SSEConnecting = true
isSSEConnecting _ = false

-- | Is the connection open?
isSSEOpen :: SSEState -> Boolean
isSSEOpen SSEOpen = true
isSSEOpen _ = false

-- | Is the connection closed?
isSSEClosed :: SSEState -> Boolean
isSSEClosed SSEClosed = true
isSSEClosed _ = false

-- | Can events be received?
canReceiveSSE :: SSEState -> Boolean
canReceiveSSE SSEOpen = true
canReceiveSSE _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // sse url
-- ═════════════════════════════════════════════════════════════════════════════

-- | Server-Sent Events endpoint URL.
-- |
-- | Must be an HTTP(S) URL that returns text/event-stream content type.
newtype SSEURL = SSEURL String

derive instance eqSSEURL :: Eq SSEURL
derive instance ordSSEURL :: Ord SSEURL

instance showSSEURL :: Show SSEURL where
  show (SSEURL u) = u

-- | Create an SSE URL.
sseURL :: String -> SSEURL
sseURL = SSEURL

-- | Extract the URL string.
unwrapSSEURL :: SSEURL -> String
unwrapSSEURL (SSEURL u) = u

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // sse config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Server-Sent Events configuration.
type SSEConfig =
  { url :: SSEURL
  , withCredentials :: Boolean    -- ^ Include cookies in CORS requests
  , retryInterval :: RetryInterval
  , lastEventId :: Maybe EventId  -- ^ Resume from this event
  }

-- | Create SSE configuration.
config :: SSEURL -> SSEConfig
config sseUrl =
  { url: sseUrl
  , withCredentials: false
  , retryInterval: defaultRetry
  , lastEventId: Nothing
  }

-- | Default configuration.
defaultConfig :: SSEURL -> SSEConfig
defaultConfig = config

-- | Set credentials flag for CORS.
withCredentials :: Boolean -> SSEConfig -> SSEConfig
withCredentials creds cfg = cfg { withCredentials = creds }

-- | Set retry interval.
withRetry :: RetryInterval -> SSEConfig -> SSEConfig
withRetry interval cfg = cfg { retryInterval = interval }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // event types
-- ═════════════════════════════════════════════════════════════════════════════

-- | SSE event type (the "event:" field).
-- |
-- | Defaults to "message" if not specified in the stream.
newtype EventType = EventType String

derive instance eqEventType :: Eq EventType
derive instance ordEventType :: Ord EventType

instance showEventType :: Show EventType where
  show (EventType t) = t

-- | Create an event type.
eventType :: String -> EventType
eventType = EventType

-- | Extract event type string.
unwrapEventType :: EventType -> String
unwrapEventType (EventType t) = t

-- | Default event type ("message").
defaultEventType :: EventType
defaultEventType = EventType "message"

-- | Is this the default event type?
isDefaultType :: EventType -> Boolean
isDefaultType (EventType t) = t == "message"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // event id
-- ═════════════════════════════════════════════════════════════════════════════

-- | SSE event identifier (the "id:" field).
-- |
-- | Used for resuming streams after reconnection.
newtype EventId = EventId (Maybe String)

derive instance eqEventId :: Eq EventId
derive instance ordEventId :: Ord EventId

instance showEventId :: Show EventId where
  show (EventId (Just id)) = id
  show (EventId Nothing) = "(no id)"

-- | Create an event ID.
eventId :: String -> EventId
eventId id = EventId (Just id)

-- | Extract event ID string.
unwrapEventId :: EventId -> Maybe String
unwrapEventId (EventId id) = id

-- | No event ID.
noEventId :: EventId
noEventId = EventId Nothing

-- | Does this event have an ID?
hasEventId :: EventId -> Boolean
hasEventId (EventId id) = isJust id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sse event
-- ═════════════════════════════════════════════════════════════════════════════

-- | Server-Sent Event data.
-- |
-- | Represents a complete event from the stream.
type SSEEvent =
  { eventType :: EventType
  , data :: Array String    -- ^ Data lines (multiple "data:" fields)
  , id :: EventId
  , origin :: String        -- ^ Origin URL of the event source
  }

-- | Create an SSE event.
sseEvent :: EventType -> Array String -> EventId -> String -> SSEEvent
sseEvent evtType dataLines evtId origin =
  { eventType: evtType
  , data: dataLines
  , id: evtId
  , origin
  }

-- | Get event data as single string (lines joined with newlines).
eventData :: SSEEvent -> String
eventData e = String.joinWith "\n" e.data

-- | Get individual data lines.
eventLines :: SSEEvent -> Array String
eventLines e = e.data

-- | Get the event type.
eventTypeOf :: SSEEvent -> EventType
eventTypeOf e = e.eventType

-- | Get the event ID.
eventIdOf :: SSEEvent -> EventId
eventIdOf e = e.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // sse result events
-- ═════════════════════════════════════════════════════════════════════════════

-- | SSE lifecycle events.
data SSEResult
  = SSEMessage SSEEvent    -- ^ Event received
  | SSEError String        -- ^ Error occurred (connection will retry)
  | SSEOpenEvent           -- ^ Connection opened

derive instance eqSSEResult :: Eq SSEResult

instance showSSEResult :: Show SSEResult where
  show (SSEMessage e) = "SSEMessage(" <> show e.eventType <> ")"
  show (SSEError err) = "SSEError(" <> err <> ")"
  show SSEOpenEvent = "SSEOpen"

-- | Is this a message event?
isSSEMessage :: SSEResult -> Boolean
isSSEMessage (SSEMessage _) = true
isSSEMessage _ = false

-- | Is this an error event?
isSSEError :: SSEResult -> Boolean
isSSEError (SSEError _) = true
isSSEError _ = false

-- | Is this an open event?
isSSEOpenEvent :: SSEResult -> Boolean
isSSEOpenEvent SSEOpenEvent = true
isSSEOpenEvent _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // retry interval
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reconnection retry interval in milliseconds.
-- |
-- | Can be set by server via "retry:" field or configured client-side.
-- | Bounded to [1000, 60000] (1 second to 1 minute).
newtype RetryInterval = RetryInterval Number

derive instance eqRetryInterval :: Eq RetryInterval
derive instance ordRetryInterval :: Ord RetryInterval

instance showRetryInterval :: Show RetryInterval where
  show (RetryInterval ms) = show ms <> "ms"

-- | Create a retry interval from milliseconds.
-- |
-- | Clamps to [1000, 60000].
retryMs :: Number -> RetryInterval
retryMs ms = RetryInterval (Bounded.clampNumber 1000.0 60000.0 ms)

-- | Extract retry interval in milliseconds.
unwrapRetry :: RetryInterval -> Number
unwrapRetry (RetryInterval ms) = ms

-- | Default retry interval: 3 seconds.
-- |
-- | This is the browser default if server doesn't specify.
defaultRetry :: RetryInterval
defaultRetry = RetryInterval 3000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // connection state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete SSE connection state.
-- |
-- | Tracks state, last event ID for reconnection, and statistics.
type SSEConnectionState =
  { state :: SSEState
  , lastEventId :: Maybe EventId
  , connectedAt :: Maybe Number
  , reconnectCount :: Int
  , eventsReceived :: Int
  , lastError :: Maybe String
  }

-- | Initial connection state.
initialSSEState :: SSEConnectionState
initialSSEState =
  { state: SSEClosed
  , lastEventId: Nothing
  , connectedAt: Nothing
  , reconnectCount: 0
  , eventsReceived: 0
  , lastError: Nothing
  }

-- | Connected state.
connectedSSEState :: Number -> SSEConnectionState
connectedSSEState timestamp =
  { state: SSEOpen
  , lastEventId: Nothing
  , connectedAt: Just timestamp
  , reconnectCount: 0
  , eventsReceived: 0
  , lastError: Nothing
  }

-- | Disconnected state with error.
disconnectedSSEState :: Maybe String -> SSEConnectionState
disconnectedSSEState err =
  { state: SSEClosed
  , lastEventId: Nothing
  , connectedAt: Nothing
  , reconnectCount: 0
  , eventsReceived: 0
  , lastError: err
  }

-- | Get the last event ID for reconnection.
lastEventId :: SSEConnectionState -> Maybe EventId
lastEventId s = s.lastEventId

-- | Get the count of events received.
eventCount :: SSEConnectionState -> Int
eventCount s = s.eventsReceived

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for SSE retry interval [1000, 60000] ms
-- |
-- | - 1000ms: Minimum sensible retry (1 second)
-- | - 60000ms: Maximum retry (1 minute)
retryBounds :: Bounded.NumberBounds
retryBounds = Bounded.numberBounds 1000.0 60000.0 Bounded.Clamps "retry"
  "SSE retry interval in milliseconds (1000-60000)"
