━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // 23 // network
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Network Pillar

HTTP, WebSocket, Server-Sent Events, and Service Workers as pure data.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Network/`
- **Files**: 21 modules
- **Lines**: 3,200 total
- **Key features**: HTTP request/response, WebSocket state machine, SSE streaming,
  Service Worker lifecycle, bounded timeouts, cache strategies

## Purpose

Network provides bounded, deterministic primitives for:
- HTTP request construction and response handling
- WebSocket bidirectional communication with reconnection
- Server-Sent Events for server push streams
- Service Worker offline-first capabilities
- Cache strategies for PWA applications
- Push notification subscription state

## Design Philosophy

Network communication at billion-agent scale requires:
- **Deterministic request construction** — same config = same request
- **Bounded timeout values** — no infinite waits
- **Explicit state machines** — no hidden connection states
- **Type-safe message handling** — text vs binary distinguished
- **Complete error representation** — no magic error strings

## Module Organization

```
Network/
├── HTTP/
│   ├── Methods.purs      — HTTP methods (GET, POST, etc.)
│   ├── URL.purs          — URL type and manipulation
│   ├── Headers.purs      — Header types and common headers
│   ├── Body.purs         — Request body types
│   ├── Timeout.purs      — Bounded timeout values
│   ├── Status.purs       — Status codes with predicates
│   ├── Request.purs      — Request construction
│   ├── Response.purs     — Response data
│   └── Result.purs       — Result/error handling
├── WebSocket/
│   ├── Types.purs        — State machine, URL, protocols
│   ├── Messages.purs     — Text and binary messages
│   ├── Close.purs        — RFC 6455 close codes
│   ├── Reconnect.purs    — Reconnection strategies
│   ├── Events.purs       — Lifecycle events
│   ├── Config.purs       — Connection configuration
│   ├── State.purs        — Connection state compound
│   └── Bounds.purs       — Bounded value definitions
├── SSE.purs              — Server-Sent Events
└── ServiceWorker.purs    — Offline-first capabilities
```


━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                   // http // 1
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# HTTP

Pure data types for HTTP communication. The runtime interprets these to execute
actual network requests — Hydrogen describes *what* to do, not *how* to do it.

────────────────────────────────────────────────────────────────────────────────
                                                            // http // methods
────────────────────────────────────────────────────────────────────────────────

## HTTPMethod Enum

HTTP request methods per RFC 7231. Each method has semantic meaning affecting
caching, idempotency, and body expectations.

| Constructor | String Value | Safe | Idempotent | Has Body |
|-------------|--------------|------|------------|----------|
| `GET` | `"GET"` | ✓ | ✓ | ✗ |
| `POST` | `"POST"` | ✗ | ✗ | ✓ |
| `PUT` | `"PUT"` | ✗ | ✓ | ✓ |
| `PATCH` | `"PATCH"` | ✗ | ✗ | ✓ |
| `DELETE` | `"DELETE"` | ✗ | ✓ | ✗ |
| `HEAD` | `"HEAD"` | ✓ | ✓ | ✗ |
| `OPTIONS` | `"OPTIONS"` | ✓ | ✓ | ✗ |

**Semantic Properties:**

- **Safe**: No server-side effects. Can be prefetched, cached, repeated freely.
- **Idempotent**: Multiple identical requests = same effect. Can retry on failure.
- **Has Body**: Method typically includes a request body.

**Query Functions:**

```purescript
isIdempotent :: HTTPMethod -> Boolean
isSafe :: HTTPMethod -> Boolean
hasRequestBody :: HTTPMethod -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // http // url
────────────────────────────────────────────────────────────────────────────────

## URL Type

Wrapped string representing a Uniform Resource Locator.

```purescript
newtype URL = URL String
```

**Constructors:**

| Function | Description |
|----------|-------------|
| `url :: String -> URL` | Create URL from string |
| `urlWithPath :: URL -> String -> URL` | Append path segment |
| `urlWithQuery :: URL -> Array (Tuple String String) -> URL` | Add query params |
| `unwrapURL :: URL -> String` | Extract string |

**Example:**

```purescript
baseUrl = url "https://api.example.com"
endpoint = urlWithPath baseUrl "users"
-- Result: "https://api.example.com/users"

withQuery = urlWithQuery endpoint [Tuple "page" "1", Tuple "limit" "20"]
-- Result: "https://api.example.com/users?page=1&limit=20"
```

────────────────────────────────────────────────────────────────────────────────
                                                             // http // headers
────────────────────────────────────────────────────────────────────────────────

## Header Types

HTTP headers as typed name-value pairs.

### HeaderName / HeaderValue

```purescript
newtype HeaderName = HeaderName String
newtype HeaderValue = HeaderValue String
type Header = Tuple HeaderName HeaderValue
```

**Constructors:**

| Function | Description |
|----------|-------------|
| `headerName :: String -> HeaderName` | Create header name |
| `headerValue :: String -> HeaderValue` | Create header value |
| `header :: String -> String -> Header` | Create name-value pair |

### Common Header Presets

| Preset | Name | Value |
|--------|------|-------|
| `contentTypeJSON` | `Content-Type` | `application/json` |
| `contentTypeForm` | `Content-Type` | `application/x-www-form-urlencoded` |
| `contentTypeText` | `Content-Type` | `text/plain` |
| `acceptJSON` | `Accept` | `application/json` |
| `acceptHTML` | `Accept` | `text/html` |
| `authorizationBearer token` | `Authorization` | `Bearer {token}` |

────────────────────────────────────────────────────────────────────────────────
                                                                // http // body
────────────────────────────────────────────────────────────────────────────────

## RequestBody Enum

HTTP request body content types.

| Constructor | Description | Content-Type |
|-------------|-------------|--------------|
| `JSONBody String` | JSON-encoded string | `application/json` |
| `TextBody String` | Plain text | `text/plain` |
| `FormBody (Array (Tuple String String))` | Form data | `application/x-www-form-urlencoded` |
| `EmptyBody` | No body | — |

**Constructors:**

```purescript
jsonBody :: String -> RequestBody
textBody :: String -> RequestBody
formBody :: Array (Tuple String String) -> RequestBody
emptyBody :: RequestBody
```


────────────────────────────────────────────────────────────────────────────────
                                                             // http // timeout
────────────────────────────────────────────────────────────────────────────────

## Timeout Atom

Bounded request timeout in milliseconds.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Timeout | Number | 0.0 | 300000.0 | clamps | 0 = use default |

**Key insight:** A timeout of 0 means "use system default", not "instant timeout".
Maximum is 300,000 ms (5 minutes) — a reasonable upper limit for any request.

**Constructors:**

| Function | Description |
|----------|-------------|
| `timeoutMs :: Number -> Timeout` | From milliseconds |
| `timeoutSeconds :: Number -> Timeout` | From seconds |
| `unwrapTimeout :: Timeout -> Number` | Extract milliseconds |

**Presets:**

| Preset | Value | Description |
|--------|-------|-------------|
| `defaultTimeout` | 30000 ms | Standard 30-second timeout |
| `noTimeout` | 0 ms | Defer to runtime default |

**Query Function:**

```purescript
isExpired :: Timeout -> Number -> Boolean
-- Check if elapsed time exceeds timeout
```

────────────────────────────────────────────────────────────────────────────────
                                                              // http // status
────────────────────────────────────────────────────────────────────────────────

## StatusCode Atom

HTTP status code bounded to valid range.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| StatusCode | Int | 100 | 599 | clamps | Per HTTP specification |

**Category Predicates:**

| Function | Range | Description |
|----------|-------|-------------|
| `isInformational` | 100-199 | Informational responses |
| `isSuccess` | 200-299 | Successful responses |
| `isRedirect` | 300-399 | Redirection responses |
| `isClientError` | 400-499 | Client error responses |
| `isServerError` | 500-599 | Server error responses |

**Common Status Presets:**

| Preset | Code | Meaning |
|--------|------|---------|
| `status200` | 200 | OK |
| `status201` | 201 | Created |
| `status204` | 204 | No Content |
| `status301` | 301 | Moved Permanently |
| `status302` | 302 | Found (Temporary Redirect) |
| `status304` | 304 | Not Modified |
| `status400` | 400 | Bad Request |
| `status401` | 401 | Unauthorized |
| `status403` | 403 | Forbidden |
| `status404` | 404 | Not Found |
| `status500` | 500 | Internal Server Error |
| `status502` | 502 | Bad Gateway |
| `status503` | 503 | Service Unavailable |

────────────────────────────────────────────────────────────────────────────────
                                                             // http // request
────────────────────────────────────────────────────────────────────────────────

## HTTPRequest Molecule

Complete request specification as pure data.

```purescript
type HTTPRequest =
  { method :: HTTPMethod
  , url :: URL
  , headers :: Array Header
  , body :: Maybe RequestBody
  , timeout :: Maybe Timeout
  }
```

**Constructors:**

| Function | Description |
|----------|-------------|
| `request` | Full request with all parameters |
| `getRequest :: URL -> Array Header -> HTTPRequest` | Simple GET |
| `postRequest :: URL -> Array Header -> String -> HTTPRequest` | POST with JSON |
| `putRequest :: URL -> Array Header -> String -> HTTPRequest` | PUT with JSON |
| `deleteRequest :: URL -> Array Header -> HTTPRequest` | Simple DELETE |

**Example:**

```purescript
userRequest = request GET 
  (url "https://api.example.com/users/123")
  [authorizationBearer "my-token"]
  Nothing
  (Just (timeoutSeconds 10))
```

────────────────────────────────────────────────────────────────────────────────
                                                            // http // response
────────────────────────────────────────────────────────────────────────────────

## HTTPResponse Molecule

Complete response data from HTTP call.

```purescript
type HTTPResponse =
  { status :: StatusCode
  , headers :: Array Header
  , body :: String
  , url :: URL              -- Final URL (after redirects)
  }
```

**Accessors:**

| Function | Description |
|----------|-------------|
| `responseBody :: HTTPResponse -> String` | Extract body |
| `responseHeader :: String -> HTTPResponse -> Maybe String` | Find header |
| `responseHeaders :: HTTPResponse -> Array Header` | All headers |

────────────────────────────────────────────────────────────────────────────────
                                                              // http // result
────────────────────────────────────────────────────────────────────────────────

## HTTPResult Enum

All possible outcomes of an HTTP request, including network-level failures.

| Constructor | Description |
|-------------|-------------|
| `HTTPOk HTTPResponse` | Request completed (may still be 4xx/5xx) |
| `HTTPTimeout` | Request timed out |
| `HTTPNetworkError` | Network-level failure |
| `HTTPCORSError` | CORS policy blocked request |
| `HTTPAborted` | Request was cancelled |

**Query Functions:**

```purescript
isOk :: HTTPResult -> Boolean     -- Did we get ANY response?
isError :: HTTPResult -> Boolean  -- Did network fail?
mapOk :: (HTTPResponse -> HTTPResponse) -> HTTPResult -> HTTPResult
```

**Key insight:** `isOk` returns true even for 4xx/5xx responses — it means
"did we receive an HTTP response?" Use `isSuccess` on the response status
to check for HTTP-level success.

## HTTPError Enum

Detailed error information for error handling and display.

| Constructor | Description |
|-------------|-------------|
| `TimeoutError Timeout` | Request exceeded timeout |
| `NetworkFailure String` | Network error with message |
| `CORSBlocked URL` | CORS prevented request |
| `RequestAborted` | Request was cancelled |
| `InvalidResponse String` | Response couldn't be parsed |
| `StatusError StatusCode String` | HTTP error status with body |

**Human-readable Messages:**

```purescript
errorMessage :: HTTPError -> String
-- TimeoutError -> "Request timed out"
-- NetworkFailure msg -> "Network error: " <> msg
-- CORSBlocked -> "Request blocked by CORS policy"
-- RequestAborted -> "Request was cancelled"
-- InvalidResponse msg -> "Invalid response: " <> msg
-- StatusError code _ -> "HTTP error " <> show code
```


━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                              // websocket // 2
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# WebSocket

Pure data types for bidirectional communication. Models the WebSocket protocol
state machine as algebraic data types.

## State Machine Diagram

```
  ┌──────────┐
  │Connecting│
  └────┬─────┘
       │ connected
       ▼
  ┌────────┐  close requested
  │  Open  │─────────────────┐
  └────┬───┘                 │
       │ close received      ▼
       │                ┌─────────┐
       └───────────────►│ Closing │
                        └────┬────┘
                             │ closed
                             ▼
                        ┌────────┐
                        │ Closed │
                        └────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                         // websocket // state
────────────────────────────────────────────────────────────────────────────────

## WebSocketState Enum

Connection state machine mirroring W3C WebSocket readyState.

| Constructor | readyState | Description |
|-------------|------------|-------------|
| `Connecting` | 0 | Connection being established |
| `Open` | 1 | Connection open and ready |
| `Closing` | 2 | Connection is closing |
| `Closed` | 3 | Connection is closed |

**Query Functions:**

| Function | Description |
|----------|-------------|
| `isConnecting :: WebSocketState -> Boolean` | State == Connecting |
| `isOpen :: WebSocketState -> Boolean` | State == Open |
| `isClosing :: WebSocketState -> Boolean` | State == Closing |
| `isClosed :: WebSocketState -> Boolean` | State == Closed |
| `canSend :: WebSocketState -> Boolean` | Only Open |
| `canReceive :: WebSocketState -> Boolean` | Open or Closing |

**Key insight:** `canReceive` is true during Closing because the connection may
still receive final messages before fully closing.

────────────────────────────────────────────────────────────────────────────────
                                                           // websocket // url
────────────────────────────────────────────────────────────────────────────────

## WebSocketURL Type

WebSocket endpoint URL (ws:// or wss://).

```purescript
newtype WebSocketURL = WebSocketURL String
```

**Constructors:**

| Function | Protocol | Description |
|----------|----------|-------------|
| `wsURL :: String -> WebSocketURL` | ws:// | Non-secure WebSocket |
| `wssURL :: String -> WebSocketURL` | wss:// | Secure WebSocket (recommended) |
| `unwrapWebSocketURL :: WebSocketURL -> String` | — | Extract URL string |
| `isSecure :: WebSocketURL -> Boolean` | — | Is wss:// protocol |

**Example:**

```purescript
secure = wssURL "api.example.com/ws"
-- Result: "wss://api.example.com/ws"
```

────────────────────────────────────────────────────────────────────────────────
                                                      // websocket // protocol
────────────────────────────────────────────────────────────────────────────────

## Protocol Type

WebSocket subprotocol identifier for handshake negotiation.

```purescript
newtype Protocol = Protocol String
```

Used during connection handshake to negotiate application-level protocol
between client and server.

**Example:**

```purescript
protocols = [protocol "graphql-ws", protocol "subscriptions-transport-ws"]
```

────────────────────────────────────────────────────────────────────────────────
                                                       // websocket // binary
────────────────────────────────────────────────────────────────────────────────

## BinaryType Enum

Binary data format for received messages.

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `ArrayBuffer` | `"arraybuffer"` | Receive as ArrayBuffer |
| `Blob` | `"blob"` | Receive as Blob |

## Bytes Type

Binary data representation as bounded byte array.

```purescript
newtype Bytes = Bytes (Array Int)
```

Each byte value is clamped to [0, 255].

| Function | Description |
|----------|-------------|
| `bytes :: Int -> Bytes` | Single byte |
| `bytesFromArray :: Array Int -> Bytes` | From array (clamped) |
| `unwrapBytes :: Bytes -> Array Int` | Extract array |
| `bytesLength :: Bytes -> Int` | Byte count |
| `emptyBytes :: Bytes` | Empty array |

────────────────────────────────────────────────────────────────────────────────
                                                      // websocket // messages
────────────────────────────────────────────────────────────────────────────────

## WebSocketMessage Enum

WebSocket frame types: text (UTF-8) or binary.

| Constructor | Description |
|-------------|-------------|
| `TextMessage String` | UTF-8 text frame |
| `BinaryMessage Bytes` | Binary data frame |

**Constructors and Queries:**

```purescript
textMessage :: String -> WebSocketMessage
binaryMessage :: Bytes -> WebSocketMessage
messageSize :: WebSocketMessage -> Int     -- Approximate size in bytes
isTextMessage :: WebSocketMessage -> Boolean
isBinaryMessage :: WebSocketMessage -> Boolean
```


────────────────────────────────────────────────────────────────────────────────
                                                         // websocket // close
────────────────────────────────────────────────────────────────────────────────

## CloseCode Atom

WebSocket close code per RFC 6455.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| CloseCode | Int | 1000 | 4999 | clamps | RFC 6455 range |

**Reserved Ranges:**

- **1000-2999**: Protocol reserved
- **3000-3999**: Library/framework use
- **4000-4999**: Application use

### Standard Close Code Presets (RFC 6455)

| Preset | Code | Description |
|--------|------|-------------|
| `closeNormal` | 1000 | Normal closure |
| `closeGoingAway` | 1001 | Endpoint going away (page close, server shutdown) |
| `closeProtocolError` | 1002 | Protocol error |
| `closeUnsupportedData` | 1003 | Unsupported data type received |
| `closeNoStatus` | 1005 | No status code received |
| `closeAbnormal` | 1006 | Abnormal closure (no close frame) |
| `closeInvalidPayload` | 1007 | Invalid frame payload data |
| `closePolicyViolation` | 1008 | Policy violation |
| `closeMessageTooBig` | 1009 | Message too big to process |
| `closeMissingExtension` | 1010 | Missing required extension |
| `closeInternalError` | 1011 | Internal server error |
| `closeServiceRestart` | 1012 | Service restarting |
| `closeTryAgainLater` | 1013 | Try again later (temporary overload) |

**Query Functions:**

```purescript
isNormalClose :: CloseCode -> Boolean  -- 1000 or 1001
isErrorClose :: CloseCode -> Boolean   -- 1002-1015
```

## CloseEvent Molecule

WebSocket close event data.

```purescript
type CloseEvent =
  { code :: CloseCode
  , reason :: String
  , wasClean :: Boolean
  }
```

| Function | Description |
|----------|-------------|
| `closeEvent :: CloseCode -> String -> Boolean -> CloseEvent` | Constructor |
| `wasClean :: CloseEvent -> Boolean` | Clean close handshake? |
| `closeReason :: CloseEvent -> String` | Reason message |

────────────────────────────────────────────────────────────────────────────────
                                                     // websocket // reconnect
────────────────────────────────────────────────────────────────────────────────

## ReconnectStrategy Molecule

Reconnection handling with exponential backoff.

```purescript
type ReconnectStrategy =
  { maxAttempts :: Int      -- 0 = infinite
  , baseDelayMs :: Number   -- Initial delay
  , maxDelayMs :: Number    -- Delay cap
  , attempt :: Int          -- Current attempt
  , jitter :: Boolean       -- Add random jitter
  }
```

**Bounds:**

| Parameter | Min | Max | Notes |
|-----------|-----|-----|-------|
| `baseDelayMs` | 100.0 | 60000.0 | 100ms - 1 minute |
| `maxDelayMs` | 1000.0 | 300000.0 | 1 second - 5 minutes |

### Exponential Backoff Formula

```
delay = baseDelay × 2^attempt
capped at maxDelay
```

**Presets:**

| Preset | Max Attempts | Base Delay | Max Delay |
|--------|--------------|------------|-----------|
| `defaultReconnect` | 5 | 1000 ms | 30000 ms |
| `noReconnect` | 0 | 0 | 0 |
| `exponentialBackoff n base` | n | base | base × 32 |

**Query Functions:**

```purescript
shouldReconnect :: ReconnectStrategy -> Boolean
nextReconnectDelay :: ReconnectStrategy -> Number
```

────────────────────────────────────────────────────────────────────────────────
                                                        // websocket // events
────────────────────────────────────────────────────────────────────────────────

## WebSocketEvent Enum

Lifecycle events for WebSocket connections.

| Constructor | Description |
|-------------|-------------|
| `WSConnecting` | Connection initiated |
| `WSOpen Protocol` | Connection established with protocol |
| `WSMessage WebSocketMessage` | Message received |
| `WSError String` | Error occurred |
| `WSClose CloseEvent` | Connection closed |
| `WSReconnecting Int` | Attempting reconnection (attempt #) |

────────────────────────────────────────────────────────────────────────────────
                                                        // websocket // config
────────────────────────────────────────────────────────────────────────────────

## WebSocketConfig Molecule

Connection configuration.

```purescript
type WebSocketConfig =
  { url :: WebSocketURL
  , protocols :: Array Protocol
  , reconnect :: Maybe ReconnectStrategy
  , binaryType :: BinaryType
  }
```

**Constructors:**

| Function | Description |
|----------|-------------|
| `config :: WebSocketURL -> WebSocketConfig` | Basic config |
| `defaultConfig :: WebSocketURL -> WebSocketConfig` | With default reconnect |
| `withProtocols :: Array Protocol -> WebSocketConfig -> WebSocketConfig` | Add protocols |
| `withReconnect :: ReconnectStrategy -> WebSocketConfig -> WebSocketConfig` | Set reconnect |

────────────────────────────────────────────────────────────────────────────────
                                               // websocket // state // compound
────────────────────────────────────────────────────────────────────────────────

## ConnectionState Compound

Complete connection state for UI rendering.

```purescript
type ConnectionState =
  { state :: WebSocketState
  , protocol :: Maybe Protocol
  , connectedAt :: Maybe Number
  , reconnectAttempt :: Int
  , lastError :: Maybe String
  , messagesSent :: Int
  , messagesReceived :: Int
  }
```

**State Constructors:**

| Function | Description |
|----------|-------------|
| `initialState :: ConnectionState` | Closed, no metadata |
| `connectedState :: Protocol -> Number -> ConnectionState` | Open with protocol |
| `disconnectedState :: Maybe String -> ConnectionState` | Closed with error |
| `reconnectingState :: Int -> ConnectionState` | Connecting with attempt |


━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                    // sse // 3
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Server-Sent Events (SSE)

Pure data types for server push streams. Models the EventSource API.

## SSE vs WebSocket

SSE is simpler when you only need server-to-client push:

| Feature | SSE | WebSocket |
|---------|-----|-----------|
| Direction | Server → Client | Bidirectional |
| Protocol | HTTP | ws:// / wss:// |
| Auto-reconnect | Built-in with event ID | Manual implementation |
| Binary support | No (text only) | Yes |
| Proxy/LB support | Standard HTTP | Needs WebSocket support |

## Protocol Format

SSE messages are text with specific format:

```
event: message-type
data: payload line 1
data: payload line 2
id: event-id

```

────────────────────────────────────────────────────────────────────────────────
                                                              // sse // state
────────────────────────────────────────────────────────────────────────────────

## SSEState Enum

EventSource connection state.

| Constructor | readyState | Description |
|-------------|------------|-------------|
| `SSEConnecting` | 0 | Connection being established |
| `SSEOpen` | 1 | Connection is open |
| `SSEClosed` | 2 | Connection is closed |

**Query Functions:**

```purescript
isSSEConnecting :: SSEState -> Boolean
isSSEOpen :: SSEState -> Boolean
isSSEClosed :: SSEState -> Boolean
canReceiveSSE :: SSEState -> Boolean  -- Only when Open
```

────────────────────────────────────────────────────────────────────────────────
                                                                // sse // url
────────────────────────────────────────────────────────────────────────────────

## SSEURL Type

```purescript
newtype SSEURL = SSEURL String
```

Must be HTTP(S) URL returning `text/event-stream` content type.

────────────────────────────────────────────────────────────────────────────────
                                                      // sse // event // type
────────────────────────────────────────────────────────────────────────────────

## EventType Type

The `event:` field in SSE stream. Defaults to "message" if not specified.

```purescript
newtype EventType = EventType String
```

| Function | Description |
|----------|-------------|
| `eventType :: String -> EventType` | Create event type |
| `defaultEventType :: EventType` | "message" |
| `isDefaultType :: EventType -> Boolean` | Is "message"? |

────────────────────────────────────────────────────────────────────────────────
                                                         // sse // event // id
────────────────────────────────────────────────────────────────────────────────

## EventId Type

The `id:` field for stream resumption after reconnection.

```purescript
newtype EventId = EventId (Maybe String)
```

| Function | Description |
|----------|-------------|
| `eventId :: String -> EventId` | Create event ID |
| `noEventId :: EventId` | No ID |
| `hasEventId :: EventId -> Boolean` | Has ID? |

**Key insight:** On reconnection, the browser sends `Last-Event-ID` header with
the last received event ID, allowing the server to resume from that point.

────────────────────────────────────────────────────────────────────────────────
                                                              // sse // event
────────────────────────────────────────────────────────────────────────────────

## SSEEvent Molecule

Complete event from the stream.

```purescript
type SSEEvent =
  { eventType :: EventType
  , data :: Array String    -- Multiple "data:" lines
  , id :: EventId
  , origin :: String        -- Origin URL
  }
```

**Accessors:**

| Function | Description |
|----------|-------------|
| `eventData :: SSEEvent -> String` | Lines joined with newlines |
| `eventLines :: SSEEvent -> Array String` | Individual data lines |
| `eventTypeOf :: SSEEvent -> EventType` | Event type |
| `eventIdOf :: SSEEvent -> EventId` | Event ID |

────────────────────────────────────────────────────────────────────────────────
                                                              // sse // result
────────────────────────────────────────────────────────────────────────────────

## SSEResult Enum

SSE lifecycle events.

| Constructor | Description |
|-------------|-------------|
| `SSEMessage SSEEvent` | Event received |
| `SSEError String` | Error (connection will auto-retry) |
| `SSEOpenEvent` | Connection opened |

**Query Functions:**

```purescript
isSSEMessage :: SSEResult -> Boolean
isSSEError :: SSEResult -> Boolean
isSSEOpenEvent :: SSEResult -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                              // sse // retry
────────────────────────────────────────────────────────────────────────────────

## RetryInterval Atom

Reconnection retry interval.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| RetryInterval | Number | 1000.0 | 60000.0 | clamps | 1s - 1min |

Can be set by server via `retry:` field or configured client-side.

**Preset:**

| Preset | Value | Description |
|--------|-------|-------------|
| `defaultRetry` | 3000 ms | Browser default if server doesn't specify |

────────────────────────────────────────────────────────────────────────────────
                                                              // sse // config
────────────────────────────────────────────────────────────────────────────────

## SSEConfig Molecule

```purescript
type SSEConfig =
  { url :: SSEURL
  , withCredentials :: Boolean    -- Include cookies in CORS
  , retryInterval :: RetryInterval
  , lastEventId :: Maybe EventId  -- Resume from this event
  }
```

**Modifiers:**

```purescript
withCredentials :: Boolean -> SSEConfig -> SSEConfig
withRetry :: RetryInterval -> SSEConfig -> SSEConfig
```

────────────────────────────────────────────────────────────────────────────────
                                                    // sse // state // compound
────────────────────────────────────────────────────────────────────────────────

## SSEConnectionState Compound

Complete SSE connection state.

```purescript
type SSEConnectionState =
  { state :: SSEState
  , lastEventId :: Maybe EventId
  , connectedAt :: Maybe Number
  , reconnectCount :: Int
  , eventsReceived :: Int
  , lastError :: Maybe String
  }
```

**State Constructors:**

| Function | Description |
|----------|-------------|
| `initialSSEState` | Closed, no events |
| `connectedSSEState :: Number -> SSEConnectionState` | Open with timestamp |
| `disconnectedSSEState :: Maybe String -> SSEConnectionState` | With error |


━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                          // service-worker // 4
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Service Worker

Pure data types for offline-first capabilities. Models the complete Service
Worker lifecycle as algebraic data types.

## Lifecycle Diagram

```
  ┌────────────┐
  │ Installing │──────► error ──► Redundant
  └─────┬──────┘
        │ installed
        ▼
  ┌───────────┐
  │ Installed │ (waiting)
  └─────┬─────┘
        │ activating
        ▼
  ┌────────────┐
  │ Activating │──────► error ──► Redundant
  └─────┬──────┘
        │ activated
        ▼
  ┌───────────┐
  │ Activated │ (controlling)
  └─────┬─────┘
        │ update replaces
        ▼
  ┌───────────┐
  │ Redundant │
  └───────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                    // service-worker // state
────────────────────────────────────────────────────────────────────────────────

## ServiceWorkerState Enum

Complete lifecycle from installation to redundancy.

| Constructor | Description |
|-------------|-------------|
| `Installing` | Script being fetched and installed |
| `Installed` | Installed but waiting to activate |
| `Activating` | Activating (claiming clients) |
| `Activated` | Active and controlling pages |
| `Redundant` | Replaced by newer worker or failed |

**Query Functions:**

| Function | Description |
|----------|-------------|
| `isInstalling` | State == Installing |
| `isInstalled` | State == Installed |
| `isActivating` | State == Activating |
| `isActivated` | State == Activated |
| `isRedundant` | State == Redundant |
| `isActive` | Activating or Activated |
| `isWaiting` | Installed (waiting to become active) |

────────────────────────────────────────────────────────────────────────────────
                                                   // service-worker // script
────────────────────────────────────────────────────────────────────────────────

## ScriptURL Type

Path to the JavaScript file containing worker code.

```purescript
newtype ScriptURL = ScriptURL String
```

**Example:**

```purescript
swScript = scriptURL "/sw.js"
```

────────────────────────────────────────────────────────────────────────────────
                                                    // service-worker // scope
────────────────────────────────────────────────────────────────────────────────

## Scope Type

Determines which URLs the worker controls. Default is the directory containing
the script.

```purescript
newtype Scope = Scope String
```

**Presets:**

| Preset | Description |
|--------|-------------|
| `defaultScope` | Empty string (use default) |

**Example:**

```purescript
appScope = scope "/app/"  -- Only control URLs under /app/
```

────────────────────────────────────────────────────────────────────────────────
                                            // service-worker // update-cache
────────────────────────────────────────────────────────────────────────────────

## UpdateViaCache Enum

How HTTP cache is handled for service worker updates.

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `Imports` | `"imports"` | Check cache for imported scripts only |
| `All` | `"all"` | Check cache for main script and imports |
| `None` | `"none"` | Bypass cache entirely |

────────────────────────────────────────────────────────────────────────────────
                                                   // service-worker // config
────────────────────────────────────────────────────────────────────────────────

## SWConfig Molecule

Registration configuration.

```purescript
type SWConfig =
  { script :: ScriptURL
  , scope :: Maybe Scope
  , updateViaCache :: UpdateViaCache
  }
```

**Constructors:**

```purescript
config :: ScriptURL -> SWConfig
defaultConfig :: ScriptURL -> SWConfig
withScope :: Scope -> SWConfig -> SWConfig
withUpdateViaCache :: UpdateViaCache -> SWConfig -> SWConfig
```

────────────────────────────────────────────────────────────────────────────────
                                              // service-worker // registration
────────────────────────────────────────────────────────────────────────────────

## RegistrationState Enum

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `NotRegistered` | `"not-registered"` | No worker registered |
| `Registering` | `"registering"` | Registration in progress |
| `Registered` | `"registered"` | Successfully registered |
| `RegistrationError` | `"error"` | Registration failed |
| `Updating` | `"updating"` | Update in progress |

**Query Functions:**

```purescript
isRegistered :: RegistrationState -> Boolean   -- Registered or Updating
isUnregistered :: RegistrationState -> Boolean -- NotRegistered or Error
hasUpdate :: RegistrationState -> Boolean      -- Updating
```

## SWRegistration Molecule

```purescript
type SWRegistration =
  { scope :: Scope
  , state :: RegistrationState
  , active :: Maybe WorkerInfo
  , waiting :: Maybe WorkerInfo
  , installing :: Maybe WorkerInfo
  }
```

## WorkerInfo Molecule

```purescript
type WorkerInfo =
  { state :: ServiceWorkerState
  , scriptURL :: ScriptURL
  }
```

────────────────────────────────────────────────────────────────────────────────
                                                   // service-worker // events
────────────────────────────────────────────────────────────────────────────────

## SWEvent Enum

Lifecycle events.

| Constructor | Description |
|-------------|-------------|
| `SWInstalling ScriptURL` | Installation started |
| `SWInstalled ScriptURL` | Installed, waiting |
| `SWActivating ScriptURL` | Activation started |
| `SWActivated ScriptURL` | Now controlling |
| `SWRedundant ScriptURL` | Became redundant |
| `SWError String` | Error occurred |
| `SWUpdateFound ScriptURL` | New version discovered |
| `SWControllerChange ScriptURL` | Page's controller changed |


────────────────────────────────────────────────────────────────────────────────
                                                 // service-worker // caching
────────────────────────────────────────────────────────────────────────────────

## CacheStrategy Enum

Caching strategies for fetch requests.

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `CacheFirst` | `"cache-first"` | Check cache, fallback to network |
| `NetworkFirst` | `"network-first"` | Try network, fallback to cache |
| `CacheOnly` | `"cache-only"` | Only use cache, fail if not cached |
| `NetworkOnly` | `"network-only"` | Only use network, no caching |
| `StaleWhileRevalidate` | `"stale-while-revalidate"` | Return cache, update in background |

### Strategy Selection Guide

| Use Case | Strategy |
|----------|----------|
| Static assets (CSS, JS, images) | `CacheFirst` |
| API data needing freshness | `NetworkFirst` |
| Offline-only resources | `CacheOnly` |
| Real-time data | `NetworkOnly` |
| Frequently updated content | `StaleWhileRevalidate` |

## CacheConfig Molecule

```purescript
type CacheConfig =
  { strategy :: CacheStrategy
  , maxAgeSeconds :: Int      -- 0 = no limit
  , maxEntries :: Int         -- 0 = no limit
  , cacheName :: String
  }
```

**Bounds:**

| Parameter | Min | Max |
|-----------|-----|-----|
| `maxAgeSeconds` | 0 | 31536000 (1 year) |
| `maxEntries` | 0 | 10000 |

────────────────────────────────────────────────────────────────────────────────
                                                   // service-worker // update
────────────────────────────────────────────────────────────────────────────────

## UpdateState Enum

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `NoUpdate` | `"no-update"` | No update available |
| `UpdateAvailable` | `"available"` | New version waiting |
| `UpdateActivating` | `"activating"` | New version activating |
| `UpdateComplete` | `"complete"` | New version now active |

**Query Functions:**

```purescript
hasNewVersion :: UpdateState -> Boolean  -- Available or Activating
needsRefresh :: UpdateState -> Boolean   -- Complete (page should refresh)
```

────────────────────────────────────────────────────────────────────────────────
                                              // service-worker // nav-preload
────────────────────────────────────────────────────────────────────────────────

## NavigationPreload Enum

Navigation preload starts network request in parallel with SW startup.

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `PreloadDisabled` | `"disabled"` | Navigation preload off |
| `PreloadEnabled` | `"enabled"` | Navigation preload active |
| `PreloadUnsupported` | `"unsupported"` | Browser doesn't support |

────────────────────────────────────────────────────────────────────────────────
                                                   // service-worker // push
────────────────────────────────────────────────────────────────────────────────

## PushState Enum

Push notification subscription state.

| Constructor | String Value | Description |
|-------------|--------------|-------------|
| `PushNotSubscribed` | `"not-subscribed"` | Not subscribed |
| `PushSubscribed` | `"subscribed"` | Subscribed and active |
| `PushDenied` | `"denied"` | User denied permission |
| `PushUnsupported` | `"unsupported"` | Push not supported |

**Query Functions:**

```purescript
isPushSubscribed :: PushState -> Boolean
isPushDenied :: PushState -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                       // service-worker // state // compound
────────────────────────────────────────────────────────────────────────────────

## SWConnectionState Compound

Complete Service Worker state combining all aspects.

```purescript
type SWConnectionState =
  { registration :: Maybe SWRegistration
  , updateState :: UpdateState
  , navigationPreload :: NavigationPreload
  , pushState :: PushState
  , isControlled :: Boolean    -- Is page controlled by SW?
  }
```

**State Constructors:**

| Function | Description |
|----------|-------------|
| `initialSWState` | No registration |
| `registeredSWState :: SWRegistration -> SWConnectionState` | After registration |
| `controlledSWState :: SWRegistration -> SWConnectionState` | SW controlling page |


━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               // bounds // 5
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Bounded Value Summary

All atoms in Network pillar with their bounds.

## HTTP Bounds

| Name | Type | Min | Max | Behavior |
|------|------|-----|-----|----------|
| Timeout | Number | 0.0 | 300000.0 | clamps |
| StatusCode | Int | 100 | 599 | clamps |

## WebSocket Bounds

| Name | Type | Min | Max | Behavior |
|------|------|-----|-----|----------|
| CloseCode | Int | 1000 | 4999 | clamps |
| Bytes | Int[] | 0 | 255 | clamps (each) |
| baseDelayMs | Number | 100.0 | 60000.0 | clamps |
| maxDelayMs | Number | 1000.0 | 300000.0 | clamps |

## SSE Bounds

| Name | Type | Min | Max | Behavior |
|------|------|-----|-----|----------|
| RetryInterval | Number | 1000.0 | 60000.0 | clamps |

## Service Worker Bounds

| Name | Type | Min | Max | Behavior |
|------|------|-----|-----|----------|
| maxAgeSeconds | Int | 0 | 31536000 | clamps |
| maxEntries | Int | 0 | 10000 | clamps |

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                            // philosophy // 6
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Design Philosophy

## Pure Data, Not Effects

Network types describe **what** to do, not **how** to do it. An `HTTPRequest`
is pure data — the runtime interprets it to execute the actual network call.

```purescript
-- This is pure data, no effects
myRequest :: HTTPRequest
myRequest = getRequest (url "https://api.example.com/users") [acceptJSON]

-- The runtime handles the actual HTTP call
-- and returns an HTTPResult
```

## Explicit State Machines

WebSocket and Service Worker are complex stateful protocols. Rather than
hide state behind callbacks, Hydrogen exposes the state machine explicitly:

```purescript
case wsState of
  Connecting -> showConnecting
  Open -> showConnected
  Closing -> showDisconnecting
  Closed -> showDisconnected
```

## Bounded Everything

No unbounded values in network types:
- Timeouts cap at 5 minutes (no infinite waits)
- Status codes bounded to HTTP spec
- Close codes bounded to RFC 6455
- Retry intervals have sensible limits

## Complete Error Representation

Every failure mode is explicitly modeled:

```purescript
case result of
  HTTPOk response -> handleSuccess response
  HTTPTimeout -> handleTimeout
  HTTPNetworkError -> handleNetworkError
  HTTPCORSError -> handleCORS
  HTTPAborted -> handleAborted
```

No magic error strings. No undefined behavior.

## Why This Matters at Scale

When agents operate at 1000 tokens/second in a billion-agent swarm:
- **Explicit states** mean instant understanding of connection status
- **Bounded values** mean no crashes from edge cases
- **Type-safe messages** mean no confusion between text and binary
- **Complete error types** mean every failure can be handled

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

```
                                                     — Opus 4.5 // 2026-03-01
```
