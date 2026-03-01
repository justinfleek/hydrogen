-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // network // http
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Request/Response Schema — Pure data types for HTTP communication.
-- |
-- | Provides bounded, deterministic types for HTTP operations without
-- | requiring JavaScript FFI. The runtime interprets these pure data
-- | structures to execute actual network requests.
-- |
-- | ## Design Philosophy
-- |
-- | HTTP communication at billion-agent scale requires:
-- | - Deterministic request construction (same config = same request)
-- | - Bounded timeout values (no infinite waits)
-- | - Explicit error states (no magic error strings)
-- | - Complete response representation (headers, status, body)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Network.HTTP as HTTP
-- |
-- | -- Build a request
-- | request = HTTP.request
-- |   { method: HTTP.GET
-- |   , url: HTTP.url "https://api.example.com/users"
-- |   , headers: [HTTP.header "Authorization" "Bearer token"]
-- |   , body: Nothing
-- |   , timeout: Just (HTTP.timeoutSeconds 30)
-- |   }
-- |
-- | -- Pattern match on result
-- | case result of
-- |   HTTP.HTTPOk response -> handleSuccess response
-- |   HTTP.HTTPTimeout -> handleTimeout
-- |   HTTP.HTTPNetworkError -> handleNetworkError
-- |   HTTP.HTTPCORSError -> handleCORS
-- | ```
-- |
-- | ## Module Organization
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `HTTP.Methods` — HTTP method types (GET, POST, etc.)
-- | - `HTTP.URL` — URL type and manipulation
-- | - `HTTP.Headers` — Header types and common headers
-- | - `HTTP.Body` — Request body types
-- | - `HTTP.Timeout` — Timeout configuration
-- | - `HTTP.Status` — Status codes and predicates
-- | - `HTTP.Request` — HTTP request construction
-- | - `HTTP.Response` — HTTP response types
-- | - `HTTP.Result` — Result/error handling

module Hydrogen.Schema.Network.HTTP
  ( module Methods
  , module URL
  , module Headers
  , module Body
  , module Timeout
  , module Status
  , module Request
  , module Response
  , module Result
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Network.HTTP.Methods
  ( HTTPMethod(GET, POST, PUT, PATCH, DELETE, HEAD, OPTIONS)
  , isIdempotent
  , isSafe
  , hasRequestBody
  ) as Methods

import Hydrogen.Schema.Network.HTTP.URL
  ( URL
  , url
  , unwrapURL
  , urlWithPath
  , urlWithQuery
  ) as URL

import Hydrogen.Schema.Network.HTTP.Headers
  ( HeaderName
  , headerName
  , unwrapHeaderName
  , HeaderValue
  , headerValue
  , unwrapHeaderValue
  , Header
  , header
  , contentTypeJSON
  , contentTypeForm
  , contentTypeText
  , acceptJSON
  , acceptHTML
  , authorizationBearer
  ) as Headers

import Hydrogen.Schema.Network.HTTP.Body
  ( RequestBody(JSONBody, TextBody, FormBody, EmptyBody)
  , jsonBody
  , textBody
  , formBody
  , emptyBody
  ) as Body

import Hydrogen.Schema.Network.HTTP.Timeout
  ( Timeout
  , timeoutMs
  , timeoutSeconds
  , unwrapTimeout
  , defaultTimeout
  , noTimeout
  , isExpired
  , timeoutBounds
  ) as Timeout

import Hydrogen.Schema.Network.HTTP.Status
  ( StatusCode
  , statusCode
  , unwrapStatusCode
  , isInformational
  , isSuccess
  , isRedirect
  , isClientError
  , isServerError
  , status200
  , status201
  , status204
  , status301
  , status302
  , status304
  , status400
  , status401
  , status403
  , status404
  , status500
  , status502
  , status503
  , statusCodeBounds
  ) as Status

import Hydrogen.Schema.Network.HTTP.Request
  ( HTTPRequest
  , request
  , getRequest
  , postRequest
  , putRequest
  , deleteRequest
  ) as Request

import Hydrogen.Schema.Network.HTTP.Response
  ( HTTPResponse
  , response
  , responseBody
  , responseHeader
  , responseHeaders
  ) as Response

import Hydrogen.Schema.Network.HTTP.Result
  ( HTTPResult(HTTPOk, HTTPTimeout, HTTPNetworkError, HTTPCORSError, HTTPAborted)
  , isOk
  , isError
  , mapOk
  , HTTPError(TimeoutError, NetworkFailure, CORSBlocked, RequestAborted, InvalidResponse, StatusError)
  , errorMessage
  ) as Result
