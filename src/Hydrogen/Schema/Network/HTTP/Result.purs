-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                     // result
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Result — Outcomes of HTTP requests including errors.
-- |
-- | Represents all possible outcomes, including network-level failures
-- | that prevent receiving any HTTP response.

module Hydrogen.Schema.Network.HTTP.Result
  ( -- * HTTP Result
    HTTPResult(HTTPOk, HTTPTimeout, HTTPNetworkError, HTTPCORSError, HTTPAborted)
  , isOk
  , isError
  , mapOk
  
  -- * HTTP Error Details
  , HTTPError(TimeoutError, NetworkFailure, CORSBlocked, RequestAborted, InvalidResponse, StatusError)
  , errorMessage
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

import Hydrogen.Schema.Network.HTTP.URL (URL)
import Hydrogen.Schema.Network.HTTP.Timeout (Timeout)
import Hydrogen.Schema.Network.HTTP.Status (StatusCode)
import Hydrogen.Schema.Network.HTTP.Response (HTTPResponse)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // http result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of an HTTP request.
-- |
-- | Represents all possible outcomes, including network-level failures
-- | that prevent receiving any HTTP response.
data HTTPResult
  = HTTPOk HTTPResponse       -- ^ Request succeeded (may still be 4xx/5xx)
  | HTTPTimeout               -- ^ Request timed out
  | HTTPNetworkError          -- ^ Network-level failure
  | HTTPCORSError             -- ^ CORS policy blocked request
  | HTTPAborted               -- ^ Request was cancelled

derive instance eqHTTPResult :: Eq HTTPResult

instance showHTTPResult :: Show HTTPResult where
  show (HTTPOk resp) = "HTTPOk(" <> show resp.status <> ")"
  show HTTPTimeout = "HTTPTimeout"
  show HTTPNetworkError = "HTTPNetworkError"
  show HTTPCORSError = "HTTPCORSError"
  show HTTPAborted = "HTTPAborted"

-- | Did the request complete successfully (receive a response)?
-- |
-- | Note: This returns true even for 4xx/5xx responses. Use isSuccess
-- | on the response status to check for HTTP-level success.
isOk :: HTTPResult -> Boolean
isOk (HTTPOk _) = true
isOk _ = false

-- | Did the request fail at the network level?
isError :: HTTPResult -> Boolean
isError (HTTPOk _) = false
isError _ = true

-- | Transform a successful response.
mapOk :: (HTTPResponse -> HTTPResponse) -> HTTPResult -> HTTPResult
mapOk f (HTTPOk resp) = HTTPOk (f resp)
mapOk _ other = other

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // http error detail
-- ═════════════════════════════════════════════════════════════════════════════

-- | Detailed HTTP error information.
-- |
-- | Provides structured error data for error handling and display.
data HTTPError
  = TimeoutError Timeout          -- ^ Request exceeded timeout
  | NetworkFailure String         -- ^ Network-level error with message
  | CORSBlocked URL               -- ^ CORS prevented request to URL
  | RequestAborted                -- ^ Request was cancelled
  | InvalidResponse String        -- ^ Response could not be parsed
  | StatusError StatusCode String -- ^ HTTP error status with body

derive instance eqHTTPError :: Eq HTTPError

instance showHTTPError :: Show HTTPError where
  show (TimeoutError t) = "TimeoutError(" <> show t <> ")"
  show (NetworkFailure msg) = "NetworkFailure(" <> msg <> ")"
  show (CORSBlocked u) = "CORSBlocked(" <> show u <> ")"
  show RequestAborted = "RequestAborted"
  show (InvalidResponse msg) = "InvalidResponse(" <> msg <> ")"
  show (StatusError code _) = "StatusError(" <> show code <> ")"

-- | Get a human-readable error message.
errorMessage :: HTTPError -> String
errorMessage (TimeoutError _) = "Request timed out"
errorMessage (NetworkFailure msg) = "Network error: " <> msg
errorMessage (CORSBlocked _) = "Request blocked by CORS policy"
errorMessage RequestAborted = "Request was cancelled"
errorMessage (InvalidResponse msg) = "Invalid response: " <> msg
errorMessage (StatusError code _) = "HTTP error " <> show code
