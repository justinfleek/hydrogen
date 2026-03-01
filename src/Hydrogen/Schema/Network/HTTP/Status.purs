-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                     // status
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Status Codes — Bounded status code types with category predicates.
-- |
-- | Per HTTP specification:
-- | - 100-199: Informational
-- | - 200-299: Success
-- | - 300-399: Redirection
-- | - 400-499: Client Error
-- | - 500-599: Server Error

module Hydrogen.Schema.Network.HTTP.Status
  ( -- * Status Code Type
    StatusCode
  , statusCode
  , unwrapStatusCode
  
  -- * Category Predicates
  , isInformational
  , isSuccess
  , isRedirect
  , isClientError
  , isServerError
  
  -- * Common Status Codes
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
  
  -- * Bounds
  , statusCodeBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (>=)
  , (<=)
  , (&&)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // status code
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP status code.
-- |
-- | Bounded to [100, 599] per HTTP specification.
newtype StatusCode = StatusCode Int

derive instance eqStatusCode :: Eq StatusCode
derive instance ordStatusCode :: Ord StatusCode

instance showStatusCode :: Show StatusCode where
  show (StatusCode code) = show code

-- | Create a status code.
-- |
-- | Clamps to valid HTTP range [100, 599].
statusCode :: Int -> StatusCode
statusCode code = StatusCode (Bounded.clampInt 100 599 code)

-- | Extract status code integer.
unwrapStatusCode :: StatusCode -> Int
unwrapStatusCode (StatusCode code) = code

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // category predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this an informational response? (100-199)
isInformational :: StatusCode -> Boolean
isInformational (StatusCode code) = code >= 100 && code <= 199

-- | Is this a success response? (200-299)
isSuccess :: StatusCode -> Boolean
isSuccess (StatusCode code) = code >= 200 && code <= 299

-- | Is this a redirect response? (300-399)
isRedirect :: StatusCode -> Boolean
isRedirect (StatusCode code) = code >= 300 && code <= 399

-- | Is this a client error response? (400-499)
isClientError :: StatusCode -> Boolean
isClientError (StatusCode code) = code >= 400 && code <= 499

-- | Is this a server error response? (500-599)
isServerError :: StatusCode -> Boolean
isServerError (StatusCode code) = code >= 500 && code <= 599

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // common status codes
-- ═════════════════════════════════════════════════════════════════════════════

status200 :: StatusCode
status200 = StatusCode 200

status201 :: StatusCode
status201 = StatusCode 201

status204 :: StatusCode
status204 = StatusCode 204

status301 :: StatusCode
status301 = StatusCode 301

status302 :: StatusCode
status302 = StatusCode 302

status304 :: StatusCode
status304 = StatusCode 304

status400 :: StatusCode
status400 = StatusCode 400

status401 :: StatusCode
status401 = StatusCode 401

status403 :: StatusCode
status403 = StatusCode 403

status404 :: StatusCode
status404 = StatusCode 404

status500 :: StatusCode
status500 = StatusCode 500

status502 :: StatusCode
status502 = StatusCode 502

status503 :: StatusCode
status503 = StatusCode 503

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for HTTP status codes [100, 599]
-- |
-- | Per HTTP specification:
-- | - 100-199: Informational
-- | - 200-299: Success
-- | - 300-399: Redirection
-- | - 400-499: Client Error
-- | - 500-599: Server Error
statusCodeBounds :: Bounded.IntBounds
statusCodeBounds = Bounded.intBounds 100 599 Bounded.Clamps "status"
  "HTTP status code (100-599)"
