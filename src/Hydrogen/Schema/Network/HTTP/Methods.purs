-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                    // methods
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Methods — Request method types as defined in RFC 7231.
-- |
-- | Each method has semantic meaning that affects caching, idempotency,
-- | and whether a request body is expected.

module Hydrogen.Schema.Network.HTTP.Methods
  ( HTTPMethod(GET, POST, PUT, PATCH, DELETE, HEAD, OPTIONS)
  , isIdempotent
  , isSafe
  , hasRequestBody
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // http methods
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP request methods as defined in RFC 7231.
-- |
-- | Each method has semantic meaning that affects caching, idempotency,
-- | and whether a request body is expected.
data HTTPMethod
  = GET      -- ^ Retrieve resource (safe, idempotent)
  | POST     -- ^ Submit data (not safe, not idempotent)
  | PUT      -- ^ Replace resource (idempotent)
  | PATCH    -- ^ Partial update (not idempotent)
  | DELETE   -- ^ Remove resource (idempotent)
  | HEAD     -- ^ GET without body (safe, idempotent)
  | OPTIONS  -- ^ Describe communication options (safe, idempotent)

derive instance eqHTTPMethod :: Eq HTTPMethod
derive instance ordHTTPMethod :: Ord HTTPMethod

instance showHTTPMethod :: Show HTTPMethod where
  show GET = "GET"
  show POST = "POST"
  show PUT = "PUT"
  show PATCH = "PATCH"
  show DELETE = "DELETE"
  show HEAD = "HEAD"
  show OPTIONS = "OPTIONS"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // method queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this method idempotent? (multiple identical requests = same effect)
-- |
-- | Idempotent methods can be safely retried on network failure.
isIdempotent :: HTTPMethod -> Boolean
isIdempotent GET = true
isIdempotent PUT = true
isIdempotent DELETE = true
isIdempotent HEAD = true
isIdempotent OPTIONS = true
isIdempotent POST = false
isIdempotent PATCH = false

-- | Is this method safe? (no server-side effects)
-- |
-- | Safe methods can be prefetched, cached, and repeated freely.
isSafe :: HTTPMethod -> Boolean
isSafe GET = true
isSafe HEAD = true
isSafe OPTIONS = true
isSafe _ = false

-- | Does this method typically have a request body?
hasRequestBody :: HTTPMethod -> Boolean
hasRequestBody POST = true
hasRequestBody PUT = true
hasRequestBody PATCH = true
hasRequestBody _ = false
