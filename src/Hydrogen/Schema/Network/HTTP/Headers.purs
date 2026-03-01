-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                    // headers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Headers — Header name/value pairs and common header constructors.
-- |
-- | Provides typed wrappers for HTTP headers with convenience functions
-- | for commonly-used headers like Content-Type and Authorization.

module Hydrogen.Schema.Network.HTTP.Headers
  ( -- * Header Types
    HeaderName
  , headerName
  , unwrapHeaderName
  , HeaderValue
  , headerValue
  , unwrapHeaderValue
  , Header
  , header
  
  -- * Common Headers
  , contentTypeJSON
  , contentTypeForm
  , contentTypeText
  , acceptJSON
  , acceptHTML
  , authorizationBearer
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  )

import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // header types
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP header name (case-insensitive by convention)
newtype HeaderName = HeaderName String

derive instance eqHeaderName :: Eq HeaderName
derive instance ordHeaderName :: Ord HeaderName

instance showHeaderName :: Show HeaderName where
  show (HeaderName n) = n

-- | Create a header name.
headerName :: String -> HeaderName
headerName = HeaderName

-- | Extract header name string.
unwrapHeaderName :: HeaderName -> String
unwrapHeaderName (HeaderName n) = n

-- | HTTP header value
newtype HeaderValue = HeaderValue String

derive instance eqHeaderValue :: Eq HeaderValue
derive instance ordHeaderValue :: Ord HeaderValue

instance showHeaderValue :: Show HeaderValue where
  show (HeaderValue v) = v

-- | Create a header value.
headerValue :: String -> HeaderValue
headerValue = HeaderValue

-- | Extract header value string.
unwrapHeaderValue :: HeaderValue -> String
unwrapHeaderValue (HeaderValue v) = v

-- | HTTP header as name-value pair
type Header = Tuple HeaderName HeaderValue

-- | Create a header from name and value strings.
header :: String -> String -> Header
header name value = Tuple (HeaderName name) (HeaderValue value)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common headers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content-Type: application/json
contentTypeJSON :: Header
contentTypeJSON = header "Content-Type" "application/json"

-- | Content-Type: application/x-www-form-urlencoded
contentTypeForm :: Header
contentTypeForm = header "Content-Type" "application/x-www-form-urlencoded"

-- | Content-Type: text/plain
contentTypeText :: Header
contentTypeText = header "Content-Type" "text/plain"

-- | Accept: application/json
acceptJSON :: Header
acceptJSON = header "Accept" "application/json"

-- | Accept: text/html
acceptHTML :: Header
acceptHTML = header "Accept" "text/html"

-- | Authorization: Bearer {token}
authorizationBearer :: String -> Header
authorizationBearer token = header "Authorization" ("Bearer " <> token)
