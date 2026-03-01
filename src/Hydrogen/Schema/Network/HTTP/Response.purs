-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                   // response
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Response — Complete response data from HTTP calls.
-- |
-- | Contains status, headers, and body from a successful HTTP call.

module Hydrogen.Schema.Network.HTTP.Response
  ( HTTPResponse
  , response
  , responseBody
  , responseHeader
  , responseHeaders
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( map
  , (==)
  )

import Data.Array (find) as Array
import Data.Maybe (Maybe)
import Data.Tuple (fst, snd)

import Hydrogen.Schema.Network.HTTP.URL (URL)
import Hydrogen.Schema.Network.HTTP.Headers (Header, unwrapHeaderName, unwrapHeaderValue)
import Hydrogen.Schema.Network.HTTP.Status (StatusCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // http response
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete HTTP response.
-- |
-- | Contains status, headers, and body from a successful HTTP call.
type HTTPResponse =
  { status :: StatusCode
  , headers :: Array Header
  , body :: String
  , url :: URL                -- ^ Final URL (after redirects)
  }

-- | Create an HTTP response.
response :: StatusCode -> Array Header -> String -> URL -> HTTPResponse
response status headers body finalUrl =
  { status
  , headers
  , body
  , url: finalUrl
  }

-- | Extract response body.
responseBody :: HTTPResponse -> String
responseBody r = r.body

-- | Find a specific header in the response.
responseHeader :: String -> HTTPResponse -> Maybe String
responseHeader name resp =
  map (\h -> unwrapHeaderValue (snd h)) 
    (Array.find (\h -> unwrapHeaderName (fst h) == name) resp.headers)

-- | Get all response headers.
responseHeaders :: HTTPResponse -> Array Header
responseHeaders r = r.headers
