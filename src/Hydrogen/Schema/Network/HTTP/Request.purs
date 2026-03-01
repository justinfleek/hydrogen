-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                    // request
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | HTTP Request — Complete request specification as pure data.
-- |
-- | Pure data describing a request. The runtime interprets this
-- | to execute the actual network call.

module Hydrogen.Schema.Network.HTTP.Request
  ( HTTPRequest
  , request
  , getRequest
  , postRequest
  , putRequest
  , deleteRequest
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Network.HTTP.Methods (HTTPMethod(GET, POST, PUT, DELETE))
import Hydrogen.Schema.Network.HTTP.URL (URL)
import Hydrogen.Schema.Network.HTTP.Headers (Header, contentTypeJSON)
import Hydrogen.Schema.Network.HTTP.Body (RequestBody(JSONBody))
import Hydrogen.Schema.Network.HTTP.Timeout (Timeout)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // http request
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete HTTP request specification.
-- |
-- | Pure data describing a request. The runtime interprets this
-- | to execute the actual network call.
type HTTPRequest =
  { method :: HTTPMethod
  , url :: URL
  , headers :: Array Header
  , body :: Maybe RequestBody
  , timeout :: Maybe Timeout
  }

-- | Create an HTTP request with all parameters.
request :: HTTPMethod -> URL -> Array Header -> Maybe RequestBody -> Maybe Timeout -> HTTPRequest
request method reqUrl headers body timeout =
  { method
  , url: reqUrl
  , headers
  , body
  , timeout
  }

-- | Create a GET request.
getRequest :: URL -> Array Header -> HTTPRequest
getRequest reqUrl headers = request GET reqUrl headers Nothing Nothing

-- | Create a POST request with JSON body.
postRequest :: URL -> Array Header -> String -> HTTPRequest
postRequest reqUrl headers json = 
  request POST reqUrl (headers <> [contentTypeJSON]) (Just (JSONBody json)) Nothing

-- | Create a PUT request with JSON body.
putRequest :: URL -> Array Header -> String -> HTTPRequest
putRequest reqUrl headers json =
  request PUT reqUrl (headers <> [contentTypeJSON]) (Just (JSONBody json)) Nothing

-- | Create a DELETE request.
deleteRequest :: URL -> Array Header -> HTTPRequest
deleteRequest reqUrl headers = request DELETE reqUrl headers Nothing Nothing
