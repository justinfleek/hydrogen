-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                       // body
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Request Body — HTTP request body types.
-- |
-- | Represents the various content types that can be sent in a request body.

module Hydrogen.Schema.Network.HTTP.Body
  ( RequestBody(..)
  , jsonBody
  , textBody
  , formBody
  , emptyBody
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , (<>)
  )

import Data.Tuple (Tuple)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // request body
-- ═════════════════════════════════════════════════════════════════════════════

-- | HTTP request body types
-- |
-- | Represents the various content types that can be sent in a request body.
data RequestBody
  = JSONBody String      -- ^ JSON-encoded string
  | TextBody String      -- ^ Plain text
  | FormBody (Array (Tuple String String))  -- ^ Form data
  | EmptyBody            -- ^ No body

derive instance eqRequestBody :: Eq RequestBody

instance showRequestBody :: Show RequestBody where
  show (JSONBody _) = "JSONBody(...)"
  show (TextBody t) = "TextBody(" <> t <> ")"
  show (FormBody _) = "FormBody(...)"
  show EmptyBody = "EmptyBody"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // body constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a JSON body.
jsonBody :: String -> RequestBody
jsonBody = JSONBody

-- | Create a text body.
textBody :: String -> RequestBody
textBody = TextBody

-- | Create a form body from key-value pairs.
formBody :: Array (Tuple String String) -> RequestBody
formBody = FormBody

-- | Empty request body.
emptyBody :: RequestBody
emptyBody = EmptyBody
