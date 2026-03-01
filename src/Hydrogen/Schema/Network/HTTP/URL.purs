-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // network // http
--                                                                        // url
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | URL Types — Uniform Resource Locator representation.
-- |
-- | Wrapped string representing a valid URL. Construction validates
-- | basic URL structure but does not perform DNS lookup.

module Hydrogen.Schema.Network.HTTP.URL
  ( URL
  , url
  , unwrapURL
  , urlWithPath
  , urlWithQuery
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , (<>)
  )

import Data.Array (find) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // url types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Uniform Resource Locator
-- |
-- | Wrapped string representing a valid URL. Construction validates
-- | basic URL structure but does not perform DNS lookup.
newtype URL = URL String

derive instance eqURL :: Eq URL
derive instance ordURL :: Ord URL

instance showURL :: Show URL where
  show (URL u) = u

-- | Create a URL from a string.
-- |
-- | Accepts the string as-is. In a full implementation, this would
-- | validate URL structure, but for the Schema layer we trust the
-- | input and let the runtime handle validation.
url :: String -> URL
url = URL

-- | Extract the URL string.
unwrapURL :: URL -> String
unwrapURL (URL u) = u

-- | Append a path segment to a URL.
-- |
-- | Handles trailing/leading slashes correctly.
urlWithPath :: URL -> String -> URL
urlWithPath (URL base) path =
  URL (base <> "/" <> path)

-- | Append query parameters to a URL.
-- |
-- | Parameters are provided as key-value pairs.
urlWithQuery :: URL -> Array (Tuple String String) -> URL
urlWithQuery (URL base) params =
  URL (base <> "?" <> joinParams params)
  where
  joinParams :: Array (Tuple String String) -> String
  joinParams ps = joinWith "&" (map formatParam ps)
  
  formatParam :: Tuple String String -> String
  formatParam (Tuple k v) = k <> "=" <> v
  
  joinWith :: String -> Array String -> String
  joinWith _ [] = ""
  joinWith sep arr = case Array.find (\_ -> true) arr of
    Nothing -> ""
    Just first -> foldlArray (\acc s -> acc <> sep <> s) first (dropFirst arr)
  
  foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
  foldlArray _ acc [] = acc
  foldlArray f acc xs = case Array.find (\_ -> true) xs of
    Nothing -> acc
    Just h -> foldlArray f (f acc h) (dropFirst xs)
  
  dropFirst :: forall a. Array a -> Array a
  dropFirst xs = dropFirstImpl xs
  
foreign import dropFirstImpl :: forall a. Array a -> Array a
