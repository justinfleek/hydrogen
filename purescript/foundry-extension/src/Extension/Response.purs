-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // extension // response
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Response parsing for Chrome extension messages.
-- |
-- | Parses Foreign values from background script into typed records.
-- | Uses FFI for safe JavaScript object property access.

module Extension.Response
  ( -- * Extraction Response
    ExtractionResponse
  , parseExtractionResponse
  
  -- * Layer Info
  , LayerInfo
  ) where

import Prelude
  ( (<$>)
  )

import Data.Either (Either(Left, Right))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Nullable (Nullable, toMaybe)
import Data.Tuple (Tuple(Tuple))

import Foreign (Foreign)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extraction result from content script
type ExtractionResponse =
  { url :: String
  , title :: String
  , elementCount :: Int
  , layerCount :: Int
  , layers :: Array LayerInfo
  }

-- | Layer summary
type LayerInfo =
  { zIndex :: Int
  , count :: Int
  }

-- | Raw response from background script (via FFI)
type RawResponse =
  { success :: Boolean
  , error :: Nullable String
  , data :: Nullable RawData
  }

-- | Raw data payload (via FFI)
type RawData =
  { screenshot :: Nullable String
  , extraction :: Nullable RawExtraction
  }

-- | Raw extraction data (via FFI)
type RawExtraction =
  { url :: String
  , title :: String
  , count :: Int
  , layerCount :: Int
  , layers :: Array RawLayer
  }

-- | Raw layer data (via FFI)
type RawLayer =
  { zIndex :: Int
  , count :: Int
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // ffi imports
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse Foreign to RawResponse.
-- | This is safe because we control the data shape from background.js
foreign import parseRawResponse :: Foreign -> RawResponse

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // parsing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse extraction response from background script.
-- |
-- | Expected format from background.js:
-- |   { success: true, data: { screenshot: "data:...", extraction: {...} } }
-- |   { success: false, error: "message" }
-- |
-- | Returns the extraction result and optional screenshot data URL.
parseExtractionResponse 
  :: Foreign 
  -> Either String (Tuple ExtractionResponse (Maybe String))
parseExtractionResponse foreign' = 
  let 
    raw = parseRawResponse foreign'
  in
    if raw.success
      then parseSuccess raw
      else parseError raw
  where
    parseSuccess raw = 
      case toMaybe raw.data of
        Nothing -> 
          Left "Response success but no data"
        Just payload -> 
          parsePayload payload
    
    parsePayload payload =
      case toMaybe payload.extraction of
        Nothing ->
          Left "Response data but no extraction"
        Just extraction -> 
          let 
            layers = convertLayers extraction.layers
            maybeScreenshot = toMaybe payload.screenshot
            result =
              { url: extraction.url
              , title: extraction.title
              , elementCount: extraction.count
              , layerCount: extraction.layerCount
              , layers: layers
              }
          in
            Right (Tuple result maybeScreenshot)
    
    parseError raw = 
      case toMaybe raw.error of
        Just msg -> Left msg
        Nothing -> Left "Unknown error"

-- | Convert raw layers to typed layers.
convertLayers :: Array RawLayer -> Array LayerInfo
convertLayers rawLayers = 
  convertLayer <$> rawLayers
  where
    convertLayer :: RawLayer -> LayerInfo
    convertLayer raw = 
      { zIndex: raw.zIndex
      , count: raw.count
      }
