-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // extension // chrome // ffi
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FFI bindings to Chrome Extension APIs.
-- |
-- | Provides typed access to:
-- |   - chrome.runtime.sendMessage
-- |   - chrome.tabs.query
-- |   - chrome.tabs.sendMessage
-- |
-- | All async operations return Aff for composability.

module Extension.Chrome
  ( -- * Tab Operations
    Tab
  , TabId
  , queryActiveTab
  , getActiveTabId
  
  -- * Messaging
  , sendMessageToTab
  , sendMessageToBackground
  
  -- * Types
  , ExtractionData
  , LayerData
  ) where

import Prelude
  ( Unit
  , bind
  , discard
  , pure
  , ($)
  )

import Data.Either (Either(Left, Right))
import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Effect.Exception (error)
import Foreign (Foreign)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Chrome Tab ID
type TabId = Int

-- | Chrome Tab object (subset of fields we need)
type Tab =
  { id :: TabId
  , url :: String
  , title :: String
  , windowId :: Int
  }

-- | Extracted page data
type ExtractionData =
  { url :: String
  , title :: String
  , viewportWidth :: Int
  , viewportHeight :: Int
  , count :: Int
  , layerCount :: Int
  , layers :: Array LayerData
  }

-- | Layer grouping by z-index
type LayerData =
  { zIndex :: Int
  , count :: Int
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // ffi imports
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Query active tab in current window
foreign import queryActiveTabImpl :: (Tab -> Effect Unit) -> (String -> Effect Unit) -> Effect Unit

-- | Send message to a specific tab (content script)
foreign import sendMessageToTabImpl 
  :: TabId 
  -> Foreign 
  -> (Foreign -> Effect Unit) 
  -> (String -> Effect Unit) 
  -> Effect Unit

-- | Send message to background script
foreign import sendMessageToBackgroundImpl 
  :: Foreign 
  -> (Foreign -> Effect Unit) 
  -> (String -> Effect Unit) 
  -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // aff wrappers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Query the active tab in the current window.
-- |
-- | Returns the active tab or fails if no active tab.
queryActiveTab :: Aff Tab
queryActiveTab = makeAff \callback -> do
  queryActiveTabImpl
    (\tab -> callback (Right tab))
    (\err -> callback (Left (error err)))
  pure nonCanceler

-- | Get just the tab ID of the active tab.
getActiveTabId :: Aff TabId
getActiveTabId = do
  tab <- queryActiveTab
  pure tab.id

-- | Send a message to a tab's content script.
-- |
-- | Used to trigger extraction in the content script.
sendMessageToTab :: TabId -> Foreign -> Aff Foreign
sendMessageToTab tabId message = makeAff \callback -> do
  sendMessageToTabImpl tabId message
    (\response -> callback (Right response))
    (\err -> callback (Left (error err)))
  pure nonCanceler

-- | Send a message to the background script.
-- |
-- | Used for operations that need service worker privileges
-- | (screenshot capture, cross-tab communication).
sendMessageToBackground :: Foreign -> Aff Foreign
sendMessageToBackground message = makeAff \callback -> do
  sendMessageToBackgroundImpl message
    (\response -> callback (Right response))
    (\err -> callback (Left (error err)))
  pure nonCanceler
