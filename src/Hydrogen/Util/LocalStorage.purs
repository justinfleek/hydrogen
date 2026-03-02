-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // local-storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Raw localStorage utilities
-- |
-- | Provides access to localStorage with raw string operations only.
-- | JSON serialization is forbidden — use Schema atoms with CBOR instead.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.LocalStorage as LS
-- |
-- | -- Store a raw string value
-- | LS.setItemRaw "theme" "dark"
-- |
-- | -- Retrieve a raw string value
-- | maybeTheme :: Maybe String <- LS.getItemRaw "theme"
-- |
-- | -- Remove a value
-- | LS.removeItem "theme"
-- |
-- | -- Clear all storage
-- | LS.clear
-- |
-- | -- Listen for changes
-- | unsubscribe <- LS.onChange "theme" \maybeValue ->
-- |   Console.log $ "Theme changed: " <> show maybeValue
-- |
-- | -- With namespacing
-- | ns <- LS.namespace "myapp"
-- | ns.setItemRaw "setting" "true"
-- | maybeVal <- ns.getItemRaw "setting"  -- Stored as "myapp:setting"
-- | ```
module Hydrogen.Util.LocalStorage
  ( -- * Core Operations (raw strings only)
    getItemRaw
  , setItemRaw
  , removeItem
  , clear
    -- * Change Listening
  , onChange
  , onAnyChange
    -- * Namespacing
  , namespace
  , Namespaced
    -- * Utilities
  , keys
  , length
  , has
  ) where

import Prelude hiding (void)

import Data.Array (filter) as Array
import Data.Maybe (Maybe, isJust)
import Data.Traversable (traverse) as Traversable
import Data.String (take, length) as String
import Effect (Effect)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Namespaced storage interface
-- | Note: For type-safe operations, use the prefixed versions of getItem/setItem
type Namespaced =
  { getItemRaw :: String -> Effect (Maybe String)
  , setItemRaw :: String -> String -> Effect Unit
  , removeItem :: String -> Effect Unit
  , clear :: Effect Unit
  , keys :: Effect (Array String)
  , prefix :: String
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═════════════════════════════════════════════════════════════════════════════

-- BROWSER BOUNDARY: localStorage is a Web Storage API for persistent key-value storage.
foreign import getItemImpl :: String -> Effect (Maybe String)

-- BROWSER BOUNDARY: localStorage is a Web Storage API for persistent key-value storage.
foreign import setItemImpl :: String -> String -> Effect Unit

-- BROWSER BOUNDARY: localStorage is a Web Storage API for persistent key-value storage.
foreign import removeItemImpl :: String -> Effect Unit

-- BROWSER BOUNDARY: localStorage is a Web Storage API for persistent key-value storage.
foreign import clearImpl :: Effect Unit

-- BROWSER BOUNDARY: localStorage is a Web Storage API for persistent key-value storage.
foreign import keysImpl :: Effect (Array String)

-- BROWSER BOUNDARY: localStorage is a Web Storage API for persistent key-value storage.
foreign import lengthImpl :: Effect Int

-- BROWSER BOUNDARY: window.addEventListener("storage") is Web API for
-- cross-tab storage change notifications.
foreign import onChangeImpl 
  :: String 
  -> (Maybe String -> Effect Unit) 
  -> Effect (Effect Unit)

-- BROWSER BOUNDARY: window.addEventListener("storage") is Web API for
-- cross-tab storage change notifications.
foreign import onAnyChangeImpl 
  :: (String -> Maybe String -> Effect Unit) 
  -> Effect (Effect Unit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // core operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a raw string from localStorage
-- |
-- | Returns `Nothing` if the key doesn't exist.
-- |
-- | ```purescript
-- | maybeTheme :: Maybe String <- getItemRaw "theme"
-- | ```
getItemRaw :: String -> Effect (Maybe String)
getItemRaw = getItemImpl

-- | Set a raw string in localStorage
-- |
-- | ```purescript
-- | setItemRaw "theme" "dark"
-- | ```
setItemRaw :: String -> String -> Effect Unit
setItemRaw = setItemImpl

-- | Remove an item from localStorage
removeItem :: String -> Effect Unit
removeItem = removeItemImpl

-- | Clear all items from localStorage
clear :: Effect Unit
clear = clearImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // change listening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Listen for changes to a specific key
-- |
-- | Fires when the key is changed from another tab/window.
-- | Note: Does not fire for changes in the same tab.
-- |
-- | ```purescript
-- | unsubscribe <- onChange "user" \maybeValue ->
-- |   case maybeValue of
-- |     Nothing -> Console.log "User removed"
-- |     Just value -> Console.log $ "User updated: " <> value
-- | ```
onChange :: String -> (Maybe String -> Effect Unit) -> Effect (Effect Unit)
onChange = onChangeImpl

-- | Listen for any storage changes
-- |
-- | Callback receives the key and new value.
onAnyChange :: (String -> Maybe String -> Effect Unit) -> Effect (Effect Unit)
onAnyChange = onAnyChangeImpl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // namespacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a namespaced storage interface
-- |
-- | All keys are prefixed with the namespace.
-- |
-- | ```purescript
-- | ns <- namespace "myapp"
-- | ns.setItemRaw "theme" "dark"  -- Stored as "myapp:theme"
-- | maybeTheme <- ns.getItemRaw "theme"
-- | ns.clear  -- Only clears "myapp:*" keys
-- | ```
namespace :: String -> Effect Namespaced
namespace prefix = pure
  { getItemRaw: \key -> getItemRaw (prefix <> ":" <> key)
  , setItemRaw: \key value -> setItemRaw (prefix <> ":" <> key) value
  , removeItem: \key -> removeItem (prefix <> ":" <> key)
  , clear: clearNamespace prefix
  , keys: getNamespaceKeys prefix
  , prefix
  }

-- | Clear all keys with a given prefix
clearNamespace :: String -> Effect Unit
clearNamespace prefix = do
  allKeys <- keysImpl
  let prefixedKeys = filterPrefix (prefix <> ":") allKeys
  traverse_ removeItem prefixedKeys
  where
  filterPrefix p arr = Array.filter (startsWith p) arr
  
  startsWith :: String -> String -> Boolean
  startsWith p str = String.take (String.length p) str == p
  
  traverse_ :: forall a. (a -> Effect Unit) -> Array a -> Effect Unit
  traverse_ f arr = void $ Traversable.traverse f arr

-- | Get all keys with a given prefix
getNamespaceKeys :: String -> Effect (Array String)
getNamespaceKeys prefix = do
  allKeys <- keysImpl
  pure $ Array.filter (startsWith (prefix <> ":")) allKeys
  where
  startsWith :: String -> String -> Boolean
  startsWith p str = String.take (String.length p) str == p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all keys in localStorage
keys :: Effect (Array String)
keys = keysImpl

-- | Get the number of items in localStorage
length :: Effect Int
length = lengthImpl

-- | Check if a key exists in localStorage
has :: String -> Effect Boolean
has key = isJust <$> getItemImpl key

-- Local void helper
void :: forall a. Effect a -> Effect Unit
void action = do
  _ <- action
  pure unit
