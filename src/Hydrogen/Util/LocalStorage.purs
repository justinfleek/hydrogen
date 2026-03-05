-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // local-storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Local storage ADT operations.
-- |
-- | Storage operations represented as algebraic data types.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Util.LocalStorage as LS
-- |
-- | getTheme :: LocalStorageOp
-- | getTheme = LS.getItem (LS.storageKey "theme")
-- |
-- | setTheme :: LocalStorageOp
-- | setTheme = LS.setItem (LS.storageKey "theme") (LS.storageValue "dark")
-- | ```
-- |
-- | ## Dependencies
-- | - Hydrogen.Schema.Storage.Local
-- | - Hydrogen.Schema.Storage.Session
-- |
-- | ## Dependents
-- | - Persistence layer
-- | - User preferences
-- | - Cache management

module Hydrogen.Util.LocalStorage
  ( module SchemaLocal
  , module SchemaSession
  -- * Direct Effect-based operations
  , getItemRaw
  , setItemRaw
  , removeItemRaw
  ) where

import Prelude (Unit)
import Data.Maybe (Maybe)
import Effect (Effect)

import Hydrogen.Schema.Storage.Local
  ( StorageKey
  , storageKey
  , unwrapStorageKey
  , storageKeyToString
  , isValidStorageKey
  , storageKeyNamespace
  , StorageValue
  , storageValue
  , unwrapStorageValue
  , emptyValue
  , isEmptyValue
  , storageValueLength
  , LocalStorageOp(GetItem, SetItem, RemoveItem, Clear, HasItem, GetAllKeys)
  , getItem
  , setItem
  , removeItem
  , clearStorage
  , hasItem
  , getAllKeys
  , opIsRead
  , opIsWrite
  , opIsDestructive
  , opKey
  , LocalStorageError(StorageNotAvailable, QuotaExceeded, SecurityError, SerializationError, KeyNotFound)
  , errorMessage
  , isQuotaError
  , isSecurityError
  , StorageResult
  , WriteResult
  , storageSuccess
  , storageFailure
  , writeSuccess
  , isStorageSuccess
  ) as SchemaLocal

import Hydrogen.Schema.Storage.Session
  ( StorageType(LocalStorage, SessionStorage, Cookies)
  , storageTypeLabel
  , storageTypePersists
  , storageTypeCrossTab
  , SessionConfig
  , sessionConfig
  , configStorageType
  , configKey
  , configTTL
  , CookieOptions
  , cookieOptions
  , defaultCookieOptions
  , secureCookieOptions
  , sessionCookieOptions
  , SessionError(SessionExpired, SessionNotFound, SessionCorrupted, SessionStorageUnavailable, CookieBlocked)
  , sessionErrorMessage
  ) as SchemaSession

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // direct effect-based operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get a raw string value from localStorage.
-- |
-- | Bypasses the ADT operation system for simple direct access.
-- | Returns Nothing if key doesn't exist.
foreign import getItemRaw :: String -> Effect (Maybe String)

-- | Set a raw string value in localStorage.
-- |
-- | Bypasses the ADT operation system for simple direct writes.
foreign import setItemRaw :: String -> String -> Effect Unit

-- | Remove a key from localStorage.
-- |
-- | Bypasses the ADT operation system for simple direct removal.
foreign import removeItemRaw :: String -> Effect Unit
