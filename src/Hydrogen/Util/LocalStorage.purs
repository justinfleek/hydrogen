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
  ) where

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
