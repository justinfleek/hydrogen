-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // storage // local
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Local Storage — ADT operations for browser localStorage API.
-- |
-- | ## Design Philosophy
-- |
-- | Local storage operations are represented as pure data structures.
-- | The runtime interprets these operations against the actual browser API.
-- | This separation enables:
-- | - Testability without browser dependencies
-- | - Serialization of storage intents
-- | - Deterministic operation sequencing
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Agents can compose storage operations algebraically. The ADT representation
-- | allows for operation batching, conflict detection, and intent logging
-- | without executing side effects.

module Hydrogen.Schema.Storage.Local
  ( -- * Storage Key
    StorageKey
  , storageKey
  , unwrapStorageKey
  , storageKeyToString
  , isValidStorageKey
  , storageKeyNamespace
  
  -- * Storage Value
  , StorageValue
  , storageValue
  , unwrapStorageValue
  , emptyValue
  , isEmptyValue
  , storageValueLength
  
  -- * Local Storage Operations
  , LocalStorageOp(..)
  , getItem
  , setItem
  , removeItem
  , clearStorage
  , hasItem
  , getAllKeys
  
  -- * Operation Introspection
  , opIsRead
  , opIsWrite
  , opIsDestructive
  , opKey
  
  -- * Storage Error
  , LocalStorageError(..)
  , errorMessage
  , isQuotaError
  , isSecurityError
  
  -- * Storage Result
  , StorageResult
  , WriteResult
  , storageSuccess
  , storageFailure
  , writeSuccess
  , isStorageSuccess
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , unit
  , show
  , otherwise
  , not
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Either (Either(Left, Right))
import Data.String (length, null, indexOf, take, Pattern(..)) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // storage key
-- ═════════════════════════════════════════════════════════════════════════════

-- | StorageKey — identifier for stored values.
-- |
-- | Keys should be non-empty strings. By convention, use namespaced keys
-- | to avoid collisions between different parts of an application:
-- | "hydrogen:user:preferences", "myapp:cache:timestamp"
newtype StorageKey = StorageKey String

derive instance eqStorageKey :: Eq StorageKey
derive instance ordStorageKey :: Ord StorageKey

instance showStorageKey :: Show StorageKey where
  show (StorageKey k) = "(StorageKey " <> show k <> ")"

-- | Construct a storage key.
-- |
-- | Returns Nothing for empty keys.
storageKey :: String -> Maybe StorageKey
storageKey s
  | String.null s = Nothing
  | otherwise = Just (StorageKey s)

-- | Unwrap storage key to string.
unwrapStorageKey :: StorageKey -> String
unwrapStorageKey (StorageKey k) = k

-- | Convert to string (alias for unwrap).
storageKeyToString :: StorageKey -> String
storageKeyToString = unwrapStorageKey

-- | Check if a string would be a valid storage key.
isValidStorageKey :: String -> Boolean
isValidStorageKey s = not (String.null s)

-- | Extract namespace from key (text before first colon).
-- |
-- | "hydrogen:user:prefs" -> Just "hydrogen"
-- | "nonamespace" -> Nothing
storageKeyNamespace :: StorageKey -> Maybe String
storageKeyNamespace (StorageKey k) =
  case String.indexOf (String.Pattern ":") k of
    Nothing -> Nothing
    Just idx -> 
      if idx == 0
        then Nothing  -- Empty namespace (key starts with colon)
        else Just (String.take idx k)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // storage value
-- ═════════════════════════════════════════════════════════════════════════════

-- | StorageValue — wrapper for stored string data.
-- |
-- | Local storage only stores strings. JSON serialization happens
-- | at a higher layer. This type ensures we track that the value
-- | came from or is destined for storage.
newtype StorageValue = StorageValue String

derive instance eqStorageValue :: Eq StorageValue
derive instance ordStorageValue :: Ord StorageValue

instance showStorageValue :: Show StorageValue where
  show (StorageValue v) = "(StorageValue " <> show (String.length v) <> " chars)"

-- | Construct a storage value from string.
storageValue :: String -> StorageValue
storageValue = StorageValue

-- | Unwrap storage value to string.
unwrapStorageValue :: StorageValue -> String
unwrapStorageValue (StorageValue v) = v

-- | Empty storage value.
emptyValue :: StorageValue
emptyValue = StorageValue ""

-- | Check if storage value is empty.
isEmptyValue :: StorageValue -> Boolean
isEmptyValue (StorageValue v) = String.null v

-- | Get length of storage value in characters.
storageValueLength :: StorageValue -> Int
storageValueLength (StorageValue v) = String.length v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // local storage operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | LocalStorageOp — ADT representing storage operations.
-- |
-- | Operations are pure data that describe intent. The runtime
-- | executes them against the actual localStorage API.
-- |
-- | This is not parameterized because different operations have different
-- | result types; use the result type documentation to determine expected results.
data LocalStorageOp
  = GetItem StorageKey                    -- ^ Read value for key (returns Maybe StorageValue)
  | SetItem StorageKey StorageValue       -- ^ Write value for key (returns Unit)
  | RemoveItem StorageKey                 -- ^ Delete key (returns Unit)
  | Clear                                 -- ^ Delete all keys (returns Unit)
  | HasItem StorageKey                    -- ^ Check if key exists (returns Boolean)
  | GetAllKeys                            -- ^ List all keys (returns Array StorageKey)

derive instance eqLocalStorageOp :: Eq LocalStorageOp

instance showLocalStorageOp :: Show LocalStorageOp where
  show (GetItem k) = "(GetItem " <> show k <> ")"
  show (SetItem k v) = "(SetItem " <> show k <> " " <> show v <> ")"
  show (RemoveItem k) = "(RemoveItem " <> show k <> ")"
  show Clear = "Clear"
  show (HasItem k) = "(HasItem " <> show k <> ")"
  show GetAllKeys = "GetAllKeys"

-- | Create a GetItem operation.
getItem :: StorageKey -> LocalStorageOp
getItem = GetItem

-- | Create a SetItem operation.
setItem :: StorageKey -> StorageValue -> LocalStorageOp
setItem k v = SetItem k v

-- | Create a RemoveItem operation.
removeItem :: StorageKey -> LocalStorageOp
removeItem = RemoveItem

-- | Create a Clear operation.
clearStorage :: LocalStorageOp
clearStorage = Clear

-- | Create a HasItem operation.
hasItem :: StorageKey -> LocalStorageOp
hasItem = HasItem

-- | Create a GetAllKeys operation.
getAllKeys :: LocalStorageOp
getAllKeys = GetAllKeys

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // operation introspection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if operation is a read (no side effects).
opIsRead :: LocalStorageOp -> Boolean
opIsRead (GetItem _) = true
opIsRead (HasItem _) = true
opIsRead GetAllKeys = true
opIsRead _ = false

-- | Check if operation is a write.
opIsWrite :: LocalStorageOp -> Boolean
opIsWrite (SetItem _ _) = true
opIsWrite (RemoveItem _) = true
opIsWrite Clear = true
opIsWrite _ = false

-- | Check if operation is destructive (removes data).
opIsDestructive :: LocalStorageOp -> Boolean
opIsDestructive (RemoveItem _) = true
opIsDestructive Clear = true
opIsDestructive _ = false

-- | Get the key involved in an operation, if any.
opKey :: LocalStorageOp -> Maybe StorageKey
opKey (GetItem k) = Just k
opKey (SetItem k _) = Just k
opKey (RemoveItem k) = Just k
opKey (HasItem k) = Just k
opKey Clear = Nothing
opKey GetAllKeys = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // storage error
-- ═════════════════════════════════════════════════════════════════════════════

-- | LocalStorageError — errors that can occur during storage operations.
data LocalStorageError
  = StorageNotAvailable         -- ^ localStorage not supported
  | QuotaExceeded               -- ^ Storage quota exceeded
  | SecurityError               -- ^ Access denied (private browsing, etc.)
  | SerializationError String   -- ^ Failed to serialize/deserialize
  | KeyNotFound StorageKey      -- ^ Requested key does not exist

derive instance eqLocalStorageError :: Eq LocalStorageError

instance showLocalStorageError :: Show LocalStorageError where
  show StorageNotAvailable = "StorageNotAvailable"
  show QuotaExceeded = "QuotaExceeded"
  show SecurityError = "SecurityError"
  show (SerializationError msg) = "(SerializationError " <> show msg <> ")"
  show (KeyNotFound k) = "(KeyNotFound " <> show k <> ")"

-- | Get human-readable error message.
errorMessage :: LocalStorageError -> String
errorMessage StorageNotAvailable = "Local storage is not available in this browser"
errorMessage QuotaExceeded = "Storage quota exceeded - cannot save more data"
errorMessage SecurityError = "Access to storage denied - may be in private browsing mode"
errorMessage (SerializationError msg) = "Failed to serialize data: " <> msg
errorMessage (KeyNotFound k) = "Key not found: " <> storageKeyToString k

-- | Check if error is a quota error.
isQuotaError :: LocalStorageError -> Boolean
isQuotaError QuotaExceeded = true
isQuotaError _ = false

-- | Check if error is a security error.
isSecurityError :: LocalStorageError -> Boolean
isSecurityError SecurityError = true
isSecurityError _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // storage result
-- ═════════════════════════════════════════════════════════════════════════════

-- | StorageResult — either success with value or failure with error.
type StorageResult a = Either LocalStorageError a

-- | WriteResult — result for operations that don't return data.
-- |
-- | SetItem, RemoveItem, and Clear operations return Unit on success.
type WriteResult = StorageResult Unit

-- | Create a successful storage result.
storageSuccess :: forall a. a -> StorageResult a
storageSuccess = Right

-- | Create a failed storage result.
storageFailure :: forall a. LocalStorageError -> StorageResult a
storageFailure = Left

-- | Create a successful write result.
-- |
-- | Use for SetItem, RemoveItem, and Clear operations.
writeSuccess :: WriteResult
writeSuccess = Right unit

-- | Check if storage result is successful.
isStorageSuccess :: forall a. StorageResult a -> Boolean
isStorageSuccess (Right _) = true
isStorageSuccess (Left _) = false
