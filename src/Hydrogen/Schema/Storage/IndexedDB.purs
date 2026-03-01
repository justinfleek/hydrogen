-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // storage // indexeddb
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | IndexedDB — ADT types for browser IndexedDB operations.
-- |
-- | ## Design Philosophy
-- |
-- | IndexedDB is a low-level, transactional database in the browser.
-- | This module represents database configuration and operations as pure
-- | data structures, allowing:
-- | - Schema definition without database connection
-- | - Version migration planning
-- | - Query composition and optimization
-- |
-- | ## At Billion-Agent Scale
-- |
-- | IndexedDB operations become declarative intents. Agents can reason
-- | about database schemas, plan migrations, and compose queries
-- | without executing side effects.

module Hydrogen.Schema.Storage.IndexedDB
  ( -- * Database Name
    DatabaseName
  , databaseName
  , unwrapDatabaseName
  , isValidDatabaseName
  
  -- * Database Version
  , Version
  , version
  , unwrapVersion
  , versionBounds
  , nextVersion
  , initialVersion
  
  -- * Store Name
  , StoreName
  , storeName
  , unwrapStoreName
  , isValidStoreName
  
  -- * Key Path
  , KeyPath(..)
  , keyPathSingle
  , keyPathCompound
  , keyPathAutoIncrement
  , isAutoIncrement
  , keyPathFields
  
  -- * Index Config
  , IndexConfig
  , indexConfig
  , indexName
  , indexKeyPath
  , indexUnique
  , indexMultiEntry
  
  -- * Store Config
  , StoreConfig
  , storeConfig
  , storeConfigName
  , storeConfigKeyPath
  , storeConfigIndexes
  , storeHasIndex
  
  -- * IndexedDB Config
  , IndexedDBConfig
  , indexedDBConfig
  , dbConfigName
  , dbConfigVersion
  , dbConfigStores
  , dbHasStore
  
  -- * Transaction Mode
  , TransactionMode(..)
  , transactionModeLabel
  , isReadOnly
  
  -- * IndexedDB Operations
  , IndexedDBOp(..)
  , opStoreName
  , opIsRead
  , opIsWrite
  
  -- * IndexedDB Error
  , IndexedDBError(..)
  , indexedDBErrorMessage
  , isVersionError
  , isNotFoundError
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , not
  , (==)
  , (+)
  , (<>)
  )

import Data.Array (any) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (null) as String
import Hydrogen.Schema.Bounded (clampInt, IntBounds, intBounds, BoundsBehavior(Clamps)) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // database name
-- ═════════════════════════════════════════════════════════════════════════════

-- | DatabaseName — identifier for an IndexedDB database.
-- |
-- | Database names must be non-empty strings.
newtype DatabaseName = DatabaseName String

derive instance eqDatabaseName :: Eq DatabaseName
derive instance ordDatabaseName :: Ord DatabaseName

instance showDatabaseName :: Show DatabaseName where
  show (DatabaseName n) = "(DatabaseName " <> show n <> ")"

-- | Construct a database name.
-- |
-- | Returns Nothing for empty names.
databaseName :: String -> Maybe DatabaseName
databaseName s
  | String.null s = Nothing
  | otherwise = Just (DatabaseName s)

-- | Unwrap database name to string.
unwrapDatabaseName :: DatabaseName -> String
unwrapDatabaseName (DatabaseName n) = n

-- | Check if a string would be a valid database name.
isValidDatabaseName :: String -> Boolean
isValidDatabaseName s = not (String.null s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // version
-- ═════════════════════════════════════════════════════════════════════════════

-- | Version — database schema version number.
-- |
-- | Versions are positive integers starting at 1. IndexedDB triggers
-- | upgrade events when opening a database with a higher version.
newtype Version = Version Int

derive instance eqVersion :: Eq Version
derive instance ordVersion :: Ord Version

instance showVersion :: Show Version where
  show (Version v) = "(Version " <> show v <> ")"

-- | Bounds for version numbers (1 to max safe integer).
versionBounds :: Bounded.IntBounds
versionBounds = Bounded.intBounds 1 2147483647 Bounded.Clamps "Version" "Database version (positive integer)"

-- | Construct a bounded version.
-- |
-- | Versions less than 1 are clamped to 1.
version :: Int -> Version
version v = Version (Bounded.clampInt 1 2147483647 v)

-- | Unwrap version to Int.
unwrapVersion :: Version -> Int
unwrapVersion (Version v) = v

-- | Get the next version number.
nextVersion :: Version -> Version
nextVersion (Version v) = Version (Bounded.clampInt 1 2147483647 (v + 1))

-- | Initial version (1).
initialVersion :: Version
initialVersion = Version 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // store name
-- ═════════════════════════════════════════════════════════════════════════════

-- | StoreName — identifier for an object store within a database.
newtype StoreName = StoreName String

derive instance eqStoreName :: Eq StoreName
derive instance ordStoreName :: Ord StoreName

instance showStoreName :: Show StoreName where
  show (StoreName n) = "(StoreName " <> show n <> ")"

-- | Construct a store name.
storeName :: String -> Maybe StoreName
storeName s
  | String.null s = Nothing
  | otherwise = Just (StoreName s)

-- | Unwrap store name to string.
unwrapStoreName :: StoreName -> String
unwrapStoreName (StoreName n) = n

-- | Check if string would be a valid store name.
isValidStoreName :: String -> Boolean
isValidStoreName s = not (String.null s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // key path
-- ═════════════════════════════════════════════════════════════════════════════

-- | KeyPath — how objects are keyed in an object store.
-- |
-- | IndexedDB supports several keying strategies:
-- | - Single field path: objects keyed by a property
-- | - Compound path: objects keyed by multiple properties
-- | - Auto-increment: database generates sequential keys
data KeyPath
  = SingleKeyPath String           -- ^ Single property name
  | CompoundKeyPath (Array String) -- ^ Multiple property names
  | AutoIncrement                  -- ^ Database-generated keys

derive instance eqKeyPath :: Eq KeyPath

instance showKeyPath :: Show KeyPath where
  show (SingleKeyPath p) = "(SingleKeyPath " <> show p <> ")"
  show (CompoundKeyPath ps) = "(CompoundKeyPath " <> show ps <> ")"
  show AutoIncrement = "AutoIncrement"

-- | Create a single-field key path.
keyPathSingle :: String -> KeyPath
keyPathSingle = SingleKeyPath

-- | Create a compound key path.
keyPathCompound :: Array String -> KeyPath
keyPathCompound = CompoundKeyPath

-- | Create an auto-increment key path.
keyPathAutoIncrement :: KeyPath
keyPathAutoIncrement = AutoIncrement

-- | Check if key path uses auto-increment.
isAutoIncrement :: KeyPath -> Boolean
isAutoIncrement AutoIncrement = true
isAutoIncrement _ = false

-- | Get the field names from a key path.
keyPathFields :: KeyPath -> Array String
keyPathFields (SingleKeyPath p) = [p]
keyPathFields (CompoundKeyPath ps) = ps
keyPathFields AutoIncrement = []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // index config
-- ═════════════════════════════════════════════════════════════════════════════

-- | IndexConfig — configuration for an object store index.
-- |
-- | Indexes allow efficient queries on non-key properties.
type IndexConfig =
  { name :: String            -- ^ Index name
  , keyPath :: KeyPath        -- ^ Property or properties to index
  , unique :: Boolean         -- ^ Enforce uniqueness
  , multiEntry :: Boolean     -- ^ Create entry for each array element
  }

-- | Construct an index config.
indexConfig :: String -> KeyPath -> Boolean -> Boolean -> IndexConfig
indexConfig n kp u me =
  { name: n
  , keyPath: kp
  , unique: u
  , multiEntry: me
  }

-- | Get index name.
indexName :: IndexConfig -> String
indexName cfg = cfg.name

-- | Get index key path.
indexKeyPath :: IndexConfig -> KeyPath
indexKeyPath cfg = cfg.keyPath

-- | Check if index enforces uniqueness.
indexUnique :: IndexConfig -> Boolean
indexUnique cfg = cfg.unique

-- | Check if index is multi-entry.
indexMultiEntry :: IndexConfig -> Boolean
indexMultiEntry cfg = cfg.multiEntry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // store config
-- ═════════════════════════════════════════════════════════════════════════════

-- | StoreConfig — configuration for an object store.
type StoreConfig =
  { name :: StoreName         -- ^ Store name
  , keyPath :: KeyPath        -- ^ Primary key path
  , indexes :: Array IndexConfig  -- ^ Secondary indexes
  }

-- | Construct a store config.
storeConfig :: StoreName -> KeyPath -> Array IndexConfig -> StoreConfig
storeConfig n kp idxs =
  { name: n
  , keyPath: kp
  , indexes: idxs
  }

-- | Get store name from config.
storeConfigName :: StoreConfig -> StoreName
storeConfigName cfg = cfg.name

-- | Get key path from config.
storeConfigKeyPath :: StoreConfig -> KeyPath
storeConfigKeyPath cfg = cfg.keyPath

-- | Get indexes from config.
storeConfigIndexes :: StoreConfig -> Array IndexConfig
storeConfigIndexes cfg = cfg.indexes

-- | Check if store has an index with given name.
storeHasIndex :: String -> StoreConfig -> Boolean
storeHasIndex indexNameToFind cfg =
  Array.any (\idx -> idx.name == indexNameToFind) cfg.indexes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // indexeddb config
-- ═════════════════════════════════════════════════════════════════════════════

-- | IndexedDBConfig — complete database configuration.
-- |
-- | Describes the database schema declaratively.
type IndexedDBConfig =
  { name :: DatabaseName
  , version :: Version
  , stores :: Array StoreConfig
  }

-- | Construct an IndexedDB config.
indexedDBConfig :: DatabaseName -> Version -> Array StoreConfig -> IndexedDBConfig
indexedDBConfig n v stores =
  { name: n
  , version: v
  , stores: stores
  }

-- | Get database name from config.
dbConfigName :: IndexedDBConfig -> DatabaseName
dbConfigName cfg = cfg.name

-- | Get database version from config.
dbConfigVersion :: IndexedDBConfig -> Version
dbConfigVersion cfg = cfg.version

-- | Get store configs from config.
dbConfigStores :: IndexedDBConfig -> Array StoreConfig
dbConfigStores cfg = cfg.stores

-- | Check if database config has a store with given name.
dbHasStore :: StoreName -> IndexedDBConfig -> Boolean
dbHasStore storeNameToFind cfg =
  Array.any (\store -> store.name == storeNameToFind) cfg.stores

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // transaction mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | TransactionMode — read/write mode for IndexedDB transactions.
data TransactionMode
  = ReadOnly           -- ^ Read-only access (can be concurrent)
  | ReadWrite          -- ^ Read-write access (exclusive)
  | VersionChange      -- ^ Schema modification (upgrade only)

derive instance eqTransactionMode :: Eq TransactionMode
derive instance ordTransactionMode :: Ord TransactionMode

instance showTransactionMode :: Show TransactionMode where
  show = transactionModeLabel

-- | Get display label for transaction mode.
transactionModeLabel :: TransactionMode -> String
transactionModeLabel ReadOnly = "readonly"
transactionModeLabel ReadWrite = "readwrite"
transactionModeLabel VersionChange = "versionchange"

-- | Check if transaction mode is read-only.
isReadOnly :: TransactionMode -> Boolean
isReadOnly ReadOnly = true
isReadOnly _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // indexeddb operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | IndexedDBOp — ADT representing IndexedDB operations.
-- |
-- | Operations are pure data describing intent. Values are represented
-- | as strings (JSON-serialized) since IndexedDB stores structured clones.
data IndexedDBOp
  = Get StoreName String              -- ^ Get record by key
  | GetAll StoreName                  -- ^ Get all records from store
  | Put StoreName String              -- ^ Insert or update record (JSON value)
  | Add StoreName String              -- ^ Insert new record (fails if exists)
  | Delete StoreName String           -- ^ Delete record by key
  | ClearStore StoreName              -- ^ Delete all records in store
  | Count StoreName                   -- ^ Count records in store
  | OpenCursor StoreName              -- ^ Open cursor for iteration

derive instance eqIndexedDBOp :: Eq IndexedDBOp

instance showIndexedDBOp :: Show IndexedDBOp where
  show (Get sn k) = "(Get " <> show sn <> " " <> show k <> ")"
  show (GetAll sn) = "(GetAll " <> show sn <> ")"
  show (Put sn _) = "(Put " <> show sn <> " <value>)"
  show (Add sn _) = "(Add " <> show sn <> " <value>)"
  show (Delete sn k) = "(Delete " <> show sn <> " " <> show k <> ")"
  show (ClearStore sn) = "(ClearStore " <> show sn <> ")"
  show (Count sn) = "(Count " <> show sn <> ")"
  show (OpenCursor sn) = "(OpenCursor " <> show sn <> ")"

-- | Get the store name from an operation.
opStoreName :: IndexedDBOp -> StoreName
opStoreName (Get sn _) = sn
opStoreName (GetAll sn) = sn
opStoreName (Put sn _) = sn
opStoreName (Add sn _) = sn
opStoreName (Delete sn _) = sn
opStoreName (ClearStore sn) = sn
opStoreName (Count sn) = sn
opStoreName (OpenCursor sn) = sn

-- | Check if operation is a read.
opIsRead :: IndexedDBOp -> Boolean
opIsRead (Get _ _) = true
opIsRead (GetAll _) = true
opIsRead (Count _) = true
opIsRead (OpenCursor _) = true
opIsRead _ = false

-- | Check if operation is a write.
opIsWrite :: IndexedDBOp -> Boolean
opIsWrite (Put _ _) = true
opIsWrite (Add _ _) = true
opIsWrite (Delete _ _) = true
opIsWrite (ClearStore _) = true
opIsWrite _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // indexeddb error
-- ═════════════════════════════════════════════════════════════════════════════

-- | IndexedDBError — errors that can occur during IndexedDB operations.
data IndexedDBError
  = DatabaseNotFound DatabaseName       -- ^ Database does not exist
  | StoreNotFound StoreName             -- ^ Object store does not exist
  | VersionError Version Version        -- ^ Version mismatch (expected, actual)
  | ConstraintError String              -- ^ Unique constraint violation
  | QuotaExceededError                  -- ^ Storage quota exceeded
  | TransactionAborted String           -- ^ Transaction was aborted
  | InvalidState String                 -- ^ Invalid operation for current state
  | DataError String                    -- ^ Invalid data provided
  | ReadOnlyError                       -- ^ Attempted write in read-only transaction

derive instance eqIndexedDBError :: Eq IndexedDBError

instance showIndexedDBError :: Show IndexedDBError where
  show (DatabaseNotFound name) = "(DatabaseNotFound " <> show name <> ")"
  show (StoreNotFound name) = "(StoreNotFound " <> show name <> ")"
  show (VersionError expected actual) = "(VersionError expected=" <> show expected <> " actual=" <> show actual <> ")"
  show (ConstraintError msg) = "(ConstraintError " <> show msg <> ")"
  show QuotaExceededError = "QuotaExceededError"
  show (TransactionAborted msg) = "(TransactionAborted " <> show msg <> ")"
  show (InvalidState msg) = "(InvalidState " <> show msg <> ")"
  show (DataError msg) = "(DataError " <> show msg <> ")"
  show ReadOnlyError = "ReadOnlyError"

-- | Get human-readable error message.
indexedDBErrorMessage :: IndexedDBError -> String
indexedDBErrorMessage (DatabaseNotFound name) = "Database not found: " <> unwrapDatabaseName name
indexedDBErrorMessage (StoreNotFound name) = "Object store not found: " <> unwrapStoreName name
indexedDBErrorMessage (VersionError expected actual) = 
  "Version mismatch: expected " <> show (unwrapVersion expected) <> ", got " <> show (unwrapVersion actual)
indexedDBErrorMessage (ConstraintError msg) = "Constraint violation: " <> msg
indexedDBErrorMessage QuotaExceededError = "Storage quota exceeded"
indexedDBErrorMessage (TransactionAborted msg) = "Transaction aborted: " <> msg
indexedDBErrorMessage (InvalidState msg) = "Invalid state: " <> msg
indexedDBErrorMessage (DataError msg) = "Invalid data: " <> msg
indexedDBErrorMessage ReadOnlyError = "Cannot modify data in read-only transaction"

-- | Check if error is a version error.
isVersionError :: IndexedDBError -> Boolean
isVersionError (VersionError _ _) = true
isVersionError _ = false

-- | Check if error is a not-found error.
isNotFoundError :: IndexedDBError -> Boolean
isNotFoundError (DatabaseNotFound _) = true
isNotFoundError (StoreNotFound _) = true
isNotFoundError _ = false
