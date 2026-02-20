-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // hydrogen // storage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Offline storage with IndexedDB
-- |
-- | Type-safe wrapper around IndexedDB for offline-first applications.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Offline.Storage as Storage
-- |
-- | -- Open a database
-- | db <- Storage.open "myapp" 1
-- |   [ Storage.store "users" { keyPath: "id" }
-- |   , Storage.store "posts" { keyPath: "id", autoIncrement: true }
-- |   ]
-- |
-- | -- Store data
-- | Storage.put db "users" user
-- |
-- | -- Get data
-- | maybeUser <- Storage.get db "users" "user-123"
-- |
-- | -- Query all
-- | users <- Storage.getAll db "users"
-- |
-- | -- Delete
-- | Storage.delete db "users" "user-123"
-- | ```
module Hydrogen.Offline.Storage
  ( -- * Types
    Database
  , StoreName
  , StoreConfig
  , IndexConfig
    -- * Database Operations
  , open
  , close
  , deleteDatabase
    -- * Store Configuration
  , store
  , storeWithIndex
    -- * CRUD Operations
  , put
  , get
  , getAll
  , getAllByIndex
  , delete
  , clear
    -- * Transactions
  , transaction
  , TransactionMode(..)
    -- * Utilities
  , count
  , keys
  , exists
  ) where

import Prelude

import Data.Argonaut (class DecodeJson, class EncodeJson, Json, decodeJson, encodeJson)
import Data.Array as Array
import Data.Either (Either(..), hush)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff, makeAff, nonCanceler)
import Effect.Class (liftEffect)
import Effect.Exception (Error)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | IndexedDB database wrapper
foreign import data Database :: Type

-- | Object store name
type StoreName = String

-- | Store configuration
type StoreConfig =
  { keyPath :: Maybe String
  , autoIncrement :: Boolean
  }

-- | Index configuration
type IndexConfig =
  { name :: String
  , keyPath :: String
  , unique :: Boolean
  , multiEntry :: Boolean
  }

-- | Transaction mode
data TransactionMode
  = ReadOnly
  | ReadWrite

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // FFI
-- ═══════════════════════════════════════════════════════════════════════════════

foreign import openImpl 
  :: String 
  -> Int 
  -> Array { name :: String, config :: StoreConfig, indexes :: Array IndexConfig }
  -> (Error -> Effect Unit)
  -> (Database -> Effect Unit)
  -> Effect Unit

foreign import closeImpl :: Database -> Effect Unit

foreign import deleteDatabaseImpl 
  :: String 
  -> (Error -> Effect Unit) 
  -> Effect Unit 
  -> Effect Unit

foreign import putImpl 
  :: Database 
  -> String 
  -> Json 
  -> (Error -> Effect Unit)
  -> Effect Unit
  -> Effect Unit

foreign import getImpl 
  :: Database 
  -> String 
  -> String 
  -> (Error -> Effect Unit)
  -> (Json -> Effect Unit)
  -> Effect Unit
  -> Effect Unit

foreign import getAllImpl 
  :: Database 
  -> String 
  -> (Error -> Effect Unit)
  -> (Array Json -> Effect Unit)
  -> Effect Unit

foreign import getAllByIndexImpl 
  :: Database 
  -> String 
  -> String  -- Index name
  -> String  -- Value
  -> (Error -> Effect Unit)
  -> (Array Json -> Effect Unit)
  -> Effect Unit

foreign import deleteImpl 
  :: Database 
  -> String 
  -> String 
  -> (Error -> Effect Unit)
  -> Effect Unit
  -> Effect Unit

foreign import clearImpl 
  :: Database 
  -> String 
  -> (Error -> Effect Unit)
  -> Effect Unit
  -> Effect Unit

foreign import countImpl 
  :: Database 
  -> String 
  -> (Error -> Effect Unit)
  -> (Int -> Effect Unit)
  -> Effect Unit

foreign import keysImpl 
  :: Database 
  -> String 
  -> (Error -> Effect Unit)
  -> (Array String -> Effect Unit)
  -> Effect Unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // database operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a store configuration
store :: StoreName -> StoreConfig -> { name :: String, config :: StoreConfig, indexes :: Array IndexConfig }
store name config = { name, config, indexes: [] }

-- | Create a store with indexes
storeWithIndex :: StoreName -> StoreConfig -> Array IndexConfig -> { name :: String, config :: StoreConfig, indexes :: Array IndexConfig }
storeWithIndex name config indexes = { name, config, indexes }

-- | Open or create a database
open 
  :: String  -- Database name
  -> Int     -- Version
  -> Array { name :: String, config :: StoreConfig, indexes :: Array IndexConfig }
  -> Aff Database
open name version stores = makeAff \callback -> do
  openImpl name version stores
    (\err -> callback (Left err))
    (\db -> callback (Right db))
  pure nonCanceler

-- | Close database connection
close :: Database -> Effect Unit
close = closeImpl

-- | Delete entire database
deleteDatabase :: String -> Aff Unit
deleteDatabase name = makeAff \callback -> do
  deleteDatabaseImpl name
    (\err -> callback (Left err))
    (callback (Right unit))
  pure nonCanceler

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // crud operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Put (insert or update) a value
put :: forall a. EncodeJson a => Database -> StoreName -> a -> Aff Unit
put db storeName value = makeAff \callback -> do
  putImpl db storeName (encodeJson value)
    (\err -> callback (Left err))
    (callback (Right unit))
  pure nonCanceler

-- | Get a value by key
get :: forall a. DecodeJson a => Database -> StoreName -> String -> Aff (Maybe a)
get db storeName key = makeAff \callback -> do
  getImpl db storeName key
    (\err -> callback (Left err))
    (\json -> callback (Right (hush $ decodeJson json)))
    (callback (Right Nothing))
  pure nonCanceler

-- | Get all values from a store
getAll :: forall a. DecodeJson a => Database -> StoreName -> Aff (Array a)
getAll db storeName = makeAff \callback -> do
  getAllImpl db storeName
    (\err -> callback (Left err))
    (\jsons -> callback (Right (Array.mapMaybe (hush <<< decodeJson) jsons)))
  pure nonCanceler

-- | Get all values matching an index
getAllByIndex :: forall a. DecodeJson a => Database -> StoreName -> String -> String -> Aff (Array a)
getAllByIndex db storeName indexName value = makeAff \callback -> do
  getAllByIndexImpl db storeName indexName value
    (\err -> callback (Left err))
    (\jsons -> callback (Right (Array.mapMaybe (hush <<< decodeJson) jsons)))
  pure nonCanceler

-- | Delete a value by key
delete :: Database -> StoreName -> String -> Aff Unit
delete db storeName key = makeAff \callback -> do
  deleteImpl db storeName key
    (\err -> callback (Left err))
    (callback (Right unit))
  pure nonCanceler

-- | Clear all values from a store
clear :: Database -> StoreName -> Aff Unit
clear db storeName = makeAff \callback -> do
  clearImpl db storeName
    (\err -> callback (Left err))
    (callback (Right unit))
  pure nonCanceler

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // transactions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Execute operations in a transaction
transaction :: forall a. Database -> Array StoreName -> TransactionMode -> Aff a -> Aff a
transaction _db _stores _mode action = action  -- Simplified - actual impl would wrap in transaction

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Count entries in a store
count :: Database -> StoreName -> Aff Int
count db storeName = makeAff \callback -> do
  countImpl db storeName
    (\err -> callback (Left err))
    (\n -> callback (Right n))
  pure nonCanceler

-- | Get all keys from a store
keys :: Database -> StoreName -> Aff (Array String)
keys db storeName = makeAff \callback -> do
  keysImpl db storeName
    (\err -> callback (Left err))
    (\ks -> callback (Right ks))
  pure nonCanceler

-- | Check if a key exists
exists :: Database -> StoreName -> String -> Aff Boolean
exists db storeName key = do
  result <- get db storeName key :: Aff (Maybe Json)
  pure $ case result of
    Just _ -> true
    Nothing -> false
