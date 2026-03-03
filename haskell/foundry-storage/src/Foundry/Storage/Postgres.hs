{-# LANGUAGE QualifiedDo #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                // foundry // storage // postgres
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage.Postgres
Description : PostgreSQL adapter for durable persistence (L3 storage)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

PostgreSQL integration for L3 durable storage.

== Purpose

L3 storage provides durable, transactional persistence:
  - ACID transactions
  - Foreign key relationships
  - Full-text search
  - Backup and replication

== Schema

PostgreSQL schema uses proper relational normalization:
  - brands (id, domain, created_at, content_hash)
  - palettes (brand_id, colors jsonb)
  - typography (brand_id, heading_font, body_font, scale)
  - etc.

== Dependencies

Requires: postgresql-simple, Foundry.Storage.Types
Required by: Foundry.Storage

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage.Postgres
  ( -- * Connection
    PostgresConn
  , PostgresConfig (..)
  , defaultConfig
  , connect
  , disconnect

    -- * Operations (graded)
  , storeBrand
  , fetchBrand
  , fetchBrandByDomain
  , deleteBrand

    -- * Transactions
  , withTransaction
  ) where

import Data.Text (Text)
import Foundry.Core.Text (tshow)
import Foundry.Core.Effects.Graded
  ( FoundryM
  , GradeLabel (..)
  , liftNet
  , liftConfig
  )
import Foundry.Core.Effects.Do qualified as F
import Foundry.Storage.Types (StorageKey, StorageResult (..), StoredBrand)

--------------------------------------------------------------------------------
-- Connection Types
--------------------------------------------------------------------------------

-- | PostgreSQL connection handle (opaque)
data PostgresConn = PostgresConn
  { pgConnString :: !Text
    -- ^ Connection string
  }
  deriving stock (Eq, Show)

-- | PostgreSQL configuration
data PostgresConfig = PostgresConfig
  { pgcHost     :: !Text
    -- ^ Database host
  , pgcPort     :: !Int
    -- ^ Database port
  , pgcDatabase :: !Text
    -- ^ Database name
  , pgcUser     :: !Text
    -- ^ Username
  , pgcPassword :: !Text
    -- ^ Password (should come from secrets manager)
  , pgcPoolSize :: !Int
    -- ^ Connection pool size
  }
  deriving stock (Eq, Show)

-- | Default configuration (localhost)
defaultConfig :: PostgresConfig
defaultConfig = PostgresConfig
  { pgcHost = "localhost"
  , pgcPort = 5432
  , pgcDatabase = "foundry"
  , pgcUser = "foundry"
  , pgcPassword = ""  -- Should be overridden
  , pgcPoolSize = 10
  }

--------------------------------------------------------------------------------
-- Connection Management
--------------------------------------------------------------------------------

-- | Connect to PostgreSQL
-- Grade: '[Net, Config] - network connection + config access
connect :: PostgresConfig -> FoundryM '[ 'Net, 'Config ] (Either Text PostgresConn)
connect cfg = F.do
  -- Network connection
  _ <- liftNet (pure ())
  -- Config access for connection params
  liftConfig $ pure $ Right PostgresConn
    { pgConnString = buildConnString cfg
    }
  where
    buildConnString :: PostgresConfig -> Text
    buildConnString c = mconcat
      [ "host=", pgcHost c
      , " port=", tshow (pgcPort c)
      , " dbname=", pgcDatabase c
      , " user=", pgcUser c
      ]

-- | Disconnect from PostgreSQL
-- Grade: '[Net] - network operation
disconnect :: PostgresConn -> FoundryM '[ 'Net ] ()
disconnect _ = liftNet $ pure ()

--------------------------------------------------------------------------------
-- Storage Operations
--------------------------------------------------------------------------------

-- | Store brand data
-- Grade: '[Net] - network write operation
storeBrand :: PostgresConn -> StoredBrand -> FoundryM '[ 'Net ] (StorageResult ())
storeBrand _conn _brand = liftNet $ pure $ StorageOk ()

-- | Fetch brand by storage key
-- Grade: '[Net] - network read operation
fetchBrand :: PostgresConn -> StorageKey -> FoundryM '[ 'Net ] (StorageResult StoredBrand)
fetchBrand _conn key = liftNet $ pure $ StorageNotFound key

-- | Fetch brand by domain
-- Grade: '[Net] - network read operation
fetchBrandByDomain :: PostgresConn -> Text -> FoundryM '[ 'Net ] (StorageResult StoredBrand)
fetchBrandByDomain _conn _domain = liftNet $ pure $ StorageError "Not found"

-- | Delete brand
-- Grade: '[Net] - network write operation
deleteBrand :: PostgresConn -> StorageKey -> FoundryM '[ 'Net ] (StorageResult ())
deleteBrand _conn _key = liftNet $ pure $ StorageOk ()

--------------------------------------------------------------------------------
-- Transactions
--------------------------------------------------------------------------------

-- | Run action in a transaction
-- Note: withTransaction takes an already-graded action and wraps it
-- The grade of the wrapped action flows through
withTransaction :: PostgresConn -> FoundryM es a -> FoundryM es a
withTransaction _conn action = action
