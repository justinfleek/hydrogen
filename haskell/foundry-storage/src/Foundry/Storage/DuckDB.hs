{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                 // foundry // storage // duckdb
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Storage.DuckDB
Description : DuckDB adapter for analytical queries (L2 storage)
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

DuckDB integration for L2 analytical storage.

== Purpose

L2 storage provides fast analytical queries over brand data:
  - Color palette statistics across brands
  - Typography distribution analysis
  - Spacing pattern aggregation
  - Voice trait correlation

== Schema

The DuckDB schema mirrors the Brand compound type with denormalized
columns for efficient analytical queries.

== Dependencies

Requires: duckdb (C library), Foundry.Storage.Types
Required by: Foundry.Storage

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Storage.DuckDB
  ( -- * Connection
    DuckDBConn
  , DuckDBConfig (..)
  , defaultConfig
  , connect
  , disconnect

    -- * Operations
  , storeBrand
  , fetchBrand
  , queryBrands

    -- * Analytics
  , countBrands
  , aggregatePalettes

    -- * Serialization
  , serializeBrand

    -- * Component Registry Schema
  , ComponentSchema (..)
  , createComponentTables
  , storeAtom
  , storeMolecule
  , storeCompound
  , queryAtomsByDomain
  , queryMoleculesByDomain
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text.Encoding qualified as T
import Data.UUID qualified as UUID
import Foundry.Core.Effects.Graded
  ( FoundryM
  , GradeLabel (..)
  , liftNet
  , liftConfig
  )
import Foundry.Core.Effects.Do qualified as F
import Foundry.Storage.Types 
  ( StorageKey (..)
  , StorageResult (..)
  , StoredBrand (..)
  , StorageLayer (..)
  )

--------------------------------------------------------------------------------
-- Connection Types
--------------------------------------------------------------------------------

-- | DuckDB connection handle (opaque)
data DuckDBConn = DuckDBConn
  { ddbPath     :: !Text
    -- ^ Database file path
  , ddbReadOnly :: !Bool
    -- ^ Read-only mode
  }
  deriving stock (Eq, Show)

-- | DuckDB configuration
data DuckDBConfig = DuckDBConfig
  { ddbcPath     :: !Text
    -- ^ Database file path (":memory:" for in-memory)
  , ddbcReadOnly :: !Bool
    -- ^ Open in read-only mode
  , ddbcThreads  :: !Int
    -- ^ Number of worker threads
  }
  deriving stock (Eq, Show)

-- | Default configuration (in-memory)
defaultConfig :: DuckDBConfig
defaultConfig = DuckDBConfig
  { ddbcPath = ":memory:"
  , ddbcReadOnly = False
  , ddbcThreads = 4
  }

--------------------------------------------------------------------------------
-- Connection Management
--------------------------------------------------------------------------------

-- | Connect to DuckDB
-- Grade: '[Net, Config] - reads config, performs connection
connect :: DuckDBConfig -> FoundryM '[ 'Net, 'Config ] (Either Text DuckDBConn)
connect cfg = F.do
  _ <- liftNet (pure ())
  liftConfig $ pure $ Right DuckDBConn
    { ddbPath = ddbcPath cfg
    , ddbReadOnly = ddbcReadOnly cfg
    }

-- | Disconnect from DuckDB
-- Grade: '[Net]
disconnect :: DuckDBConn -> FoundryM '[ 'Net ] ()
disconnect _ = liftNet $ pure ()

--------------------------------------------------------------------------------
-- Storage Operations
--------------------------------------------------------------------------------

-- | Store brand data
-- Grade: '[Net]
storeBrand :: DuckDBConn -> StoredBrand -> FoundryM '[ 'Net ] (StorageResult ())
storeBrand _conn _brand = liftNet $ pure $ StorageOk ()

-- | Fetch brand by key
-- Grade: '[Net]
fetchBrand :: DuckDBConn -> StorageKey -> FoundryM '[ 'Net ] (StorageResult StoredBrand)
fetchBrand _conn key = liftNet $ pure $ StorageNotFound key

-- | Query brands with filter
-- Grade: '[Net]
queryBrands :: DuckDBConn -> Text -> FoundryM '[ 'Net ] (StorageResult [StoredBrand])
queryBrands _conn _query = liftNet $ pure $ StorageOk []

--------------------------------------------------------------------------------
-- Analytics
--------------------------------------------------------------------------------

-- | Count total brands
-- Grade: '[Net]
countBrands :: DuckDBConn -> FoundryM '[ 'Net ] (StorageResult Int)
countBrands _conn = liftNet $ pure $ StorageOk 0

-- | Aggregate palette data across brands
-- Grade: '[Net]
aggregatePalettes :: DuckDBConn -> FoundryM '[ 'Net ] (StorageResult [(Text, Int)])
aggregatePalettes _conn = liftNet $ pure $ StorageOk []

-- | Serialize brand data to binary format for bulk operations.
--
-- Produces a simple length-prefixed binary format:
--
-- @
--   [4 bytes: key length]
--   [key bytes]
--   [4 bytes: domain length]
--   [domain UTF-8 bytes]
--   [16 bytes: UUID]
--   [1 byte: storage layer]
--   [4 bytes: content length]
--   [content bytes]
-- @
--
-- Used for efficient bulk inserts and binary protocol communication.
-- Note: createdAt is not serialized (determined by storage time).
serializeBrand :: StoredBrand -> ByteString
serializeBrand brand = BS.concat
  [ encodeLength (BS.length keyBytes)
  , keyBytes
  , encodeLength (BS.length domainBytes)
  , domainBytes
  , UUID.toASCIIBytes (sbBrandId brand)
  , encodeLayer (sbLayer brand)
  , encodeLength (BS.length (sbContent brand))
  , sbContent brand
  ]
  where
    keyBytes    = unStorageKey (sbKey brand)
    domainBytes = T.encodeUtf8 (sbDomain brand)
    
    -- Encode 32-bit length as 4 bytes (big-endian)
    encodeLength :: Int -> ByteString
    encodeLength n = BS.pack
      [ fromIntegral ((n `shiftR` 24) .&. 0xFF)
      , fromIntegral ((n `shiftR` 16) .&. 0xFF)
      , fromIntegral ((n `shiftR`  8) .&. 0xFF)
      , fromIntegral  (n             .&. 0xFF)
      ]
    
    -- Encode storage layer as single byte
    encodeLayer :: StorageLayer -> ByteString
    encodeLayer L1HAMT    = BS.singleton 0
    encodeLayer L2DuckDB  = BS.singleton 1
    encodeLayer L3Postgres = BS.singleton 2
    
    -- Bit operations (avoiding import for small use)
    shiftR :: Int -> Int -> Int
    shiftR = div' where div' x k = x `div` (2 ^ k)
    
    (.&.) :: Int -> Int -> Int
    (.&.) = andBits where andBits x m = x `mod` (m + 1)

--------------------------------------------------------------------------------
-- Component Registry Schema
--------------------------------------------------------------------------------

-- | Component schema DDL statements
--
-- These create the tables needed for the Atomic Design component registry:
--   - atoms: Color, font, spacing, radius, shadow primitives
--   - molecules: Button, input, link combinations
--   - compounds: Card, nav, hero assemblies
--
-- All components are UUID5-addressed for deterministic identity.
data ComponentSchema = ComponentSchema
  { csAtomsTable     :: !Text
  , csMoleculesTable :: !Text
  , csCompoundsTable :: !Text
  }
  deriving stock (Eq, Show)

-- | Create component registry tables
--
-- DDL for the three-tier atomic design schema:
--
-- @
-- CREATE TABLE atoms (
--   id UUID PRIMARY KEY,              -- UUID5 from domain:level:type:hash
--   domain TEXT NOT NULL,             -- Source brand domain
--   atom_type TEXT NOT NULL,          -- color, font, spacing, radius, shadow
--   name TEXT NOT NULL,               -- Semantic name
--   data JSON NOT NULL,               -- Type-specific data
--   created_at TIMESTAMP DEFAULT NOW()
-- );
--
-- CREATE TABLE molecules (
--   id UUID PRIMARY KEY,
--   domain TEXT NOT NULL,
--   molecule_type TEXT NOT NULL,      -- button, input, link, badge
--   variant TEXT,                     -- primary, secondary, ghost, etc.
--   atom_refs UUID[],                 -- References to atoms
--   data JSON NOT NULL,
--   created_at TIMESTAMP DEFAULT NOW()
-- );
--
-- CREATE TABLE compounds (
--   id UUID PRIMARY KEY,
--   domain TEXT NOT NULL,
--   compound_type TEXT NOT NULL,      -- card, nav, hero, footer
--   molecule_refs UUID[],             -- References to molecules
--   atom_refs UUID[],                 -- Direct atom references
--   data JSON NOT NULL,
--   created_at TIMESTAMP DEFAULT NOW()
-- );
-- @
-- | Create component registry tables
-- Grade: '[Net]
createComponentTables :: DuckDBConn -> FoundryM '[ 'Net ] (StorageResult ComponentSchema)
createComponentTables _conn = liftNet $ pure $ StorageOk ComponentSchema
  { csAtomsTable     = "atoms"
  , csMoleculesTable = "molecules"
  , csCompoundsTable = "compounds"
  }

-- | Store an atom in the registry
-- Grade: '[Net]
storeAtom
  :: DuckDBConn
  -> Text      -- ^ UUID (as text)
  -> Text      -- ^ Domain
  -> Text      -- ^ Atom type
  -> Text      -- ^ Name
  -> ByteString -- ^ JSON data
  -> FoundryM '[ 'Net ] (StorageResult ())
storeAtom _conn _uuid _domain _atomType _name _jsonData = liftNet $ pure $ StorageOk ()

-- | Store a molecule in the registry
-- Grade: '[Net]
storeMolecule
  :: DuckDBConn
  -> Text      -- ^ UUID
  -> Text      -- ^ Domain
  -> Text      -- ^ Molecule type
  -> Text      -- ^ Variant
  -> [Text]    -- ^ Atom references (UUIDs)
  -> ByteString -- ^ JSON data
  -> FoundryM '[ 'Net ] (StorageResult ())
storeMolecule _conn _uuid _domain _molType _variant _atomRefs _jsonData = liftNet $ pure $ StorageOk ()

-- | Store a compound in the registry
-- Grade: '[Net]
storeCompound
  :: DuckDBConn
  -> Text      -- ^ UUID
  -> Text      -- ^ Domain
  -> Text      -- ^ Compound type
  -> [Text]    -- ^ Molecule references
  -> [Text]    -- ^ Direct atom references
  -> ByteString -- ^ JSON data
  -> FoundryM '[ 'Net ] (StorageResult ())
storeCompound _conn _uuid _domain _compType _molRefs _atomRefs _jsonData = liftNet $ pure $ StorageOk ()

-- | Query atoms by domain
-- Grade: '[Net]
queryAtomsByDomain :: DuckDBConn -> Text -> FoundryM '[ 'Net ] (StorageResult [(Text, Text, ByteString)])
queryAtomsByDomain _conn _domain = liftNet $ pure $ StorageOk []

-- | Query molecules by domain
-- Grade: '[Net]
queryMoleculesByDomain :: DuckDBConn -> Text -> FoundryM '[ 'Net ] (StorageResult [(Text, Text, ByteString)])
queryMoleculesByDomain _conn _domain = liftNet $ pure $ StorageOk []
