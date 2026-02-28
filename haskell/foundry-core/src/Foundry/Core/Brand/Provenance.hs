{- |
Module      : Foundry.Core.Brand.Provenance
Description : Content provenance tracking
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

SHA256 content hashing and source tracking for audit trails.
-}
module Foundry.Core.Brand.Provenance
  ( -- * Types
    ContentHash (..)
  , SourceURL (..)
  , Timestamp (..)
  , Provenance (..)
  ) where

import Data.Aeson (ToJSON (..), FromJSON (..), (.=), (.:), object, withObject, withText)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (UTCTime)
import Data.Word (Word8)
import Numeric (showHex, readHex)

-- | SHA256 content hash (deterministic)
newtype ContentHash = ContentHash {unContentHash :: ByteString}
  deriving stock (Eq, Ord, Show)

-- | Source URL for ingested content
newtype SourceURL = SourceURL {unSourceURL :: Text}
  deriving stock (Eq, Show)

-- | Timestamp for provenance tracking
newtype Timestamp = Timestamp {unTimestamp :: UTCTime}
  deriving stock (Eq, Ord, Show)

-- | Complete provenance record
data Provenance = Provenance
  { provenanceHash :: !ContentHash
  , provenanceSource :: !SourceURL
  , provenanceTimestamp :: !Timestamp
  }
  deriving stock (Eq, Show)

--------------------------------------------------------------------------------
-- JSON Instances
--------------------------------------------------------------------------------

-- | Encode ByteString as hex text for JSON
bytesToHex :: ByteString -> Text
bytesToHex bs = T.pack $ concatMap (\w -> pad2 $ showHex w "") (BS.unpack bs)
  where
    pad2 :: String -> String
    pad2 [c] = ['0', c]
    pad2 s   = s

-- | Decode hex text back to ByteString
hexToBytes :: Text -> Either String ByteString
hexToBytes hex 
  | T.length hex `mod` 2 /= 0 = Left "Hex string must have even length"
  | otherwise = 
      let pairs = T.chunksOf 2 hex
          parseHexByte :: Text -> Either String Word8
          parseHexByte t = case readHex (T.unpack t) of
            [(n, "")] -> Right (fromIntegral (n :: Int))
            _         -> Left $ "Invalid hex: " <> T.unpack t
      in BS.pack <$> traverse parseHexByte pairs

-- | ContentHash encodes as hex string
instance ToJSON ContentHash where
  toJSON (ContentHash bs) = toJSON (bytesToHex bs)

instance FromJSON ContentHash where
  parseJSON = withText "ContentHash" $ \t ->
    case hexToBytes t of
      Left err -> fail err
      Right bs -> pure (ContentHash bs)

-- | SourceURL encodes as plain text
instance ToJSON SourceURL where
  toJSON (SourceURL url) = toJSON url

instance FromJSON SourceURL where
  parseJSON = withText "SourceURL" $ \t -> pure (SourceURL t)

-- | Timestamp encodes as ISO 8601
instance ToJSON Timestamp where
  toJSON (Timestamp t) = toJSON t

instance FromJSON Timestamp where
  parseJSON v = Timestamp <$> parseJSON v

-- | Provenance as an object
instance ToJSON Provenance where
  toJSON p = object
    [ "hash"      .= provenanceHash p
    , "source"    .= provenanceSource p
    , "timestamp" .= provenanceTimestamp p
    ]

instance FromJSON Provenance where
  parseJSON = withObject "Provenance" $ \v -> Provenance
    <$> v .: "hash"
    <*> v .: "source"
    <*> v .: "timestamp"
