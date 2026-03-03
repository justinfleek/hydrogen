-- | Variable-length integer encoding for SIGIL wire format
-- |
-- | Port of Slide.Wire.Varint to PureScript.
-- |
-- | Uses LEB128-style encoding:
-- |   - Each byte encodes 7 bits of data
-- |   - High bit indicates continuation (1 = more bytes follow)
-- |   - Little-endian (LSB first)

module Hydrogen.Scraper.Wire.Varint
  ( -- * Encoding
    encodeVarint
  , varintSize
  
  -- * Decoding
  , decodeVarint
  , DecodeResult
  ) where

import Prelude

import Data.Array ((:))
import Data.Array as Array
import Data.Int.Bits ((.&.), (.|.), shl, shr, zshr)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- | Result of decoding: (value, bytes consumed)
type DecodeResult = Tuple Int Int

-- | Encode an integer as varint bytes
-- |
-- | Returns array of bytes (each 0-255)
encodeVarint :: Int -> Array Int
encodeVarint n = go n []
  where
    go :: Int -> Array Int -> Array Int
    go value acc
      | value < 128 = Array.reverse (value : acc)
      | otherwise = 
          let byte = (value .&. 0x7F) .|. 0x80
              rest = value `zshr` 7
          in go rest (byte : acc)

-- | Calculate how many bytes a varint will need
varintSize :: Int -> Int
varintSize n
  | n < 0x80 = 1
  | n < 0x4000 = 2
  | n < 0x200000 = 3
  | n < 0x10000000 = 4
  | otherwise = 5

-- | Decode a varint from bytes
-- |
-- | Returns Nothing if incomplete, Just (value, bytesConsumed) otherwise
decodeVarint :: Array Int -> Maybe DecodeResult
decodeVarint bytes = go 0 0 0
  where
    go :: Int -> Int -> Int -> Maybe DecodeResult
    go index value shift
      | index >= Array.length bytes = Nothing  -- incomplete
      | otherwise = case Array.index bytes index of
          Nothing -> Nothing
          Just byte ->
            let newValue = value .|. ((byte .&. 0x7F) `shl` shift)
            in if (byte .&. 0x80) == 0
               then Just (Tuple newValue (index + 1))
               else go (index + 1) newValue (shift + 7)


