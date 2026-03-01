-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // element // binary // primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Primitives
-- |
-- | Low-level byte operations for Element serialization:
-- | - Byte array manipulation (concat, slice, length)
-- | - Integer read/write (u8, u32 little-endian)
-- | - Float read/write (f32 as fixed-point)
-- | - String encoding (length-prefixed UTF-8)
-- | - Header serialization

module Hydrogen.Element.Binary.Primitives
  ( -- * Byte Operations
    toByteArray
  , fromByteArray
  , bytesLength
  , concatBytes
  , emptyBytes
  
  -- * Integer I/O
  , writeU32
  , readU32
  , writeU8
  , readU8
  
  -- * Float I/O
  , writeF32
  , readF32
  
  -- * String I/O
  , serializeString
  , deserializeString
  , serializeMaybeString
  , deserializeMaybeString
  
  -- * Header I/O
  , serializeHeader
  , deserializeHeader
  
  -- * FFI
  , toCodePointArray
  , bytesToString
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( bind
  , pure
  , ($)
  , (+)
  , (*)
  , (/)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (floor, toNumber)
import Data.Int.Bits (shl, shr, (.&.), (.|.))

import Hydrogen.Element.Binary.Types
  ( Bytes(Bytes)
  , Header
  , DeserializeResult
  , magic
  , version
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // byte utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Bytes to raw array
toByteArray :: Bytes -> Array Int
toByteArray (Bytes arr) = arr

-- | Create Bytes from raw array
fromByteArray :: Array Int -> Bytes
fromByteArray = Bytes

-- | Get byte count
bytesLength :: Bytes -> Int
bytesLength (Bytes arr) = Array.length arr

-- | Concatenate byte arrays
concatBytes :: Bytes -> Bytes -> Bytes
concatBytes (Bytes a) (Bytes b) = Bytes (a <> b)

-- | Empty bytes
emptyBytes :: Bytes
emptyBytes = Bytes []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // integer read/write
-- ═════════════════════════════════════════════════════════════════════════════

-- | Write u32 little-endian (4 bytes)
writeU32 :: Int -> Bytes
writeU32 n =
  let b0 = n .&. 0xFF
      b1 = (shr n 8) .&. 0xFF
      b2 = (shr n 16) .&. 0xFF
      b3 = (shr n 24) .&. 0xFF
  in Bytes [b0, b1, b2, b3]

-- | Read u32 little-endian
readU32 :: Array Int -> Int -> Maybe Int
readU32 arr offset = do
  b0 <- Array.index arr offset
  b1 <- Array.index arr (offset + 1)
  b2 <- Array.index arr (offset + 2)
  b3 <- Array.index arr (offset + 3)
  pure (b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24))

-- | Write u8 (1 byte)
writeU8 :: Int -> Bytes
writeU8 n = Bytes [n .&. 0xFF]

-- | Read u8
readU8 :: Array Int -> Int -> Maybe Int
readU8 arr offset = Array.index arr offset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // float read/write
-- ═════════════════════════════════════════════════════════════════════════════

-- | Write f32 as 4 bytes (IEEE 754)
-- | Note: Uses integer approximation. Full impl would use FFI Float32Array.
writeF32 :: Number -> Bytes
writeF32 n =
  -- Encode as fixed-point: multiply by 256 to preserve some precision
  let scaled = floor (n * 256.0)
      b0 = scaled .&. 0xFF
      b1 = (shr scaled 8) .&. 0xFF
      b2 = (shr scaled 16) .&. 0xFF
      b3 = (shr scaled 24) .&. 0xFF
  in Bytes [b0, b1, b2, b3]

-- | Read f32 from 4 bytes
readF32 :: Array Int -> Int -> Maybe Number
readF32 arr offset = do
  v <- readU32 arr offset
  pure (toNumber v / 256.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // string read/write
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a string (length-prefixed)
-- |
-- | Layout: length (u32) + utf8 bytes
serializeString :: String -> Bytes
serializeString str =
  let bytes = toCodePointArray str
  in concatBytes (writeU32 (Array.length bytes)) (Bytes bytes)

-- | Deserialize String (length-prefixed)
deserializeString :: Array Int -> Int -> Maybe (DeserializeResult String)
deserializeString arr offset = do
  len <- readU32 arr offset
  let bytes = Array.slice (offset + 4) (offset + 4 + len) arr
  let str = bytesToString bytes
  Just { value: str, bytesRead: 4 + len }

-- | Serialize Maybe String
serializeMaybeString :: Maybe String -> Bytes
serializeMaybeString = case _ of
  Nothing -> writeU8 0
  Just s -> concatBytes (writeU8 1) (serializeString s)

-- | Deserialize Maybe String
deserializeMaybeString :: Array Int -> Int -> Maybe (DeserializeResult (Maybe String))
deserializeMaybeString arr offset = do
  hasValue <- readU8 arr offset
  if hasValue == 0
    then Just { value: Nothing, bytesRead: 1 }
    else do
      strResult <- deserializeString arr (offset + 1)
      Just { value: Just strResult.value, bytesRead: 1 + strResult.bytesRead }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // header serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize header
serializeHeader :: Header -> Bytes
serializeHeader h =
  concatBytes (writeU32 h.magic) $
  concatBytes (writeU32 h.version) $
  concatBytes (writeU32 h.size) $
  writeU32 h.checksum

-- | Deserialize header
deserializeHeader :: Array Int -> Maybe Header
deserializeHeader arr = do
  m <- readU32 arr 0
  v <- readU32 arr 4
  s <- readU32 arr 8
  c <- readU32 arr 12
  if m == magic && v == version
    then Just { magic: m, version: v, size: s, checksum: c }
    else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // ffi
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert string to array of code points (ASCII)
foreign import toCodePointArray :: String -> Array Int

-- | Convert byte array to String (ASCII)
foreign import bytesToString :: Array Int -> String
