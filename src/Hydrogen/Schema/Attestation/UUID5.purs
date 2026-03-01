-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // attestation // uuid5
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Deterministic UUID generation using SHA-256.
-- |
-- | This module implements UUID5-style identifiers but uses SHA-256 instead
-- | of SHA-1 (which RFC 4122 specifies). We use version nibble 0x5 and
-- | variant bits 0b10 to maintain format compatibility while using a
-- | stronger hash.
-- |
-- | ## Why Deterministic UUIDs?
-- |
-- | At billion-agent scale, agents need reproducible identity:
-- | - Same namespace + name → same UUID (always)
-- | - Two agents creating the same Element get the same UUID
-- | - Enables deterministic caching, diffing, and distribution
-- | - Full algebraic reasoning about identity
-- |
-- | ## Format
-- |
-- | Standard UUID format: xxxxxxxx-xxxx-5xxx-yxxx-xxxxxxxxxxxx
-- | Where:
-- | - 5 indicates version 5 (name-based, SHA-256 in our case)
-- | - y is 8, 9, a, or b (variant bits)
-- |
-- | ## Namespaces
-- |
-- | Hydrogen defines standard namespaces for different content types:
-- | - Element namespace for UI components
-- | - Event namespace for scheduling
-- | - Attestation namespace for proofs

module Hydrogen.Schema.Attestation.UUID5
  ( -- * Re-exported from Namespaces
    module Hydrogen.Schema.Attestation.UUID5.Namespaces
  -- * UUID5 Generation
  , uuid5
  , uuid5Bytes
  , uuid5FromHash
  -- * Parsing
  , fromString
  -- * Output
  , toHex
  , toBytes
  , toString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , ($)
  , (<>)
  , (-)
  , (+)
  , (*)
  , (<)
  , (>=)
  , (==)
  , (&&)
  )

import Data.Array (length, index, foldl, range, snoc, concat, slice) as Array
import Data.Int.Bits (shr, or, and)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.String.CodeUnits (toCharArray) as String
import Data.Char (toCharCode)

import Hydrogen.Schema.Attestation.SHA256 (sha256Bytes, toBytes) as SHA256

-- Re-export namespaces
import Hydrogen.Schema.Attestation.UUID5.Namespaces
  ( UUID5(..)
  , nsElement
  , nsEvent
  , nsAttestation
  , nsContact
  , nsButton
  , nsToggle
  , nsTab
  , nsTabPanel
  , nsAccordionTrigger
  , nsAccordionContent
  , nsOTPInput
  , nsOTPDigit
  , nsMesh
  , nsScene
  , nsPosition
  , nsMaterial
  , nsLight
  , nsCamera
  , nsLayer
  , nsComposition
  , nsProperty
  , nsEffect
  , nsMask
  , nsKeyframe
  , nsRenderEffect
  , nsComputeKernel
  , nsFrameState
  , nsAnimationState
  , nsSpringState
  , nsEffectPass
  , nsBlurKernel
  , nsGlowKernel
  , nsParticleKernel
  )





-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate UUID5 from namespace and name (string)
-- |
-- | This is the primary API for UUID generation.
-- | Same namespace + name always produces the same UUID.
uuid5 :: UUID5 -> String -> UUID5
uuid5 namespace name =
  let
    chars = String.toCharArray name
    nameBytes = Array.foldl (\acc c -> Array.snoc acc (toCharCode c)) [] chars
  in
    uuid5Bytes namespace nameBytes

-- | Generate UUID5 from namespace and name (bytes)
-- |
-- | For use when the name is already in byte form.
uuid5Bytes :: UUID5 -> Array Int -> UUID5
uuid5Bytes (UUID5 nsBytes) nameBytes =
  let
    -- Concatenate namespace + name
    input = Array.concat [nsBytes, nameBytes]
    -- Hash with SHA-256
    hashBytes = SHA256.toBytes $ SHA256.sha256Bytes input
  in
    uuid5FromHash hashBytes

-- | Create UUID5 from hash bytes
-- |
-- | Takes first 16 bytes of hash and applies version/variant bits.
-- | Version 5 (nibble 5 at position 6)
-- | Variant 10xx (bits at position 8)
uuid5FromHash :: Array Int -> UUID5
uuid5FromHash hashBytes =
  let
    -- Take first 16 bytes
    bytes16 = Array.slice 0 16 hashBytes
    
    -- Set version bits (byte 6): clear top 4 bits, set to 0101 (version 5)
    byte6 = fromMaybe 0 $ Array.index bytes16 6
    byte6' = or (and byte6 0x0F) 0x50
    
    -- Set variant bits (byte 8): clear top 2 bits, set to 10xx
    byte8 = fromMaybe 0 $ Array.index bytes16 8
    byte8' = or (and byte8 0x3F) 0x80
    
    -- Apply modifications
    result = applyAt 6 byte6' $ applyAt 8 byte8' bytes16
  in
    UUID5 result

-- | Apply a value at a specific index
applyAt :: Int -> Int -> Array Int -> Array Int
applyAt idx val arr =
  Array.foldl (\acc i ->
    let v = if i == idx then val else fromMaybe 0 $ Array.index arr i
    in Array.snoc acc v)
    []
    (Array.range 0 15)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // parsing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parse UUID5 from standard string format.
-- |
-- | Accepts format: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx (36 characters)
-- | Also accepts format: xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx (32 characters)
-- |
-- | Returns nsElement (the nil-equivalent namespace) if parsing fails.
-- | This is safe for deserialization since an invalid UUID will simply
-- | not match any legitimate content-addressed ID.
fromString :: String -> UUID5
fromString str =
  let
    -- Remove dashes to get pure hex
    chars = String.toCharArray str
    hexChars = Array.foldl (\acc c -> 
      if toCharCode c == 45 then acc  -- skip dash (ASCII 45)
      else Array.snoc acc c) [] chars
    
    -- Parse pairs of hex chars into bytes
    bytes = parseHexPairs hexChars 0 []
  in
    if Array.length bytes == 16
    then UUID5 bytes
    else nsElement  -- fallback to namespace if invalid

-- | Parse pairs of hex characters into bytes
parseHexPairs :: Array Char -> Int -> Array Int -> Array Int
parseHexPairs chars idx acc =
  if idx >= Array.length chars
  then acc
  else
    let
      c1 = fromMaybe '0' $ Array.index chars idx
      c2 = fromMaybe '0' $ Array.index chars (idx + 1)
      byte = hexCharToInt c1 * 16 + hexCharToInt c2
    in
      parseHexPairs chars (idx + 2) (Array.snoc acc byte)

-- | Convert hex character to integer value
hexCharToInt :: Char -> Int
hexCharToInt c =
  let code = toCharCode c
  in
    if code >= 48 && code < 58 then code - 48       -- '0'-'9'
    else if code >= 65 && code < 71 then code - 55  -- 'A'-'F'
    else if code >= 97 && code < 103 then code - 87 -- 'a'-'f'
    else 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert UUID5 to standard string format
-- |
-- | Returns: xxxxxxxx-xxxx-xxxx-xxxx-xxxxxxxxxxxx (36 characters)
toString :: UUID5 -> String
toString (UUID5 bytes) =
  let
    hex = Array.foldl (\acc b -> acc <> byteToHex b) "" bytes
    -- Insert dashes at positions 8, 12, 16, 20
    part1 = sliceStr 0 8 hex
    part2 = sliceStr 8 12 hex
    part3 = sliceStr 12 16 hex
    part4 = sliceStr 16 20 hex
    part5 = sliceStr 20 32 hex
  in
    part1 <> "-" <> part2 <> "-" <> part3 <> "-" <> part4 <> "-" <> part5

-- | Convert UUID5 to hexadecimal string (32 characters, no dashes)
toHex :: UUID5 -> String
toHex (UUID5 bytes) = 
  Array.foldl (\acc b -> acc <> byteToHex b) "" bytes

-- | Convert UUID5 to byte array (16 bytes)
toBytes :: UUID5 -> Array Int
toBytes (UUID5 bytes) = bytes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slice a string by character indices
sliceStr :: Int -> Int -> String -> String
sliceStr start end str =
  let
    chars = String.toCharArray str
    len = Array.length chars
    sliced = Array.foldl (\acc i ->
      if i >= start then
        if i < end then
          case Array.index chars i of
            Nothing -> acc
            Just c -> acc <> charToString c
        else acc
      else acc)
      ""
      (Array.range 0 (len - 1))
  in
    sliced

-- | Convert char to string
charToString :: Char -> String
charToString c = 
  let code = toCharCode c
  in hexDigit (shr code 4) <> hexDigit (and code 0x0F)

-- | Convert a byte to 2-character hex string
byteToHex :: Int -> String
byteToHex b = hexDigit (shr b 4) <> hexDigit (and b 0x0F)

-- | Convert 0-15 to hex digit
hexDigit :: Int -> String
hexDigit n
  | n < 1 = "0"
  | n < 2 = "1"
  | n < 3 = "2"
  | n < 4 = "3"
  | n < 5 = "4"
  | n < 6 = "5"
  | n < 7 = "6"
  | n < 8 = "7"
  | n < 9 = "8"
  | n < 10 = "9"
  | n < 11 = "a"
  | n < 12 = "b"
  | n < 13 = "c"
  | n < 14 = "d"
  | n < 15 = "e"
  | otherwise = "f"
