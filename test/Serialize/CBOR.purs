-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // test // serialize // cbor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property tests for Hydrogen.Serialize.CBOR
-- |
-- | Tests the CBOR serialization module:
-- | - Primitive encoding (Int, Number, String, Boolean)
-- | - Compound encoding (Array, Map)
-- | - Wire format correctness (RFC 8949)
-- |
-- | ## Test Philosophy
-- |
-- | CBOR is a wire format contract. Same value = same bytes, always.
-- | These tests verify deterministic encoding for all primitive types.

module Test.Serialize.CBOR
  ( cborTests
  ) where

import Prelude
  ( Unit
  , discard
  , negate
  )

import Data.Array (index) as Array
import Data.Maybe (Maybe(Just))
import Hydrogen.Serialize.CBOR as CBOR
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // test suite
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main test export - CBOR serialization tests
cborTests :: Spec Unit
cborTests = describe "Serialize.CBOR" do
  intEncodingTests
  boolEncodingTests
  stringEncodingTests
  arrayEncodingTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // int encoding tests
-- ═══════════════════════════════════════════════════════════════════════════════

intEncodingTests :: Spec Unit
intEncodingTests = describe "Int encoding" do
  
  it "encodes 0 as single byte 0x00" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt 0)
    Array.index bytes 0 `shouldEqual` Just 0
  
  it "encodes 1 as single byte 0x01" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt 1)
    Array.index bytes 0 `shouldEqual` Just 1
  
  it "encodes 23 as single byte 0x17" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt 23)
    Array.index bytes 0 `shouldEqual` Just 23
  
  it "encodes 24 as two bytes (0x18 0x18)" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt 24)
    Array.index bytes 0 `shouldEqual` Just 24  -- 0x18 = major type 0 + additional 24
    Array.index bytes 1 `shouldEqual` Just 24
  
  it "encodes 255 as two bytes (0x18 0xff)" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt 255)
    Array.index bytes 0 `shouldEqual` Just 24  -- 0x18
    Array.index bytes 1 `shouldEqual` Just 255
  
  it "encodes -1 as negative integer (0x20)" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt (negate 1))
    -- Negative integers use major type 1, value = -(1+n), so -1 -> n=0 -> 0x20
    Array.index bytes 0 `shouldEqual` Just 32  -- 0x20 = major type 1 + additional 0
  
  it "encodes -10 as negative integer (0x29)" do
    let bytes = CBOR.serializeToArray (CBOR.encodeInt (negate 10))
    -- -10 -> n=9 -> 0x29
    Array.index bytes 0 `shouldEqual` Just 41  -- 0x29 = major type 1 + additional 9

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // bool encoding tests
-- ═══════════════════════════════════════════════════════════════════════════════

boolEncodingTests :: Spec Unit
boolEncodingTests = describe "Bool encoding" do
  
  it "encodes true as 0xf5" do
    let bytes = CBOR.serializeToArray (CBOR.encodeBool true)
    Array.index bytes 0 `shouldEqual` Just 245  -- 0xf5
  
  it "encodes false as 0xf4" do
    let bytes = CBOR.serializeToArray (CBOR.encodeBool false)
    Array.index bytes 0 `shouldEqual` Just 244  -- 0xf4
  
  it "encodes null as 0xf6" do
    let bytes = CBOR.serializeToArray CBOR.encodeNull
    Array.index bytes 0 `shouldEqual` Just 246  -- 0xf6

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // string encoding tests
-- ═══════════════════════════════════════════════════════════════════════════════

stringEncodingTests :: Spec Unit
stringEncodingTests = describe "String encoding" do
  
  it "encodes empty string as 0x60" do
    let bytes = CBOR.serializeToArray (CBOR.encodeString "")
    -- Major type 3 (text) + length 0 = 0x60
    Array.index bytes 0 `shouldEqual` Just 96  -- 0x60
  
  it "encodes 'a' as 0x61 0x61" do
    let bytes = CBOR.serializeToArray (CBOR.encodeString "a")
    -- Major type 3 + length 1 = 0x61, followed by ASCII 'a' = 0x61
    Array.index bytes 0 `shouldEqual` Just 97  -- 0x61
    Array.index bytes 1 `shouldEqual` Just 97  -- ASCII 'a'

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // array encoding tests
-- ═══════════════════════════════════════════════════════════════════════════════

arrayEncodingTests :: Spec Unit
arrayEncodingTests = describe "Array encoding" do
  
  it "encodes empty array as 0x80" do
    let bytes = CBOR.serializeToArray (CBOR.encodeArray ([] :: Array Int))
    -- Major type 4 (array) + length 0 = 0x80
    Array.index bytes 0 `shouldEqual` Just 128  -- 0x80
  
  it "encodes [1] as 0x81 0x01" do
    let bytes = CBOR.serializeToArray (CBOR.encodeArray [1])
    -- Major type 4 + length 1 = 0x81, followed by int 1 = 0x01
    Array.index bytes 0 `shouldEqual` Just 129  -- 0x81
    Array.index bytes 1 `shouldEqual` Just 1
  
  it "encodes [1, 2, 3] correctly" do
    let bytes = CBOR.serializeToArray (CBOR.encodeArray [1, 2, 3])
    -- Major type 4 + length 3 = 0x83
    Array.index bytes 0 `shouldEqual` Just 131  -- 0x83
    Array.index bytes 1 `shouldEqual` Just 1
    Array.index bytes 2 `shouldEqual` Just 2
    Array.index bytes 3 `shouldEqual` Just 3
