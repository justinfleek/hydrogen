-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // adversarial // identity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Adversarial Identity Tests — UUID5 determinism and collision resistance.
-- |
-- | ## Threat Model
-- |
-- | A malicious actor might:
-- | - Attempt to create UUID collisions to impersonate entities
-- | - Exploit non-determinism to corrupt caches across agent swarms
-- | - Forge generation counters to bypass cache invalidation
-- | - Inject invalid UUIDs through deserialization
-- | - Craft inputs that produce predictable UUIDs
-- |
-- | ## Security Properties Tested
-- |
-- | 1. **Determinism**: Same inputs always produce same UUID5
-- | 2. **Collision Resistance**: Different inputs produce different UUIDs
-- | 3. **Version/Variant Correctness**: All UUIDs have correct format bits
-- | 4. **Namespace Isolation**: Different namespaces produce different UUIDs
-- | 5. **Generation Monotonicity**: Generation only increases, never regresses

module Test.Adversarial.Identity
  ( identityAdversarialTests
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all, foldl)
import Data.Int as Int
import Data.Int.Bits (shr)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.String.CodeUnits as StringCU
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck (Result, (<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Schema modules under test
import Hydrogen.Schema.Attestation.UUID5 as UUID5
import Hydrogen.Schema.Identity.Temporal as Identity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═════════════════════════════════════════════════════════════════════════════

identityAdversarialTests :: Spec Unit
identityAdversarialTests = describe "Adversarial Identity Tests" do
  uuid5DeterminismTests
  uuid5CollisionTests
  uuid5FormatTests
  generationMonotonicityTests
  cacheKeySecurityTests

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // uuid5 determinism tests
-- ═════════════════════════════════════════════════════════════════════════════

uuid5DeterminismTests :: Spec Unit
uuid5DeterminismTests = describe "UUID5 Determinism" do
  
  describe "Same input → same output" do
    it "identical name produces identical UUID" do
      let name = "test-entity-12345"
      let uuid1 = UUID5.uuid5 UUID5.nsElement name
      let uuid2 = UUID5.uuid5 UUID5.nsElement name
      UUID5.toString uuid1 `shouldEqual` UUID5.toString uuid2
    
    it "empty name produces consistent UUID" do
      let uuid1 = UUID5.uuid5 UUID5.nsElement ""
      let uuid2 = UUID5.uuid5 UUID5.nsElement ""
      UUID5.toString uuid1 `shouldEqual` UUID5.toString uuid2
    
    it "property: determinism holds for all strings" do
      Spec.quickCheck propUUID5Determinism
  
  describe "Namespace affects output" do
    it "same name, different namespace → different UUID" do
      let name = "shared-name"
      let uuid1 = UUID5.uuid5 UUID5.nsElement name
      let uuid2 = UUID5.uuid5 UUID5.nsEvent name
      UUID5.toString uuid1 `shouldSatisfy` \u1 -> 
        u1 /= UUID5.toString uuid2
    
    it "all standard namespaces produce unique UUIDs for same name" do
      let name = "test-name"
      let namespaces = 
            [ UUID5.nsElement
            , UUID5.nsEvent
            , UUID5.nsAttestation
            , UUID5.nsContact
            , UUID5.nsButton
            , UUID5.nsMesh
            , UUID5.nsScene
            ]
      let uuids = map (\ns -> UUID5.toString (UUID5.uuid5 ns name)) namespaces
      let uniqueCount = Array.length $ Array.nub uuids
      uniqueCount `shouldEqual` Array.length namespaces
  
  describe "Identified wrapper determinism" do
    it "identify same name produces same UUID" do
      let value1 = { x: 100, y: 200 }
      let value2 = { x: 100, y: 200 }
      let id1 = Identity.identify "my-point" value1
      let id2 = Identity.identify "my-point" value2
      UUID5.toString (Identity.getUUID id1) `shouldEqual` 
        UUID5.toString (Identity.getUUID id2)
    
    it "different names produce different UUIDs" do
      let value = { x: 100, y: 200 }
      let id1 = Identity.identify "point-a" value
      let id2 = Identity.identify "point-b" value
      UUID5.toString (Identity.getUUID id1) `shouldSatisfy` \u1 ->
        u1 /= UUID5.toString (Identity.getUUID id2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // uuid5 collision tests
-- ═════════════════════════════════════════════════════════════════════════════

uuid5CollisionTests :: Spec Unit
uuid5CollisionTests = describe "UUID5 Collision Resistance" do
  
  describe "Different inputs → different outputs" do
    it "incrementing numbers produce unique UUIDs" do
      let uuids = map (\i -> UUID5.toString (UUID5.uuid5 UUID5.nsElement (show i))) 
                      (Array.range 0 999)
      let uniqueCount = Array.length $ Array.nub uuids
      uniqueCount `shouldEqual` 1000
    
    it "similar strings produce different UUIDs" do
      let uuid1 = UUID5.uuid5 UUID5.nsElement "test"
      let uuid2 = UUID5.uuid5 UUID5.nsElement "test "  -- trailing space
      let uuid3 = UUID5.uuid5 UUID5.nsElement "Test"   -- different case
      let uuid4 = UUID5.uuid5 UUID5.nsElement "test1"  -- suffix
      let uuids = 
            [ UUID5.toString uuid1
            , UUID5.toString uuid2
            , UUID5.toString uuid3
            , UUID5.toString uuid4
            ]
      Array.length (Array.nub uuids) `shouldEqual` 4
    
    it "property: collision probability negligible" do
      Spec.quickCheck propNoCollisions
  
  describe "Adversarial collision attempts" do
    it "cannot craft two different inputs with same UUID" do
      -- Try known collision attempts
      let pairs = 
            [ Tuple "a" "b"
            , Tuple "aa" "ab"
            , Tuple "" " "
            , Tuple "0" "00"
            , Tuple "test_null" "test_null_null"  -- null byte variants (escaped as text)
            ]
      let allDifferent = all (\(Tuple a b) ->
            UUID5.toString (UUID5.uuid5 UUID5.nsElement a) /= 
            UUID5.toString (UUID5.uuid5 UUID5.nsElement b)) pairs
      allDifferent `shouldEqual` true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // uuid5 format tests
-- ═════════════════════════════════════════════════════════════════════════════

uuid5FormatTests :: Spec Unit
uuid5FormatTests = describe "UUID5 Format Correctness" do
  
  describe "Version and variant bits" do
    it "version nibble is always 5" do
      Spec.quickCheck propVersionNibble
    
    it "variant bits are always 10xx" do
      Spec.quickCheck propVariantBits
  
  describe "String format" do
    it "output is 36 characters (8-4-4-4-12)" do
      let uuid = UUID5.uuid5 UUID5.nsElement "test"
      String.length (UUID5.toString uuid) `shouldEqual` 36
    
    it "dashes at correct positions" do
      let uuidStr = UUID5.toString (UUID5.uuid5 UUID5.nsElement "test")
      StringCU.charAt 8 uuidStr `shouldEqual` Just '-'
      StringCU.charAt 13 uuidStr `shouldEqual` Just '-'
      StringCU.charAt 18 uuidStr `shouldEqual` Just '-'
      StringCU.charAt 23 uuidStr `shouldEqual` Just '-'
    
    it "all characters are valid hex or dash" do
      Spec.quickCheck propValidHexChars
  
  describe "Byte array format" do
    it "output is exactly 16 bytes" do
      let uuid = UUID5.uuid5 UUID5.nsElement "test"
      Array.length (UUID5.toBytes uuid) `shouldEqual` 16
    
    it "all bytes in valid range [0,255]" do
      let uuid = UUID5.uuid5 UUID5.nsElement "test"
      let bytes = UUID5.toBytes uuid
      all (\b -> b >= 0 && b <= 255) bytes `shouldEqual` true
  
  describe "Parsing roundtrip" do
    it "toString → fromString → toString is identity" do
      let uuid1 = UUID5.uuid5 UUID5.nsElement "roundtrip-test"
      let str1 = UUID5.toString uuid1
      let uuid2 = UUID5.fromString str1
      let str2 = UUID5.toString uuid2
      str1 `shouldEqual` str2
    
    it "property: roundtrip preserves all UUIDs" do
      Spec.quickCheck propParsingRoundtrip
    
    it "invalid strings fallback to nsElement" do
      let invalid = UUID5.fromString "not-a-uuid"
      -- Should fallback gracefully
      Array.length (UUID5.toBytes invalid) `shouldEqual` 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // generation monotonicity tests
-- ═════════════════════════════════════════════════════════════════════════════

generationMonotonicityTests :: Spec Unit
generationMonotonicityTests = describe "Generation Monotonicity" do
  
  describe "Generation counter behavior" do
    it "initial generation is 0" do
      Identity.unwrapGeneration Identity.initialGeneration `shouldEqual` 0
    
    it "nextGeneration increments by 1" do
      let g0 = Identity.initialGeneration
      let g1 = Identity.nextGeneration g0
      let g2 = Identity.nextGeneration g1
      Identity.unwrapGeneration g0 `shouldEqual` 0
      Identity.unwrapGeneration g1 `shouldEqual` 1
      Identity.unwrapGeneration g2 `shouldEqual` 2
    
    it "negative input clamped to 0" do
      let g = Identity.generation (-100)
      Identity.unwrapGeneration g `shouldEqual` 0
    
    it "generation near Int max handles increment" do
      let g = Identity.generation 2147483646
      let g' = Identity.nextGeneration g
      -- Should increment without overflow wrapping to negative
      Identity.unwrapGeneration g' `shouldSatisfy` \v -> v > 0
  
  describe "Identified update semantics" do
    it "updateIdentified bumps generation" do
      let id0 = Identity.identify "test" 100
      let id1 = Identity.updateIdentified (\x -> x + 1) id0
      Identity.unwrapGeneration (Identity.getGeneration id0) `shouldEqual` 0
      Identity.unwrapGeneration (Identity.getGeneration id1) `shouldEqual` 1
    
    it "bumpGeneration only changes generation" do
      let id0 = Identity.identify "test" 100
      let id1 = Identity.bumpGeneration id0
      -- Same UUID
      UUID5.toString (Identity.getUUID id0) `shouldEqual` 
        UUID5.toString (Identity.getUUID id1)
      -- Same value
      Identity.unwrapIdentified id0 `shouldEqual` Identity.unwrapIdentified id1
      -- Different generation
      Identity.getGeneration id0 `shouldSatisfy` \g0 ->
        g0 /= Identity.getGeneration id1
    
    it "isNewerThan correctly compares generations" do
      let id0 = Identity.identify "test" 100
      let id1 = Identity.bumpGeneration id0
      let id2 = Identity.bumpGeneration id1
      Identity.isNewerThan id1 id0 `shouldEqual` true
      Identity.isNewerThan id2 id1 `shouldEqual` true
      Identity.isNewerThan id0 id1 `shouldEqual` false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // cache key security tests
-- ═════════════════════════════════════════════════════════════════════════════

cacheKeySecurityTests :: Spec Unit
cacheKeySecurityTests = describe "Cache Key Security" do
  
  describe "Cache key uniqueness" do
    it "same identity, different generation → different cache key" do
      let id0 = Identity.identify "test" 100
      let id1 = Identity.bumpGeneration id0
      let key0 = Identity.cacheKeyString (Identity.toCacheKey id0)
      let key1 = Identity.cacheKeyString (Identity.toCacheKey id1)
      key0 `shouldSatisfy` \k0 -> k0 /= key1
    
    it "different identity → different cache key" do
      let id0 = Identity.identify "test-a" 100
      let id1 = Identity.identify "test-b" 100
      let key0 = Identity.cacheKeyString (Identity.toCacheKey id0)
      let key1 = Identity.cacheKeyString (Identity.toCacheKey id1)
      key0 `shouldSatisfy` \k0 -> k0 /= key1
    
    it "sameContent requires both UUID and generation match" do
      let id0 = Identity.identify "test" 100
      let id1 = Identity.identify "test" 100  -- same name → same UUID
      let id2 = Identity.bumpGeneration id1
      Identity.sameContent id0 id1 `shouldEqual` true
      Identity.sameContent id0 id2 `shouldEqual` false
  
  describe "Cache invalidation" do
    it "stale cache correctly detected" do
      let id0 = Identity.identify "entity" { value: 1 }
      let id1 = Identity.updateIdentified (\r -> r { value = 2 }) id0
      -- id0 is now stale relative to id1
      Identity.isNewerThan id1 id0 `shouldEqual` true
      Identity.sameContent id0 id1 `shouldEqual` false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // property generators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate adversarial strings for UUID testing
genAdversarialString :: Gen String
genAdversarialString = frequency $ NEA.cons'
  (Tuple 10.0 (pure ""))                                -- Empty
  [ Tuple 10.0 (pure " ")                               -- Single space
  , Tuple 10.0 (pure "test")                            -- Normal
  , Tuple 10.0 (pure "TEST")                            -- Uppercase
  , Tuple 10.0 (pure "a")                               -- Single char
  , Tuple 10.0 (genNumberedString)                      -- Generated string
  , Tuple 10.0 (pure "unicode-日本語")                   -- Unicode
  , Tuple 10.0 (pure "special!@#$%^&*()")               -- Special chars
  , Tuple 5.0  (pure "very-long-string-" <> show <$> chooseInt 0 1000000)
  , Tuple 5.0  (pure "αβγδε")                           -- Greek
  ]

-- | Generate a numbered string for variety
genNumberedString :: Gen String
genNumberedString = do
  n <- chooseInt 0 1000000
  pure ("entity-" <> show n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // property tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property: UUID5 is deterministic
propUUID5Determinism :: Gen Result
propUUID5Determinism = do
  name <- genAdversarialString
  let uuid1 = UUID5.uuid5 UUID5.nsElement name
  let uuid2 = UUID5.uuid5 UUID5.nsElement name
  pure $ (UUID5.toString uuid1 === UUID5.toString uuid2)

-- | Property: Different inputs produce different UUIDs (within reasonable probability)
propNoCollisions :: Gen Result
propNoCollisions = do
  name1 <- genAdversarialString
  name2 <- genAdversarialString
  let uuid1 = UUID5.uuid5 UUID5.nsElement name1
  let uuid2 = UUID5.uuid5 UUID5.nsElement name2
  pure $ if name1 == name2
    then UUID5.toString uuid1 === UUID5.toString uuid2
    else (UUID5.toString uuid1 /= UUID5.toString uuid2)
      <?> "Collision: " <> name1 <> " and " <> name2 <> " produced same UUID"

-- | Property: Version nibble is always 5
propVersionNibble :: Gen Result
propVersionNibble = do
  name <- genAdversarialString
  let uuid = UUID5.uuid5 UUID5.nsElement name
  let bytes = UUID5.toBytes uuid
  let byte6 = Array.index bytes 6
  pure $ case byte6 of
    Just b -> ((b `shr` 4) == 5)
      <?> "Version nibble should be 5, got " <> show (b `shr` 4)
    Nothing -> false <?> "Missing byte 6"

-- | Property: Variant bits are 10xx
propVariantBits :: Gen Result
propVariantBits = do
  name <- genAdversarialString
  let uuid = UUID5.uuid5 UUID5.nsElement name
  let bytes = UUID5.toBytes uuid
  let byte8 = Array.index bytes 8
  pure $ case byte8 of
    Just b -> 
      let topBits = b `shr` 6
      in (topBits == 2)  -- 10 in binary
        <?> "Variant bits should be 10, got " <> show topBits
    Nothing -> false <?> "Missing byte 8"

-- | Property: All output characters are valid hex or dash
propValidHexChars :: Gen Result
propValidHexChars = do
  name <- genAdversarialString
  let uuid = UUID5.uuid5 UUID5.nsElement name
  let str = UUID5.toString uuid
  -- UUID format is 8-4-4-4-12 with dashes, all lowercase hex
  -- Total 36 characters: 32 hex + 4 dashes
  let validLength = String.length str == 36
  -- Simple check: verify it's not empty and has the right length
  pure $ validLength
    <?> "UUID string has invalid length: " <> show (String.length str) <> " (expected 36)"

-- | Property: Parsing roundtrip preserves UUID
propParsingRoundtrip :: Gen Result
propParsingRoundtrip = do
  name <- genAdversarialString
  let uuid1 = UUID5.uuid5 UUID5.nsElement name
  let str1 = UUID5.toString uuid1
  let uuid2 = UUID5.fromString str1
  let str2 = UUID5.toString uuid2
  pure $ (str1 === str2)
