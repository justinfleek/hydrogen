-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // adversarial // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Adversarial State Tests — State corruption and invariant violation detection.
-- |
-- | ## Threat Model
-- |
-- | A malicious actor might:
-- | - Inject invalid state through deserialization
-- | - Create inconsistent compound types
-- | - Violate type invariants through edge case inputs
-- | - Corrupt shared state to cascade failures
-- | - Exploit partial updates to break atomicity
-- |
-- | ## Security Properties Tested
-- |
-- | 1. **Invariant Preservation**: All smart constructors enforce invariants
-- | 2. **Atomic Updates**: Compound updates cannot leave inconsistent state
-- | 3. **Cascade Prevention**: Invalid state cannot propagate
-- | 4. **Idempotence**: Operations that should be idempotent are

module Test.Adversarial.State
  ( stateAdversarialTests
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all, foldl)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing), isJust, isNothing, fromMaybe)
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck (Result, (<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, frequency, elements)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Schema modules under test
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Saturation
import Hydrogen.Schema.Color.Lightness as Lightness
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Navigation.Index as Index
import Hydrogen.Schema.Game.Entity as Entity
import Hydrogen.Schema.Game.World as World
import Hydrogen.Schema.Compute.Dispatch as Dispatch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═════════════════════════════════════════════════════════════════════════════

stateAdversarialTests :: Spec Unit
stateAdversarialTests = describe "Adversarial State Tests" do
  invariantPreservationTests
  compoundConsistencyTests
  idempotenceTests
  cascadePreventionTests

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // invariant preservation tests
-- ═════════════════════════════════════════════════════════════════════════════

invariantPreservationTests :: Spec Unit
invariantPreservationTests = describe "Invariant Preservation" do
  
  describe "Color invariants" do
    it "HSL always produces valid colors" do
      Spec.quickCheck propHSLInvariant
    
    it "RGB channels always in [0,255]" do
      Spec.quickCheck propRGBInvariant
    
    it "Opacity always in [0,100]" do
      Spec.quickCheck propOpacityInvariant
  
  describe "Index invariants" do
    it "position always < total (when total > 0)" do
      Spec.quickCheck propIndexPositionInvariant
    
    it "position always >= 0" do
      Spec.quickCheck propIndexNonNegative
  
  describe "Dispatch invariants" do
    it "workgroup dimensions always >= 1" do
      Spec.quickCheck propWorkgroupMinimum
    
    it "grid dimensions always >= 1" do
      Spec.quickCheck propGridMinimum
    
    it "shared memory always bounded" do
      Spec.quickCheck propSharedMemoryBounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // compound consistency tests
-- ═════════════════════════════════════════════════════════════════════════════

compoundConsistencyTests :: Spec Unit
compoundConsistencyTests = describe "Compound Consistency" do
  
  describe "Entity state consistency" do
    it "entity with destroyed state is not active" do
      let entity = Entity.entity 1 
            (Entity.position2D 0.0 0.0)
            (Entity.velocity2D 0.0 0.0)
            (Entity.gameRectangle 10.0 10.0)
      let destroyed = Entity.setState Entity.Destroyed entity
      Entity.isDestroyed destroyed `shouldEqual` true
      Entity.isActive destroyed `shouldEqual` false
    
    it "frozen entity state is consistent" do
      let entity = Entity.entity 1 
            (Entity.position2D 0.0 0.0)
            (Entity.velocity2D 0.0 0.0)
            (Entity.gameRectangle 10.0 10.0)
      let frozen = Entity.setState Entity.Frozen entity
      Entity.isFrozen frozen `shouldEqual` true
      Entity.isActive frozen `shouldEqual` false
  
  describe "IndexedPosition consistency" do
    it "wrap mode: position always valid after any operation" do
      let ip = Index.indexedPosition 5 10 Index.Wrap
      let advanced = Index.advance 1000 ip
      let pos = Index.position advanced
      pos `shouldSatisfy` \p -> p >= 0 && p < 10
    
    it "clamp mode: position stays at boundary" do
      let ip = Index.indexedPosition 5 10 Index.Clamp
      let advanced = Index.advance 1000 ip
      let pos = Index.position advanced
      pos `shouldEqual` 9  -- Clamped to max
    
    it "empty collection has position 0" do
      let ip = Index.indexedPosition 5 0 Index.Wrap
      Index.position ip `shouldEqual` 0
      Index.total ip `shouldEqual` 0
  
  describe "DispatchConfig consistency" do
    it "workgroup size components multiply correctly" do
      let wg = Dispatch.workgroupSize 8 8 4
      Dispatch.totalThreads wg `shouldEqual` 256
    
    it "total invocations is workgroup × grid" do
      let wg = Dispatch.workgroupSize 64 1 1
      let gr = Dispatch.gridSize 100 1 1
      let dc = Dispatch.dispatchConfig wg gr Dispatch.noSharedMemory
      Dispatch.totalInvocations dc `shouldEqual` 6400

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // idempotence tests
-- ═════════════════════════════════════════════════════════════════════════════

idempotenceTests :: Spec Unit
idempotenceTests = describe "Idempotence Properties" do
  
  describe "Clamping is idempotent" do
    it "double-clamping Hue same as single" do
      Spec.quickCheck propHueClampIdempotent
    
    it "double-clamping Saturation same as single" do
      Spec.quickCheck propSaturationClampIdempotent
    
    it "double-clamping Channel same as single" do
      Spec.quickCheck propChannelClampIdempotent
  
  describe "Normalization is idempotent" do
    it "normalizing position twice same as once" do
      let ip1 = Index.indexedPosition 15 10 Index.Wrap
      let ip2 = Index.indexedPosition (Index.position ip1) 10 Index.Wrap
      Index.position ip1 `shouldEqual` Index.position ip2
  
  describe "State transitions" do
    it "setting same state twice is idempotent" do
      let entity = Entity.entity 1 
            (Entity.position2D 0.0 0.0)
            (Entity.velocity2D 0.0 0.0)
            (Entity.gameRectangle 10.0 10.0)
      let frozen1 = Entity.setState Entity.Frozen entity
      let frozen2 = Entity.setState Entity.Frozen frozen1
      frozen1 `shouldEqual` frozen2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // cascade prevention tests
-- ═════════════════════════════════════════════════════════════════════════════

cascadePreventionTests :: Spec Unit
cascadePreventionTests = describe "Cascade Prevention" do
  
  describe "Invalid input isolation" do
    it "NaN-like inputs don't corrupt color" do
      -- While we can't inject actual NaN through smart constructors,
      -- we test extreme values that might cause issues
      let h = Hue.hue 999999999
      Hue.unwrap h `shouldSatisfy` \v -> v >= 0 && v <= 359
    
    it "extreme values don't corrupt dispatch" do
      let wg = Dispatch.workgroupSize 999999 999999 999999
      let x = Dispatch.unwrapWorkgroupDimX (Dispatch.getWorkgroupDimX wg)
      let y = Dispatch.unwrapWorkgroupDimY (Dispatch.getWorkgroupDimY wg)
      let z = Dispatch.unwrapWorkgroupDimZ (Dispatch.getWorkgroupDimZ wg)
      x `shouldSatisfy` \v -> v >= 1 && v <= 1024
      y `shouldSatisfy` \v -> v >= 1 && v <= 1024
      z `shouldSatisfy` \v -> v >= 1 && v <= 64
  
  describe "Operation chains don't accumulate errors" do
    it "1000 hue rotations don't drift" do
      let h0 = Hue.hue 0
      -- Rotate by 360 should be identity
      let rotated = foldl (\h _ -> Hue.rotate 360 h) h0 (Array.range 1 1000)
      Hue.unwrap rotated `shouldEqual` 0
    
    it "1000 channel inversions alternate correctly" do
      let c0 = Channel.channel 100
      -- 1000 inversions (even number) = identity
      let inverted = foldl (\c _ -> Channel.invert c) c0 (Array.range 1 1000)
      Channel.unwrap inverted `shouldEqual` 100
    
    it "advance/retreat cycles are stable" do
      Spec.quickCheck propAdvanceRetreatStable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // property generators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate adversarial integers
genAdversarialInt :: Gen Int
genAdversarialInt = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0))
  [ Tuple 10.0 (pure 1)
  , Tuple 10.0 (pure (-1))
  , Tuple 10.0 (pure 2147483647)
  , Tuple 10.0 (pure (-2147483648))
  , Tuple 5.0  (chooseInt (-1000) 1000)
  , Tuple 5.0  (chooseInt 1000000 2147483647)
  ]

-- | Generate adversarial numbers
genAdversarialNumber :: Gen Number
genAdversarialNumber = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0.0))
  [ Tuple 10.0 (pure 1.0)
  , Tuple 10.0 (pure (-1.0))
  , Tuple 10.0 (pure 1.0e10)
  , Tuple 10.0 (pure (-1.0e10))
  , Tuple 5.0  (Int.toNumber <$> chooseInt (-1000) 1000)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // property tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property: HSL values always produce valid ranges
propHSLInvariant :: Gen Result
propHSLInvariant = do
  h <- genAdversarialInt
  s <- genAdversarialInt
  l <- genAdversarialInt
  let hue = Hue.hue h
  let sat = Saturation.saturation s
  let lit = Lightness.lightness l
  let hv = Hue.unwrap hue
  let sv = Saturation.unwrap sat
  let lv = Lightness.unwrap lit
  pure $ (hv >= 0 && hv <= 359 && sv >= 0 && sv <= 100 && lv >= 0 && lv <= 100)
    <?> "HSL(" <> show hv <> "," <> show sv <> "," <> show lv <> ") out of bounds"

-- | Property: RGB channels always in [0,255]
propRGBInvariant :: Gen Result
propRGBInvariant = do
  r <- genAdversarialInt
  g <- genAdversarialInt
  b <- genAdversarialInt
  let rc = Channel.channel r
  let gc = Channel.channel g
  let bc = Channel.channel b
  let rv = Channel.unwrap rc
  let gv = Channel.unwrap gc
  let bv = Channel.unwrap bc
  pure $ (rv >= 0 && rv <= 255 && gv >= 0 && gv <= 255 && bv >= 0 && bv <= 255)
    <?> "RGB(" <> show rv <> "," <> show gv <> "," <> show bv <> ") out of bounds"

-- | Property: Opacity always in [0,100]
propOpacityInvariant :: Gen Result
propOpacityInvariant = do
  o <- genAdversarialInt
  let opacity = Opacity.opacity o
  let v = Opacity.unwrap opacity
  pure $ (v >= 0 && v <= 100)
    <?> "Opacity " <> show v <> " out of bounds"

-- | Property: IndexedPosition position < total (when total > 0)
propIndexPositionInvariant :: Gen Result
propIndexPositionInvariant = do
  pos <- genAdversarialInt
  total <- chooseInt 1 1000  -- Positive totals only
  let ip = Index.indexedPosition pos total Index.Wrap
  let p = Index.position ip
  let t = Index.total ip
  pure $ (t == 0 || p < t)
    <?> "Position " <> show p <> " should be < total " <> show t

-- | Property: Index position always >= 0
propIndexNonNegative :: Gen Result
propIndexNonNegative = do
  pos <- genAdversarialInt
  total <- genAdversarialInt
  let ip = Index.indexedPosition pos total Index.Wrap
  let p = Index.position ip
  pure $ (p >= 0)
    <?> "Position " <> show p <> " should be >= 0"

-- | Property: Workgroup dimensions always >= 1
propWorkgroupMinimum :: Gen Result
propWorkgroupMinimum = do
  x <- genAdversarialInt
  y <- genAdversarialInt
  z <- genAdversarialInt
  let wg = Dispatch.workgroupSize x y z
  let xv = Dispatch.unwrapWorkgroupDimX (Dispatch.getWorkgroupDimX wg)
  let yv = Dispatch.unwrapWorkgroupDimY (Dispatch.getWorkgroupDimY wg)
  let zv = Dispatch.unwrapWorkgroupDimZ (Dispatch.getWorkgroupDimZ wg)
  pure $ (xv >= 1 && yv >= 1 && zv >= 1)
    <?> "Workgroup dims (" <> show xv <> "," <> show yv <> "," <> show zv <> ") should all be >= 1"

-- | Property: Grid dimensions always >= 1
propGridMinimum :: Gen Result
propGridMinimum = do
  x <- genAdversarialInt
  y <- genAdversarialInt
  z <- genAdversarialInt
  let gr = Dispatch.gridSize x y z
  let xv = Dispatch.unwrapGridDimX (Dispatch.getGridDimX gr)
  let yv = Dispatch.unwrapGridDimY (Dispatch.getGridDimY gr)
  let zv = Dispatch.unwrapGridDimZ (Dispatch.getGridDimZ gr)
  pure $ (xv >= 1 && yv >= 1 && zv >= 1)
    <?> "Grid dims (" <> show xv <> "," <> show yv <> "," <> show zv <> ") should all be >= 1"

-- | Property: Shared memory always bounded
propSharedMemoryBounded :: Gen Result
propSharedMemoryBounded = do
  bytes <- genAdversarialInt
  let sm = Dispatch.sharedMemoryBytes bytes
  let v = Dispatch.unwrapSharedMemoryBytes sm
  pure $ (v >= 0 && v <= 49152)
    <?> "SharedMemory " <> show v <> " should be in [0, 49152]"

-- | Property: Hue clamping is idempotent
propHueClampIdempotent :: Gen Result
propHueClampIdempotent = do
  n <- genAdversarialInt
  let h1 = Hue.hue n
  let h2 = Hue.hue (Hue.unwrap h1)
  pure $ (h1 === h2)

-- | Property: Saturation clamping is idempotent
propSaturationClampIdempotent :: Gen Result
propSaturationClampIdempotent = do
  n <- genAdversarialInt
  let s1 = Saturation.saturation n
  let s2 = Saturation.saturation (Saturation.unwrap s1)
  pure $ (s1 === s2)

-- | Property: Channel clamping is idempotent
propChannelClampIdempotent :: Gen Result
propChannelClampIdempotent = do
  n <- genAdversarialInt
  let c1 = Channel.channel n
  let c2 = Channel.channel (Channel.unwrap c1)
  pure $ (c1 === c2)

-- | Property: Advance/retreat cycles are stable
propAdvanceRetreatStable :: Gen Result
propAdvanceRetreatStable = do
  pos <- chooseInt 0 99
  total <- chooseInt 1 100
  steps <- chooseInt 1 10000
  let ip0 = Index.indexedPosition pos total Index.Wrap
  let advanced = Index.advance steps ip0
  let retreated = Index.retreat steps advanced
  pure $ (Index.position retreated === Index.position ip0)
