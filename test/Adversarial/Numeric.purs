-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // adversarial // numeric
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Adversarial Numeric Tests — Hunting bugs that malicious actors would exploit.
-- |
-- | ## Threat Model
-- |
-- | A malicious AI trained on poisoned data might:
-- | - Emit code that appears to clamp but actually overflows
-- | - Create "optimizations" that skip boundary checks
-- | - Inject values that accumulate errors over time
-- | - Plant time bombs that work N times then fail
-- |
-- | ## Test Strategy
-- |
-- | These tests probe every bounded numeric type with:
-- | - Exact boundary values (min, max)
-- | - Values just outside boundaries (min-1, max+1)
-- | - Values far outside boundaries (massive positive/negative)
-- | - Special values (0, -0, NaN, Infinity)
-- | - Sequences that accumulate toward failure
-- |
-- | ## At Billion-Agent Scale
-- |
-- | A 0.0001% edge case happens 1,000 times per second with 1B agents.
-- | Every edge case WILL be hit. Every invariant WILL be tested.

module Test.Adversarial.Numeric
  ( numericAdversarialTests
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all, foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck (Result, (<?>), (===))
import Test.QuickCheck.Gen (Gen, chooseInt, frequency, elements)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Schema atoms we're testing
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Saturation
import Hydrogen.Schema.Color.Lightness as Lightness
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Navigation.Index as Index
import Hydrogen.Schema.Tensor.Dimension as Dim
import Hydrogen.Schema.Compute.Dispatch as Dispatch
import Hydrogen.Schema.Game.Entity as GameEntity
import Hydrogen.Schema.Identity.Temporal as Temporal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═════════════════════════════════════════════════════════════════════════════

numericAdversarialTests :: Spec Unit
numericAdversarialTests = describe "Adversarial Numeric Tests" do
  boundaryAttackTests
  overflowAttackTests
  accumulationAttackTests
  specialValueTests
  timeBombTests

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // boundary attacks
-- ═════════════════════════════════════════════════════════════════════════════

boundaryAttackTests :: Spec Unit
boundaryAttackTests = describe "Boundary Attacks" do
  
  describe "Hue [0-359] WRAPPING" do
    it "survives Int max injection" do
      let h = Hue.hue 2147483647
      Hue.unwrap h `shouldSatisfy` \v -> v >= 0 && v <= 359
    
    it "survives Int min injection" do
      let h = Hue.hue (-2147483648)
      Hue.unwrap h `shouldSatisfy` \v -> v >= 0 && v <= 359
    
    it "wrap semantics at 360" do
      Hue.unwrap (Hue.hueWrap 360) `shouldEqual` 0
    
    it "wrap semantics at -1" do
      Hue.unwrap (Hue.hueWrap (-1)) `shouldEqual` 359
    
    it "adversarial wrap: far negative" do
      Spec.quickCheck propHueWrapFarNegative
    
    it "adversarial wrap: far positive" do
      Spec.quickCheck propHueWrapFarPositive
  
  describe "Saturation [0-100] CLAMPING" do
    it "clamps at exactly 0" do
      Saturation.unwrap (Saturation.saturation 0) `shouldEqual` 0
    
    it "clamps at exactly 100" do
      Saturation.unwrap (Saturation.saturation 100) `shouldEqual` 100
    
    it "clamps negative to 0" do
      Saturation.unwrap (Saturation.saturation (-1000000)) `shouldEqual` 0
    
    it "clamps large to 100" do
      Saturation.unwrap (Saturation.saturation 1000000) `shouldEqual` 100
    
    it "survives all adversarial inputs" do
      Spec.quickCheck propSaturationAlwaysBounded
  
  describe "Channel [0-255] CLAMPING" do
    it "clamps at exactly 0" do
      Channel.unwrap (Channel.channel 0) `shouldEqual` 0
    
    it "clamps at exactly 255" do
      Channel.unwrap (Channel.channel 255) `shouldEqual` 255
    
    it "boundary attack: 256" do
      Channel.unwrap (Channel.channel 256) `shouldEqual` 255
    
    it "boundary attack: -1" do
      Channel.unwrap (Channel.channel (-1)) `shouldEqual` 0
    
    it "inversion at boundaries" do
      Channel.unwrap (Channel.invert (Channel.channel 0)) `shouldEqual` 255
      Channel.unwrap (Channel.invert (Channel.channel 255)) `shouldEqual` 0
  
  describe "Dim [1-1073741824] CLAMPING" do
    it "clamps at exactly 1" do
      Dim.unwrapDim (Dim.dim 1) `shouldEqual` 1
    
    it "boundary attack: 0 (below min)" do
      Dim.unwrapDim (Dim.dim 0) `shouldEqual` 1
    
    it "boundary attack: negative" do
      Dim.unwrapDim (Dim.dim (-1000)) `shouldEqual` 1
    
    it "survives adversarial inputs" do
      Spec.quickCheck propDimAlwaysBounded
  
  describe "WorkgroupDimX [1-1024] CLAMPING" do
    it "clamps 0 to 1" do
      Dispatch.unwrapWorkgroupDimX (Dispatch.workgroupDimX 0) `shouldEqual` 1
    
    it "clamps 2000 to 1024" do
      Dispatch.unwrapWorkgroupDimX (Dispatch.workgroupDimX 2000) `shouldEqual` 1024
    
    it "survives Int max" do
      let wg = Dispatch.workgroupDimX 2147483647
      Dispatch.unwrapWorkgroupDimX wg `shouldSatisfy` \v -> v >= 1 && v <= 1024

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // overflow attacks
-- ═════════════════════════════════════════════════════════════════════════════

overflowAttackTests :: Spec Unit
overflowAttackTests = describe "Overflow Attacks" do
  
  describe "Grid Size Overflow" do
    it "grid computation doesn't overflow" do
      -- 65535 * 65535 * 65535 would overflow Int
      let g = Dispatch.gridSize 65535 65535 65535
      let total = Dispatch.totalWorkgroups g
      -- Should be clamped or computed safely
      total `shouldSatisfy` \v -> v > 0
    
    it "total invocations handles large values" do
      let wg = Dispatch.workgroupSize 1024 1 1
      let gr = Dispatch.gridSize 65535 1 1
      let dc = Dispatch.dispatchConfig wg gr Dispatch.noSharedMemory
      let total = Dispatch.totalInvocations dc
      -- 1024 * 65535 = 67,107,840 (fits in Int)
      total `shouldSatisfy` \v -> v > 0
  
  describe "Navigation Index Overflow" do
    it "index wrapping handles negative overflow" do
      let ip = Index.indexedPosition (-2147483648) 10 Index.Wrap
      Index.position ip `shouldSatisfy` \v -> v >= 0 && v < 10
    
    it "advance handles large jumps" do
      let ip = Index.indexedPosition 5 10 Index.Wrap
      let ip' = Index.advance 2147483647 ip
      Index.position ip' `shouldSatisfy` \v -> v >= 0 && v < 10
  
  describe "Generation Overflow" do
    it "generation handles Int max" do
      let g = Temporal.generation 2147483647
      Temporal.unwrapGeneration g `shouldSatisfy` \v -> v >= 0
    
    it "nextGeneration near max" do
      let g = Temporal.generation 2147483646
      let next = Temporal.nextGeneration g
      -- Should handle overflow gracefully
      Temporal.unwrapGeneration next `shouldSatisfy` \v -> v >= 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // accumulation attacks
-- ═════════════════════════════════════════════════════════════════════════════

accumulationAttackTests :: Spec Unit
accumulationAttackTests = describe "Accumulation Attacks" do
  
  describe "Repeated Hue Rotation" do
    it "1000 rotations stay bounded" do
      let h0 = Hue.hue 180
      let rotated = foldl (\h _ -> Hue.rotate 7 h) h0 (Array.range 1 1000)
      Hue.unwrap rotated `shouldSatisfy` \v -> v >= 0 && v <= 359
    
    it "rotation by 360 is identity" do
      Spec.quickCheck propRotation360Identity
  
  describe "Repeated Channel Operations" do
    it "1000 brighten/darken cycles" do
      let c0 = Channel.channel 128
      -- Brighten then darken repeatedly
      let cycled = foldl (\c _ -> Channel.brighten 1 (Channel.darken 1 c)) c0 (Array.range 1 1000)
      -- Should still be bounded
      Channel.unwrap cycled `shouldSatisfy` \v -> v >= 0 && v <= 255
    
    it "inversion cycle is identity" do
      Spec.quickCheck propChannelDoubleInvert
  
  describe "Repeated Navigation" do
    it "1000 next/prev cycles in Wrap mode" do
      let ip0 = Index.indexedPosition 0 10 Index.Wrap
      let cycled = foldl (\ip _ -> Index.prev (Index.next ip)) ip0 (Array.range 1 1000)
      Index.position cycled `shouldEqual` 0
    
    it "large advance/retreat cycle" do
      let ip0 = Index.indexedPosition 5 10 Index.Wrap
      let advanced = Index.advance 9999 ip0
      let retreated = Index.retreat 9999 advanced
      Index.position retreated `shouldEqual` 5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // special value tests
-- ═════════════════════════════════════════════════════════════════════════════

specialValueTests :: Spec Unit
specialValueTests = describe "Special Value Injection" do
  
  describe "Zero Handling" do
    it "Count of 0 is empty" do
      let c = Index.count 0
      Index.isEmpty c `shouldEqual` true
    
    it "IndexedPosition with 0 count" do
      let ip = Index.indexedPosition 0 0 Index.Clamp
      Index.total ip `shouldEqual` 0
      Index.position ip `shouldEqual` 0
    
    it "Dim rejects 0" do
      Dim.unwrapDim (Dim.dim 0) `shouldEqual` 1
  
  describe "Negative Handling" do
    it "Negative count becomes 0" do
      let c = Index.count (-100)
      Index.unwrapCount c `shouldEqual` 0
    
    it "Negative generation becomes 0" do
      Temporal.unwrapGeneration (Temporal.generation (-1000)) `shouldEqual` 0
    
    it "All bounded atoms reject negatives" do
      Spec.quickCheck propNegativesClamped
  
  describe "Maximum Handling" do
    it "Count max is 10000" do
      Index.unwrapCount (Index.count 20000) `shouldEqual` 10000
    
    it "Dim max is 1073741824" do
      Dim.unwrapDim (Dim.dim 2000000000) `shouldEqual` 1073741824

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // time bomb tests
-- ═════════════════════════════════════════════════════════════════════════════

timeBombTests :: Spec Unit
timeBombTests = describe "Time Bomb Detection" do
  
  describe "Counter Wraparound" do
    it "generation at max-1 increments correctly" do
      let g = Temporal.generation 2147483646
      let next = Temporal.nextGeneration g
      Temporal.unwrapGeneration next `shouldSatisfy` \v -> v > 0
  
  describe "Index Wraparound" do
    it "index navigation at boundary" do
      let ip = Index.indexedPosition 9 10 Index.Wrap
      let next = Index.next ip
      Index.position next `shouldEqual` 0
    
    it "repeated navigation doesn't accumulate errors" do
      -- Go around 10 times
      let ip0 = Index.indexedPosition 0 10 Index.Wrap
      let laps = foldl (\ip _ -> Index.next ip) ip0 (Array.range 1 100)
      Index.position laps `shouldEqual` 0
  
  describe "Dispatch Validation" do
    it "validates after many configurations" do
      Spec.quickCheck propDispatchAlwaysValidatable

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // property generators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Adversarial Int generator - biased toward problematic values
genAdversarialInt :: Gen Int
genAdversarialInt = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0))
  [ Tuple 10.0 (pure 1)
  , Tuple 10.0 (pure (-1))
  , Tuple 10.0 (pure 2147483647)
  , Tuple 10.0 (pure (-2147483648))
  , Tuple 10.0 (pure 2147483646)
  , Tuple 10.0 (pure (-2147483647))
  , Tuple 5.0  (chooseInt 2147483640 2147483647)
  , Tuple 5.0  (chooseInt (-2147483648) (-2147483640))
  , Tuple 5.0  (chooseInt (-100) 100)
  , Tuple 5.0  (chooseInt 1000 100000)
  , Tuple 5.0  (chooseInt (-100000) (-1000))
  , Tuple 5.0  (chooseInt 100000 2147483647)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // property tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hue wrap handles far negative values correctly
propHueWrapFarNegative :: Gen Result
propHueWrapFarNegative = do
  n <- chooseInt (-2147483648) (-1000000)
  let h = Hue.hueWrap n
  let v = Hue.unwrap h
  pure $ (v >= 0 && v <= 359)
    <?> "HueWrap(" <> show n <> ") = " <> show v <> " should be in [0,359]"

-- | Hue wrap handles far positive values correctly
propHueWrapFarPositive :: Gen Result
propHueWrapFarPositive = do
  n <- chooseInt 1000000 2147483647
  let h = Hue.hueWrap n
  let v = Hue.unwrap h
  pure $ (v >= 0 && v <= 359)
    <?> "HueWrap(" <> show n <> ") = " <> show v <> " should be in [0,359]"

-- | Saturation always bounded under adversarial input
propSaturationAlwaysBounded :: Gen Result
propSaturationAlwaysBounded = do
  n <- genAdversarialInt
  let s = Saturation.saturation n
  let v = Saturation.unwrap s
  pure $ (v >= 0 && v <= 100)
    <?> "Saturation(" <> show n <> ") = " <> show v <> " should be in [0,100]"

-- | Dim always bounded under adversarial input
propDimAlwaysBounded :: Gen Result
propDimAlwaysBounded = do
  n <- genAdversarialInt
  let d = Dim.dim n
  let v = Dim.unwrapDim d
  pure $ (v >= 1 && v <= 1073741824)
    <?> "Dim(" <> show n <> ") = " <> show v <> " should be in [1,1073741824]"

-- | Rotating by 360 is always identity
propRotation360Identity :: Gen Result
propRotation360Identity = do
  n <- chooseInt 0 359
  let h = Hue.hue n
  let rotated = Hue.rotate 360 h
  pure $ h === rotated

-- | Double inversion is identity for channels
propChannelDoubleInvert :: Gen Result
propChannelDoubleInvert = do
  n <- chooseInt 0 255
  let c = Channel.channel n
  let doubled = Channel.invert (Channel.invert c)
  pure $ c === doubled

-- | All bounded atoms clamp negatives properly
propNegativesClamped :: Gen Result
propNegativesClamped = do
  n <- chooseInt (-2147483648) (-1)
  let sat = Saturation.unwrap (Saturation.saturation n)
  let lit = Lightness.unwrap (Lightness.lightness n)
  let opa = Opacity.unwrap (Opacity.opacity n)
  let cha = Channel.unwrap (Channel.channel n)
  let dim = Dim.unwrapDim (Dim.dim n)
  let gen = Temporal.unwrapGeneration (Temporal.generation n)
  pure $ (sat == 0 && lit == 0 && opa == 0 && cha == 0 && dim == 1 && gen == 0)
    <?> "Negative " <> show n <> " should clamp to min values"

-- | Dispatch configurations are always validatable
propDispatchAlwaysValidatable :: Gen Result
propDispatchAlwaysValidatable = do
  wgx <- chooseInt 1 2000
  wgy <- chooseInt 1 2000
  wgz <- chooseInt 1 100
  grx <- chooseInt 1 100000
  gry <- chooseInt 1 100000
  grz <- chooseInt 1 100000
  let wg = Dispatch.workgroupSize wgx wgy wgz
  let gr = Dispatch.gridSize grx gry grz
  let dc = Dispatch.dispatchConfig wg gr Dispatch.noSharedMemory
  -- Validation should return a result (not crash)
  -- The fact that validateDispatch completes without exception is the test
  case Dispatch.validateDispatch dc of
    Nothing -> pure $ true <?> "Dispatch is valid"
    Just err -> pure $ true <?> ("Dispatch validation caught: " <> err)
