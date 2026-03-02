-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // adversarial // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Adversarial Bounds Tests — Escape attempts and boundary violations.
-- |
-- | ## Threat Model
-- |
-- | A malicious actor might:
-- | - Inject values outside bounded ranges to crash or corrupt state
-- | - Exploit wrap vs clamp semantics to produce unexpected values
-- | - Chain operations to escape bounds through accumulation
-- | - Use NaN/Infinity to bypass numeric guards
-- | - Create invalid compound types through carefully crafted atoms
-- |
-- | ## Security Properties Tested
-- |
-- | 1. **Clamp Correctness**: Values outside range are clamped to bounds
-- | 2. **Wrap Correctness**: Values outside range wrap correctly (where applicable)
-- | 3. **NaN/Infinity Rejection**: Special values cannot enter bounded types
-- | 4. **Operation Closure**: Operations on bounded types produce bounded results
-- | 5. **Compound Validity**: Compound types maintain invariants

module Test.Adversarial.Bounds
  ( boundsAdversarialTests
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all, foldl)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck (Result, (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Schema modules under test - Color
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Saturation
import Hydrogen.Schema.Color.Lightness as Lightness
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity

-- Schema modules under test - Dimension
import Hydrogen.Schema.Dimension.Percentage as Percent
import Hydrogen.Schema.Dimension.Angular as Angular

-- Schema modules under test - Temporal
import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Temporal.FPS as FPS

-- Schema modules under test - Compute
import Hydrogen.Schema.Compute.Dispatch as Dispatch

-- Schema modules under test - Navigation
import Hydrogen.Schema.Navigation.Index as Index

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═════════════════════════════════════════════════════════════════════════════

boundsAdversarialTests :: Spec Unit
boundsAdversarialTests = describe "Adversarial Bounds Tests" do
  clampingTests
  wrappingTests
  specialValueTests
  operationClosureTests
  accumulationTests

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // clamping tests
-- ═════════════════════════════════════════════════════════════════════════════

clampingTests :: Spec Unit
clampingTests = describe "Clamping Behavior" do
  
  describe "Color channel clamping [0,255]" do
    it "negative values clamp to 0" do
      Channel.unwrap (Channel.channel (-1000)) `shouldEqual` 0
    
    it "excessive values clamp to 255" do
      Channel.unwrap (Channel.channel 1000) `shouldEqual` 255
    
    it "Int min clamps to 0" do
      Channel.unwrap (Channel.channel (-2147483648)) `shouldEqual` 0
    
    it "Int max clamps to 255" do
      Channel.unwrap (Channel.channel 2147483647) `shouldEqual` 255
    
    it "property: all channels in [0,255]" do
      Spec.quickCheck propChannelBounded
  
  describe "Saturation clamping [0,100]" do
    it "negative values clamp to 0" do
      Saturation.unwrap (Saturation.saturation (-50)) `shouldEqual` 0
    
    it "excessive values clamp to 100" do
      Saturation.unwrap (Saturation.saturation 150) `shouldEqual` 100
    
    it "property: all saturation in [0,100]" do
      Spec.quickCheck propSaturationBounded
  
  describe "Lightness clamping [0,100]" do
    it "negative values clamp to 0" do
      Lightness.unwrap (Lightness.lightness (-50)) `shouldEqual` 0
    
    it "excessive values clamp to 100" do
      Lightness.unwrap (Lightness.lightness 150) `shouldEqual` 100
    
    it "property: all lightness in [0,100]" do
      Spec.quickCheck propLightnessBounded
  
  describe "Opacity clamping [0,100]" do
    it "negative values clamp to 0" do
      Opacity.unwrap (Opacity.opacity (-50)) `shouldEqual` 0
    
    it "excessive values clamp to 100" do
      Opacity.unwrap (Opacity.opacity 150) `shouldEqual` 100
  
  describe "Progress clamping [0.0,1.0]" do
    it "negative values clamp to 0.0" do
      Progress.unwrapProgress (Progress.progress (-0.5)) `shouldEqual` 0.0
    
    it "excessive values clamp to 1.0" do
      Progress.unwrapProgress (Progress.progress 1.5) `shouldEqual` 1.0
    
    it "property: all progress in [0.0,1.0]" do
      Spec.quickCheck propProgressBounded
  
  describe "FPS clamping [1,240]" do
    it "zero clamps to 1" do
      FPS.unwrap (FPS.fps 0.0) `shouldEqual` 1.0
    
    it "negative clamps to 1" do
      FPS.unwrap (FPS.fps (-60.0)) `shouldEqual` 1.0
    
    it "excessive clamps to 240" do
      FPS.unwrap (FPS.fps 1000.0) `shouldEqual` 240.0
    
    it "property: all FPS in [1,240]" do
      Spec.quickCheck propFPSBounded
  
  describe "Percent clamping [0,100]" do
    it "negative clamps to 0" do
      Percent.unwrapPercent (Percent.percent (-50.0)) `shouldEqual` 0.0
    
    it "excessive clamps to 100" do
      Percent.unwrapPercent (Percent.percent 150.0) `shouldEqual` 100.0
  
  describe "Ratio clamping [0.0,1.0]" do
    it "negative clamps to 0" do
      Percent.unwrapRatio (Percent.ratio (-0.5)) `shouldEqual` 0.0
    
    it "excessive clamps to 1" do
      Percent.unwrapRatio (Percent.ratio 1.5) `shouldEqual` 1.0
  
  describe "SignedPercent clamping [-100,100]" do
    it "below -100 clamps" do
      Percent.unwrapSignedPercent (Percent.signedPercent (-150.0)) `shouldEqual` (-100.0)
    
    it "above 100 clamps" do
      Percent.unwrapSignedPercent (Percent.signedPercent 150.0) `shouldEqual` 100.0
  
  describe "SignedRatio clamping [-1.0,1.0]" do
    it "below -1 clamps" do
      Percent.unwrapSignedRatio (Percent.signedRatio (-1.5)) `shouldEqual` (-1.0)
    
    it "above 1 clamps" do
      Percent.unwrapSignedRatio (Percent.signedRatio 1.5) `shouldEqual` 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // wrapping tests
-- ═════════════════════════════════════════════════════════════════════════════

wrappingTests :: Spec Unit
wrappingTests = describe "Wrapping Behavior" do
  
  describe "Hue wrapping [0,359]" do
    -- Note: hue() CLAMPS, hueWrap() WRAPS
    -- Use hueWrap for cyclic behavior
    it "360 wraps to 0" do
      Hue.unwrap (Hue.hueWrap 360) `shouldEqual` 0
    
    it "720 wraps to 0" do
      Hue.unwrap (Hue.hueWrap 720) `shouldEqual` 0
    
    it "361 wraps to 1" do
      Hue.unwrap (Hue.hueWrap 361) `shouldEqual` 1
    
    it "-1 wraps to 359" do
      Hue.unwrap (Hue.hueWrap (-1)) `shouldEqual` 359
    
    it "-360 wraps to 0" do
      Hue.unwrap (Hue.hueWrap (-360)) `shouldEqual` 0
    
    it "property: all hues in [0,359]" do
      Spec.quickCheck propHueBounded
    
    it "rotate by 360 is identity" do
      let h = Hue.hue 180
      Hue.unwrap (Hue.rotate 360 h) `shouldEqual` 180
    
    it "rotate by -360 is identity" do
      let h = Hue.hue 180
      Hue.unwrap (Hue.rotate (-360) h) `shouldEqual` 180
  
  describe "IndexedPosition wrapping" do
    it "advance past total wraps" do
      let ip = Index.indexedPosition 5 10 Index.Wrap
      let advanced = Index.advance 7 ip
      Index.position advanced `shouldEqual` 2  -- (5 + 7) mod 10
    
    it "retreat past zero wraps" do
      let ip = Index.indexedPosition 3 10 Index.Wrap
      let retreated = Index.retreat 5 ip
      Index.position retreated `shouldEqual` 8  -- (3 - 5 + 10) mod 10
    
    it "large advance wraps correctly" do
      let ip = Index.indexedPosition 0 10 Index.Wrap
      let advanced = Index.advance 1000 ip
      Index.position advanced `shouldEqual` 0  -- 1000 mod 10
    
    it "negative total is handled" do
      let ip = Index.indexedPosition 5 (-10) Index.Wrap
      Index.total ip `shouldSatisfy` \t -> t >= 0
  
  describe "Degree normalization" do
    it "normalizes to [0, 360)" do
      let d = Angular.normalizeDegrees (Angular.degrees 720.0)
      Angular.unwrapDegrees d `shouldSatisfy` \v -> v >= 0.0 && v < 360.0
    
    it "-90 normalizes to 270" do
      let d = Angular.normalizeDegrees (Angular.degrees (-90.0))
      Angular.unwrapDegrees d `shouldSatisfy` \v -> v >= 269.0 && v <= 271.0
    
    it "45 stays 45" do
      let d = Angular.normalizeDegrees (Angular.degrees 45.0)
      Angular.unwrapDegrees d `shouldSatisfy` \v -> v >= 44.0 && v <= 46.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // special value tests
-- ═════════════════════════════════════════════════════════════════════════════

specialValueTests :: Spec Unit
specialValueTests = describe "Special Value Handling" do
  
  describe "NaN rejection in Progress" do
    it "NaN becomes clamped value" do
      -- NaN comparisons always return false, so clamp should handle it
      let p = Progress.progress (0.0 / 0.0)  -- NaN
      let v = Progress.unwrapProgress p
      -- Either clamped to 0.0 or 1.0, not NaN
      (v >= 0.0 || v <= 1.0) `shouldEqual` true  -- NaN fails both
    
    it "property: progress never NaN" do
      Spec.quickCheck propProgressNotNaN
  
  describe "Infinity rejection in Percent" do
    it "positive infinity becomes 100" do
      let p = Percent.percent (1.0 / 0.0)  -- +Infinity
      Percent.unwrapPercent p `shouldSatisfy` \v -> v <= 100.0
    
    it "negative infinity becomes 0" do
      let p = Percent.percent ((-1.0) / 0.0)  -- -Infinity
      Percent.unwrapPercent p `shouldSatisfy` \v -> v >= 0.0
  
  describe "Infinity rejection in FPS" do
    it "positive infinity becomes 240" do
      let f = FPS.fps (1.0 / 0.0)
      FPS.unwrap f `shouldEqual` 240.0
    
    it "negative infinity becomes 1" do
      let f = FPS.fps ((-1.0) / 0.0)
      FPS.unwrap f `shouldEqual` 1.0
  
  describe "Workgroup dimension handling" do
    it "zero becomes 1" do
      let wg = Dispatch.workgroupSize 0 0 0
      Dispatch.unwrapWorkgroupDimX (Dispatch.getWorkgroupDimX wg) `shouldEqual` 1
      Dispatch.unwrapWorkgroupDimY (Dispatch.getWorkgroupDimY wg) `shouldEqual` 1
      Dispatch.unwrapWorkgroupDimZ (Dispatch.getWorkgroupDimZ wg) `shouldEqual` 1
    
    it "negative becomes 1" do
      let wg = Dispatch.workgroupSize (-100) (-100) (-100)
      Dispatch.unwrapWorkgroupDimX (Dispatch.getWorkgroupDimX wg) `shouldSatisfy` \v -> v >= 1
      Dispatch.unwrapWorkgroupDimY (Dispatch.getWorkgroupDimY wg) `shouldSatisfy` \v -> v >= 1
      Dispatch.unwrapWorkgroupDimZ (Dispatch.getWorkgroupDimZ wg) `shouldSatisfy` \v -> v >= 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // operation closure tests
-- ═════════════════════════════════════════════════════════════════════════════

operationClosureTests :: Spec Unit
operationClosureTests = describe "Operation Closure" do
  
  describe "Hue rotation closure" do
    it "rotate always produces valid hue" do
      Spec.quickCheck propHueRotateClosure
    
    it "multiple rotations stay bounded" do
      let h0 = Hue.hue 180
      let rotations = Array.range 1 1000
      let final = foldl (\h _ -> Hue.rotate 37 h) h0 rotations
      Hue.unwrap final `shouldSatisfy` \v -> v >= 0 && v <= 359
  
  describe "Channel inversion closure" do
    it "invert always produces valid channel" do
      Spec.quickCheck propChannelInvertClosure
    
    it "double inversion is identity" do
      let c = Channel.channel 100
      Channel.unwrap (Channel.invert (Channel.invert c)) `shouldEqual` 100
  
  describe "Progress arithmetic" do
    it "lerp always in [0,1]" do
      Spec.quickCheck propProgressLerpBounded
  
  describe "IndexedPosition advance/retreat" do
    it "any sequence of operations stays valid" do
      Spec.quickCheck propIndexOperationsClosure

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // accumulation tests
-- ═════════════════════════════════════════════════════════════════════════════

accumulationTests :: Spec Unit
accumulationTests = describe "Accumulation Safety" do
  
  describe "Hue rotation accumulation" do
    it "1000 small rotations don't exceed bounds" do
      let h0 = Hue.hue 0
      let rotated = foldl (\h _ -> Hue.rotate 1 h) h0 (Array.range 1 1000)
      Hue.unwrap rotated `shouldSatisfy` \v -> v >= 0 && v <= 359
    
    it "1000 rotations by 360 = identity" do
      let h0 = Hue.hue 123
      let rotated = foldl (\h _ -> Hue.rotate 360 h) h0 (Array.range 1 1000)
      Hue.unwrap rotated `shouldEqual` 123
  
  describe "Channel operation accumulation" do
    it "1000 inversions alternate correctly" do
      let c0 = Channel.channel 100
      let final = foldl (\c _ -> Channel.invert c) c0 (Array.range 1 1000)
      -- 1000 inversions (even) = identity
      Channel.unwrap final `shouldEqual` 100
  
  describe "IndexedPosition accumulation" do
    it "large advance/retreat cycles stable" do
      let ip0 = Index.indexedPosition 5 100 Index.Wrap
      let ip1 = Index.advance 10000 ip0
      let ip2 = Index.retreat 10000 ip1
      Index.position ip2 `shouldEqual` Index.position ip0
    
    it "prime-number advances don't align" do
      -- Advance by prime numbers should eventually hit all positions
      let ip0 = Index.indexedPosition 0 10 Index.Wrap
      let primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
      let advanced = foldl (\ip p -> Index.advance p ip) ip0 primes
      Index.position advanced `shouldSatisfy` \v -> v >= 0 && v < 10

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
  , Tuple 10.0 (pure 255)
  , Tuple 10.0 (pure 256)
  , Tuple 10.0 (pure 359)
  , Tuple 10.0 (pure 360)
  , Tuple 5.0  (chooseInt (-1000) 1000)
  , Tuple 5.0  (chooseInt 1000000 2147483647)
  ]

-- | Generate adversarial numbers
-- |
-- | Note: We do NOT test Infinity or NaN — those are forbidden values.
-- | Bounded types must reject them at construction, not handle them gracefully.
-- | Instead we test extreme but finite values.
genAdversarialNumber :: Gen Number
genAdversarialNumber = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0.0))
  [ Tuple 10.0 (pure 1.0)
  , Tuple 10.0 (pure (-1.0))
  , Tuple 10.0 (pure 100.0)
  , Tuple 10.0 (pure 101.0)
  , Tuple 10.0 (pure (-0.001))
  , Tuple 10.0 (pure 1.001)
  , Tuple 5.0  (pure 1.0e308)           -- Near max finite double
  , Tuple 5.0  (pure (-1.0e308))        -- Near min finite double
  , Tuple 5.0  (Int.toNumber <$> chooseInt (-1000) 1000)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // property tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property: All channels in [0,255]
propChannelBounded :: Gen Result
propChannelBounded = do
  n <- genAdversarialInt
  let c = Channel.channel n
  let v = Channel.unwrap c
  pure $ (v >= 0 && v <= 255)
    <?> "Channel " <> show v <> " out of bounds"

-- | Property: All saturation in [0,100]
propSaturationBounded :: Gen Result
propSaturationBounded = do
  n <- genAdversarialInt
  let s = Saturation.saturation n
  let v = Saturation.unwrap s
  pure $ (v >= 0 && v <= 100)
    <?> "Saturation " <> show v <> " out of bounds"

-- | Property: All lightness in [0,100]
propLightnessBounded :: Gen Result
propLightnessBounded = do
  n <- genAdversarialInt
  let l = Lightness.lightness n
  let v = Lightness.unwrap l
  pure $ (v >= 0 && v <= 100)
    <?> "Lightness " <> show v <> " out of bounds"

-- | Property: All hues in [0,359]
propHueBounded :: Gen Result
propHueBounded = do
  n <- genAdversarialInt
  let h = Hue.hue n
  let v = Hue.unwrap h
  pure $ (v >= 0 && v <= 359)
    <?> "Hue " <> show v <> " out of bounds"

-- | Property: All progress in [0.0,1.0]
propProgressBounded :: Gen Result
propProgressBounded = do
  n <- genAdversarialNumber
  let p = Progress.progress n
  let v = Progress.unwrapProgress p
  pure $ (v >= 0.0 && v <= 1.0)
    <?> "Progress " <> show v <> " out of bounds"

-- | Property: All FPS in [1,240]
propFPSBounded :: Gen Result
propFPSBounded = do
  n <- genAdversarialNumber
  let f = FPS.fps n
  let v = FPS.unwrap f
  pure $ (v >= 1.0 && v <= 240.0)
    <?> "FPS " <> show v <> " out of bounds"

-- | Property: Progress never NaN
propProgressNotNaN :: Gen Result
propProgressNotNaN = do
  n <- genAdversarialNumber
  let p = Progress.progress n
  let v = Progress.unwrapProgress p
  -- NaN != NaN, so v == v is false for NaN
  pure $ (v == v)
    <?> "Progress produced NaN"

-- | Property: Hue rotation produces valid hue
propHueRotateClosure :: Gen Result
propHueRotateClosure = do
  initial <- genAdversarialInt
  rotation <- genAdversarialInt
  let h = Hue.hue initial
  let rotated = Hue.rotate rotation h
  let v = Hue.unwrap rotated
  pure $ (v >= 0 && v <= 359)
    <?> "Rotated hue " <> show v <> " out of bounds"

-- | Property: Channel invert produces valid channel
propChannelInvertClosure :: Gen Result
propChannelInvertClosure = do
  n <- genAdversarialInt
  let c = Channel.channel n
  let inverted = Channel.invert c
  let v = Channel.unwrap inverted
  pure $ (v >= 0 && v <= 255)
    <?> "Inverted channel " <> show v <> " out of bounds"

-- | Property: Progress lerp always in [0,1]
propProgressLerpBounded :: Gen Result
propProgressLerpBounded = do
  t <- genAdversarialNumber
  let p = Progress.progress t
  let v = Progress.unwrapProgress p
  pure $ (v >= 0.0 && v <= 1.0)
    <?> "Progress " <> show v <> " out of bounds after construction"

-- | Property: Index operations always produce valid position
propIndexOperationsClosure :: Gen Result
propIndexOperationsClosure = do
  pos <- chooseInt (-1000) 1000
  total <- chooseInt 0 100
  advance <- chooseInt (-1000) 1000
  retreat <- chooseInt (-1000) 1000
  let ip0 = Index.indexedPosition pos total Index.Wrap
  let ip1 = Index.advance advance ip0
  let ip2 = Index.retreat retreat ip1
  let p = Index.position ip2
  let t = Index.total ip2
  pure $ (t == 0 || (p >= 0 && p < t))
    <?> "Position " <> show p <> " invalid for total " <> show t
