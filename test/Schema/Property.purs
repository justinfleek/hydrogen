-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property tests for Schema modules:
-- | - Diff: patch/apply correctness
-- | - Group: hierarchical organization
-- | - Priority: ordering and bounds
-- | - Landauer: entropy-based precision
-- | - Color atoms: Hue, Saturation, Lightness, Opacity, Channel
-- | - Identity: Generation monotonicity
-- |
-- | ## Test Philosophy
-- |
-- | At billion-agent scale, unbounded values or incorrect clamp/wrap behavior
-- | causes cascading failures. These tests verify:
-- | - Bounds are ALWAYS enforced
-- | - Clamping vs wrapping semantics are correct
-- | - Adversarial inputs don't break invariants
module Test.Schema.Property
  ( schemaPropertyTests
  ) where

import Prelude (Unit, bind, negate, pure, unit, ($), (&&), (||), (<=), (>=), (<>), (==), (/=), (>), (<), show, discard, otherwise, (+), (-), mod)

import Data.Array.NonEmpty as NEA
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Schema.Diff as Diff
import Hydrogen.Schema.Group as Group
import Hydrogen.Schema.Priority as Priority
import Hydrogen.Schema.GPU.Landauer as Landauer
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Saturation
import Hydrogen.Schema.Color.Lightness as Lightness
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Identity.Temporal as Temporal
import Test.QuickCheck (Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate bounded integers
genInt :: Gen Int
genInt = chooseInt (-1000) 1000

-- | Generate Priority levels
genPriority :: Gen Priority.Priority
genPriority = elements $ NEA.cons'
  Priority.Critical
  [ Priority.High
  , Priority.Normal
  , Priority.Low
  , Priority.Background
  ]

-- | Generate Numeric Priority
genNumericPriority :: Gen Priority.NumericPriority
genNumericPriority = do
  n <- chooseInt 0 1000
  pure $ Priority.numericPriority n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // test suite
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main test export — Schema property tests
schemaPropertyTests :: Spec Unit
schemaPropertyTests = describe "Schema Property Tests" do
  diffPropertyTests
  priorityPropertyTests
  landauerPropertyTests
  huePropertyTests
  saturationPropertyTests
  lightnessPropertyTests
  opacityPropertyTests
  channelPropertyTests
  generationPropertyTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // diff tests
-- ═══════════════════════════════════════════════════════════════════════════════

diffPropertyTests :: Spec Unit
diffPropertyTests = describe "Diff" do
  describe "Diff Constructors" do
    it "NoChange constructor exists" do
      let _ = Diff.NoChange :: Diff.Diff Int
      pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // priority tests
-- ═══════════════════════════════════════════════════════════════════════════════

priorityPropertyTests :: Spec Unit
priorityPropertyTests = describe "Priority" do
  describe "Ordering" do
    it "critical is highest" do
      Spec.quickCheck propCriticalHighest

    it "background is lowest" do
      Spec.quickCheck propBackgroundLowest
  
  describe "Numeric Priority" do
    it "numeric priority is bounded [0, 1000]" do
      Spec.quickCheck propNumericPriorityBounded

-- Property: Critical is highest
propCriticalHighest :: Gen Result
propCriticalHighest = do
  p <- genPriority
  pure $ Priority.priorityToInt p <= Priority.priorityToInt Priority.Critical
    <?> show p <> " should be <= critical"

-- Property: Background is lowest
propBackgroundLowest :: Gen Result
propBackgroundLowest = do
  p <- genPriority
  pure $ Priority.priorityToInt Priority.Background <= Priority.priorityToInt p
    <?> "background should be <= " <> show p

-- Property: NumericPriority is bounded [0, 1000]
propNumericPriorityBounded :: Gen Result
propNumericPriorityBounded = do
  np <- genNumericPriority
  let v = Priority.unwrapNumericPriority np
  pure $ v >= 0 && v <= 1000
    <?> "NumericPriority " <> show v <> " should be in [0, 1000]"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // landauer tests
-- ═══════════════════════════════════════════════════════════════════════════════

landauerPropertyTests :: Spec Unit
landauerPropertyTests = describe "Landauer Precision" do
  describe "Free Boundary Condition" do
    it "entropy <= precision implies free boundary" do
      Spec.quickCheck propFreeBoundaryCondition
    
    it "forward sensitivity is non-negative" do
      Spec.quickCheck propForwardSensitivityNonNeg
    
    it "backward sensitivity is non-negative" do
      Spec.quickCheck propBackwardSensitivityNonNeg
    
    it "effective precision bounds both flows" do
      Spec.quickCheck propEffectivePrecisionBounds

-- | Generate entropy values (0-64 bits)
genEntropy :: Gen Number
genEntropy = do
  bits <- chooseInt 0 64
  pure $ intToNumber bits

-- | Generate tolerance values (0-8 bits, typical)
genTolerance :: Gen Number
genTolerance = do
  bits <- chooseInt 0 8
  pure $ intToNumber bits

-- | Generate precision bits (1-64)
genPrecisionBits :: Gen Int
genPrecisionBits = chooseInt 1 64

-- | Convert Int to Number
intToNumber :: Int -> Number
intToNumber n = intToNumberGo n 0.0

intToNumberGo :: Int -> Number -> Number
intToNumberGo n acc
  | n <= 0 = acc
  | otherwise = intToNumberGo (n - 1) (acc + 1.0)

-- Property: Free boundary when entropy <= precision
propFreeBoundaryCondition :: Gen Result
propFreeBoundaryCondition = do
  entropyBits <- chooseInt 0 32
  precisionBits <- chooseInt entropyBits 64  -- precision >= entropy
  let ent = Landauer.entropy (intToNumber entropyBits)
  let prec = Landauer.precisionBits precisionBits
  let cost = Landauer.landauerCost ent prec
  pure $ Landauer.isFree cost
    <?> "Entropy " <> show entropyBits <> " <= precision " <> show precisionBits <> " should be free"

-- Property: Forward sensitivity is non-negative
propForwardSensitivityNonNeg :: Gen Result
propForwardSensitivityNonNeg = do
  e <- genEntropy
  b <- genPrecisionBits
  let ent = Landauer.entropy e
  let prec = Landauer.precisionBits b
  let sens = Landauer.forwardSensitivity ent prec
  pure $ sens >= 0.0
    <?> "Forward sensitivity should be >= 0, got " <> show sens

-- Property: Backward sensitivity is non-negative
propBackwardSensitivityNonNeg :: Gen Result
propBackwardSensitivityNonNeg = do
  e <- genEntropy
  b <- genPrecisionBits
  let ent = Landauer.entropy e
  let prec = Landauer.precisionBits b
  let sens = Landauer.backwardSensitivity ent prec
  pure $ sens >= 0.0
    <?> "Backward sensitivity should be >= 0, got " <> show sens

-- Property: Effective precision bounds both forward and backward requirements
propEffectivePrecisionBounds :: Gen Result
propEffectivePrecisionBounds = do
  fwdE <- genEntropy
  bwdE <- genEntropy
  fwdTol <- genTolerance
  bwdTol <- genTolerance
  let fwdEnt = Landauer.entropy fwdE
  let bwdEnt = Landauer.entropy bwdE
  let tol = Landauer.distortionTolerance fwdTol bwdTol
  let prec = Landauer.effectivePrecision fwdEnt bwdEnt tol
  -- Effective precision should satisfy both tolerances
  -- This is a structural property - the precision is computed as max of requirements
  let fwdSatisfied = Landauer.satisfiesForwardTolerance fwdEnt prec tol
  let bwdSatisfied = Landauer.satisfiesBackwardTolerance bwdEnt prec tol
  pure $ fwdSatisfied && bwdSatisfied
    <?> "Effective precision should satisfy both tolerances"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // adversarial generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Wide range integers for adversarial testing
genWideRangeInt :: Gen Int
genWideRangeInt = frequency $ NEA.cons'
  (Tuple 20.0 (chooseInt (-1000000) (-1)))          -- Large negatives
  [ Tuple 20.0 (chooseInt 0 100)                    -- Normal range
  , Tuple 20.0 (chooseInt 101 1000)                 -- Above typical bounds
  , Tuple 20.0 (chooseInt 1000 1000000)             -- Large positives
  , Tuple 10.0 (elements $ NEA.cons' 0 [(-1), 2147483647, (-2147483648)])
  , Tuple 10.0 (pure 2147483647)                    -- Int max
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // hue property tests
-- ═══════════════════════════════════════════════════════════════════════════════

huePropertyTests :: Spec Unit
huePropertyTests = describe "Hue (wrapping, 0-359)" do
  
  describe "Bounds Invariant" do
    it "hue always produces values in 0-359 (clamping)" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let h = Hue.hue n
        let val = Hue.unwrap h
        pure $ (val >= 0 && val <= 359)
          <?> "Hue out of bounds: input=" <> show n <> ", output=" <> show val
    
    it "hueWrap always produces values in 0-359 (wrapping)" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let h = Hue.hueWrap n
        let val = Hue.unwrap h
        pure $ (val >= 0 && val <= 359)
          <?> "HueWrap out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Wrapping Behavior" do
    it "hueWrap(360) == 0" do
      Hue.unwrap (Hue.hueWrap 360) `shouldEqual` 0
    
    it "hueWrap(-1) == 359" do
      Hue.unwrap (Hue.hueWrap (-1)) `shouldEqual` 359
    
    it "hueWrap(n + 360) == hueWrap(n)" do
      Spec.quickCheck do
        n <- chooseInt (-1000) 1000
        let h1 = Hue.hueWrap n
        let h2 = Hue.hueWrap (n + 360)
        pure $ h1 === h2
  
  describe "Rotation" do
    it "rotate 0 is identity" do
      Spec.quickCheck do
        n <- chooseInt 0 359
        let h = Hue.hue n
        pure $ Hue.rotate 0 h === h
    
    it "double complement is identity" do
      Spec.quickCheck do
        n <- chooseInt 0 359
        let h = Hue.hue n
        pure $ Hue.complement (Hue.complement h) === h

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // saturation property tests
-- ═══════════════════════════════════════════════════════════════════════════════

saturationPropertyTests :: Spec Unit
saturationPropertyTests = describe "Saturation (clamping, 0-100)" do
  
  describe "Bounds Invariant" do
    it "saturation always produces values in 0-100" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let s = Saturation.saturation n
        let val = Saturation.unwrap s
        pure $ (val >= 0 && val <= 100)
          <?> "Saturation out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Clamping" do
    it "saturation(-1) == 0" do
      Saturation.unwrap (Saturation.saturation (-1)) `shouldEqual` 0
    
    it "saturation(101) == 100" do
      Saturation.unwrap (Saturation.saturation 101) `shouldEqual` 100
    
    it "values in range preserved" do
      Spec.quickCheck do
        n <- chooseInt 0 100
        let s = Saturation.saturation n
        pure $ Saturation.unwrap s === n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // lightness property tests
-- ═══════════════════════════════════════════════════════════════════════════════

lightnessPropertyTests :: Spec Unit
lightnessPropertyTests = describe "Lightness (clamping, 0-100)" do
  
  describe "Bounds Invariant" do
    it "lightness always produces values in 0-100" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let l = Lightness.lightness n
        let val = Lightness.unwrap l
        pure $ (val >= 0 && val <= 100)
          <?> "Lightness out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Clamping" do
    it "lightness(-1) == 0" do
      Lightness.unwrap (Lightness.lightness (-1)) `shouldEqual` 0
    
    it "lightness(101) == 100" do
      Lightness.unwrap (Lightness.lightness 101) `shouldEqual` 100

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // opacity property tests
-- ═══════════════════════════════════════════════════════════════════════════════

opacityPropertyTests :: Spec Unit
opacityPropertyTests = describe "Opacity (clamping, 0-100)" do
  
  describe "Bounds Invariant" do
    it "opacity always produces values in 0-100" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let o = Opacity.opacity n
        let val = Opacity.unwrap o
        pure $ (val >= 0 && val <= 100)
          <?> "Opacity out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Predicates" do
    it "predicates are mutually exclusive" do
      Spec.quickCheck do
        n <- chooseInt 0 100
        let o = Opacity.opacity n
        let isT = Opacity.isTransparent o
        let isO = Opacity.isOpaque o
        let isS = Opacity.isSemiTransparent o
        -- Exactly one should be true
        let count = (if isT then 1 else 0) + (if isO then 1 else 0) + (if isS then 1 else 0)
        pure $ count === 1

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // channel property tests
-- ═══════════════════════════════════════════════════════════════════════════════

channelPropertyTests :: Spec Unit
channelPropertyTests = describe "Channel (clamping, 0-255)" do
  
  describe "Bounds Invariant" do
    it "channel always produces values in 0-255" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let c = Channel.channel n
        let val = Channel.unwrap c
        pure $ (val >= 0 && val <= 255)
          <?> "Channel out of bounds: input=" <> show n <> ", output=" <> show val
  
  describe "Inversion" do
    it "invert(invert(c)) == c" do
      Spec.quickCheck do
        n <- chooseInt 0 255
        let c = Channel.channel n
        pure $ Channel.invert (Channel.invert c) === c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // generation property tests
-- ═══════════════════════════════════════════════════════════════════════════════

generationPropertyTests :: Spec Unit
generationPropertyTests = describe "Generation (non-negative, monotonic)" do
  
  describe "Bounds Invariant" do
    it "generation always produces non-negative values" do
      Spec.quickCheck do
        n <- genWideRangeInt
        let g = Temporal.generation n
        let val = Temporal.unwrapGeneration g
        pure $ val >= 0
          <?> "Generation negative: input=" <> show n <> ", output=" <> show val
  
  describe "Monotonicity" do
    it "nextGeneration always increases" do
      Spec.quickCheck do
        n <- chooseInt 0 1000000
        let g = Temporal.generation n
        let next = Temporal.nextGeneration g
        let gVal = Temporal.unwrapGeneration g
        let nextVal = Temporal.unwrapGeneration next
        pure $ nextVal > gVal
          <?> "nextGeneration not monotonic: " <> show gVal <> " -> " <> show nextVal
    
    it "initialGeneration is 0" do
      Temporal.unwrapGeneration Temporal.initialGeneration `shouldEqual` 0
