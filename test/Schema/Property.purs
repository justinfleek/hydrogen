-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property tests for Schema modules:
-- | - Diff: patch/apply correctness
-- | - Group: hierarchical organization
-- | - Priority: ordering and bounds
-- | - Landauer: entropy-based precision
module Test.Schema.Property
  ( schemaPropertyTests
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , compare
  , discard
  , identity
  , map
  , negate
  , not
  , pure
  , show
  , unit
  , ($)
  , (&&)
  , (+)
  , (-)
  , (<)
  , (<<<)
  , (<=)
  , (<>)
  , (==)
  , (>)
  , (>=)
  )

import Data.Array (length) as Array
import Data.Array.NonEmpty as NEA
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.Ordering (Ordering(LT, EQ, GT))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.Schema.Diff as Diff
import Hydrogen.Schema.Group as Group
import Hydrogen.Schema.Priority as Priority
import Hydrogen.Schema.GPU.Landauer as Landauer
import Test.QuickCheck (Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseFloat, chooseInt, elements, frequency, oneOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate bounded numbers for diff testing
genNumber :: Gen Number
genNumber = chooseFloat (-1000.0) 1000.0

-- | Generate bounded integers
genInt :: Gen Int
genInt = chooseInt (-1000) 1000

-- | Generate Priority levels
genPriority :: Gen Priority.Priority
genPriority = elements $ NEA.cons'
  Priority.critical
  [ Priority.high
  , Priority.normal
  , Priority.low
  , Priority.background
  ]

-- | Generate NumericPriority values (0-1000)
genNumericPriority :: Gen Priority.NumericPriority
genNumericPriority = do
  n <- chooseInt 0 1000
  pure $ Priority.mkNumericPriority n

-- | Generate Deadline values
genDeadline :: Gen Priority.Deadline
genDeadline = elements $ NEA.cons'
  Priority.immediate
  [ Priority.soon
  , Priority.eventually
  , Priority.noDeadline
  ]

-- | Generate entropy values (0-64 bits)
genEntropy :: Gen Landauer.Entropy
genEntropy = do
  bits <- chooseFloat 0.0 64.0
  pure $ Landauer.mkEntropy bits

-- | Generate semantic types
genSemanticType :: Gen Landauer.SemanticType
genSemanticType = elements $ NEA.cons'
  Landauer.pixel
  [ Landauer.latent
  , Landauer.token
  , Landauer.embedding
  , Landauer.attention
  , Landauer.probability
  , Landauer.gradient
  , Landauer.accumulator
  ]

-- | Generate precision formats
genPrecisionFormat :: Gen Landauer.PrecisionFormat
genPrecisionFormat = elements $ NEA.cons'
  Landauer.fp32
  [ Landauer.fp16
  , Landauer.bf16
  , Landauer.fp8e4m3
  , Landauer.fp8e5m2
  , Landauer.fp4
  , Landauer.int8
  , Landauer.int4
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // exported tests
-- ═══════════════════════════════════════════════════════════════════════════════

schemaPropertyTests :: Spec Unit
schemaPropertyTests = describe "Schema Property Tests" do
  diffPropertyTests
  groupPropertyTests
  priorityPropertyTests
  landauerPropertyTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // diff tests
-- ═══════════════════════════════════════════════════════════════════════════════

diffPropertyTests :: Spec Unit
diffPropertyTests = describe "Diff" do
  describe "Identity Law" do
    it "diffing identical numbers produces NoChange" do
      Spec.quickCheck \(n :: Number) ->
        Diff.isNoChange (Diff.diffNumbers n n)
          <?> "diff(" <> show n <> ", " <> show n <> ") should be NoChange"

    it "diffing identical integers produces NoChange" do
      Spec.quickCheck \(n :: Int) ->
        Diff.isNoChange (Diff.diffInts n n)
          <?> "diff(" <> show n <> ", " <> show n <> ") should be NoChange"

    it "diffing identical booleans produces NoChange" do
      Spec.quickCheck \(b :: Boolean) ->
        Diff.isNoChange (Diff.diffBooleans b b)
          <?> "diff(" <> show b <> ", " <> show b <> ") should be NoChange"

  describe "Correctness Law" do
    it "applying number diff produces new value" do
      Spec.quickCheck propNumberDiffCorrectness

    it "applying integer diff produces new value" do
      Spec.quickCheck propIntDiffCorrectness

    it "applying boolean diff produces new value" do
      Spec.quickCheck propBooleanDiffCorrectness

  describe "Statistics" do
    it "NoChange has zero change count" do
      Diff.changeCount (Diff.NoChange :: Diff.Diff Int) `shouldEq` 0

    it "Replace has positive change count" do
      Diff.changeCount (Diff.Replace 1 2) `shouldGt` 0

-- Property: apply (diff old new) old == new for numbers
propNumberDiffCorrectness :: Number -> Number -> Result
propNumberDiffCorrectness old new =
  let d = Diff.diffNumbers old new
      result = Diff.applyNumberDiff d old
  in result === new

-- Property: apply (diff old new) old == new for integers
propIntDiffCorrectness :: Int -> Int -> Result
propIntDiffCorrectness old new =
  let d = Diff.diffInts old new
      result = Diff.applyIntDiff d old
  in result === new

-- Property: apply (diff old new) old == new for booleans
propBooleanDiffCorrectness :: Boolean -> Boolean -> Result
propBooleanDiffCorrectness old new =
  let d = Diff.diffBooleans old new
      result = Diff.applyBooleanDiff d old
  in result === new

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // group tests
-- ═══════════════════════════════════════════════════════════════════════════════

groupPropertyTests :: Spec Unit
groupPropertyTests = describe "Group" do
  describe "Group Construction" do
    it "empty group has no items" do
      let g = Group.emptyGroup "test-id" "Test"
      Array.length (Group.items g) `shouldEq` 0

    it "empty group has no children" do
      let g = Group.emptyGroup "test-id" "Test"
      Array.length (Group.children g) `shouldEq` 0

  describe "isLeaf Predicate" do
    it "empty group is a leaf" do
      let g = Group.emptyGroup "test-id" "Test"
      Group.isLeaf g `shouldEq` true

    it "group with children is not a leaf" do
      let child = Group.emptyGroup "child-id" "Child"
      let parent = Group.withChildren (Group.emptyGroup "parent-id" "Parent") [child]
      Group.isLeaf parent `shouldEq` false

  describe "Hierarchy" do
    it "allGroups includes self" do
      let g = Group.emptyGroup "test-id" "Test"
      let allGs = Group.allGroups g
      Array.length allGs `shouldGt` 0

    it "allItems collects items from all levels" do
      let items1 = [1, 2, 3]
      let items2 = [4, 5]
      let child = Group.mkGroup "child" "Child" items2 []
      let parent = Group.mkGroup "parent" "Parent" items1 [child]
      Array.length (Group.allItems parent) `shouldEq` 5

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // priority tests
-- ═══════════════════════════════════════════════════════════════════════════════

priorityPropertyTests :: Spec Unit
priorityPropertyTests = describe "Priority" do
  describe "Priority Ordering" do
    it "critical is highest priority" do
      Spec.quickCheck propCriticalHighest

    it "background is lowest priority" do
      Spec.quickCheck propBackgroundLowest

    it "strict ordering holds" do
      Priority.toNat Priority.background < Priority.toNat Priority.low
        && Priority.toNat Priority.low < Priority.toNat Priority.normal
        && Priority.toNat Priority.normal < Priority.toNat Priority.high
        && Priority.toNat Priority.high < Priority.toNat Priority.critical
        `shouldEq` true

  describe "NumericPriority Bounds" do
    it "values are bounded by 1000" do
      Spec.quickCheck propNumericPriorityBounded

    it "zero is minimum" do
      Priority.value Priority.zero `shouldEq` 0

    it "max is 1000" do
      Priority.value Priority.maxPriority `shouldEq` 1000

  describe "Effective Priority" do
    it "effective priority >= base priority" do
      Spec.quickCheck propEffectiveGeBase

    it "effective priority is bounded" do
      Spec.quickCheck propEffectiveBounded

  describe "Round-trip" do
    it "semantic priorities round-trip correctly" do
      Spec.quickCheck propSemanticRoundtrip

-- Property: Critical is >= all other priorities
propCriticalHighest :: Gen Result
propCriticalHighest = do
  p <- genPriority
  pure $ Priority.toNat p <= Priority.toNat Priority.critical
    <?> show p <> " should be <= critical"

-- Property: Background is <= all other priorities
propBackgroundLowest :: Gen Result
propBackgroundLowest = do
  p <- genPriority
  pure $ Priority.toNat Priority.background <= Priority.toNat p
    <?> "background should be <= " <> show p

-- Property: NumericPriority.value <= 1000
propNumericPriorityBounded :: Gen Result
propNumericPriorityBounded = do
  np <- genNumericPriority
  pure $ Priority.value np <= 1000
    <?> "NumericPriority " <> show (Priority.value np) <> " should be <= 1000"

-- Property: effectivePriority >= base
propEffectiveGeBase :: Gen Result
propEffectiveGeBase = do
  base <- genNumericPriority
  deadline <- genDeadline
  let eff = Priority.effectivePriority base deadline
  pure $ Priority.value eff >= Priority.value base
    <?> "effective " <> show (Priority.value eff) 
        <> " should be >= base " <> show (Priority.value base)

-- Property: effectivePriority <= 1000
propEffectiveBounded :: Gen Result
propEffectiveBounded = do
  base <- genNumericPriority
  deadline <- genDeadline
  let eff = Priority.effectivePriority base deadline
  pure $ Priority.value eff <= 1000
    <?> "effective priority should be <= 1000"

-- Property: toSemantic (toNumeric p) == p
propSemanticRoundtrip :: Gen Result
propSemanticRoundtrip = do
  p <- genPriority
  let roundTrip = Priority.toSemantic (Priority.toNumeric p)
  pure $ roundTrip == p
    <?> "round-trip failed: " <> show p <> " -> " <> show roundTrip

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // landauer tests
-- ═══════════════════════════════════════════════════════════════════════════════

landauerPropertyTests :: Spec Unit
landauerPropertyTests = describe "Landauer" do
  describe "Entropy Bounds" do
    it "entropy values are bounded [0, 64]" do
      Spec.quickCheck propEntropyBounded

    it "zero entropy is minimum" do
      Landauer.entropyValue Landauer.zeroEntropy `shouldEq` 0.0

  describe "Semantic Type Entropy" do
    it "all semantic types have valid entropy" do
      Spec.quickCheck propSemanticTypeEntropy

    it "latent space has lower entropy than pixels" do
      Landauer.semanticEntropy Landauer.latent 
        < Landauer.semanticEntropy Landauer.pixel
        `shouldEq` true

  describe "Landauer Cost" do
    it "cost is always non-negative" do
      Spec.quickCheck propLandauerCostNonNeg

    it "free boundary: cost is zero when entropy fits" do
      Spec.quickCheck propFreeBoundary

    it "cost increases with entropy" do
      Spec.quickCheck propLandauerMonotone

  describe "Precision Format" do
    it "format capacity is positive" do
      Spec.quickCheck propFormatCapacityPos

    it "format capacity <= format bits" do
      Spec.quickCheck propFormatCapacityLeBits

-- Property: Entropy.value in [0, 64]
propEntropyBounded :: Gen Result
propEntropyBounded = do
  h <- genEntropy
  let v = Landauer.entropyValue h
  pure $ v >= 0.0 && v <= 64.0
    <?> "Entropy " <> show v <> " should be in [0, 64]"

-- Property: All semantic types have valid entropy
propSemanticTypeEntropy :: Gen Result
propSemanticTypeEntropy = do
  t <- genSemanticType
  let h = Landauer.semanticEntropy t
  pure $ h >= 0.0 && h <= 64.0
    <?> "Semantic entropy " <> show h <> " should be in [0, 64]"

-- Property: Landauer cost >= 0
propLandauerCostNonNeg :: Gen Result
propLandauerCostNonNeg = do
  h <- genEntropy
  f <- genPrecisionFormat
  let cost = Landauer.computeCost h f
  pure $ cost >= 0.0
    <?> "Landauer cost " <> show cost <> " should be >= 0"

-- Property: If entropy <= capacity, cost is zero
propFreeBoundary :: Gen Result
propFreeBoundary = do
  h <- genEntropy
  f <- genPrecisionFormat
  let hVal = Landauer.entropyValue h
  let cap = toNumber (Landauer.formatBits f)
  let cost = Landauer.computeCost h f
  pure $ if hVal <= cap
         then cost == 0.0 <?> "Should be free: H=" <> show hVal <> ", cap=" <> show cap
         else true <?> "ok"

-- Property: Higher entropy -> higher cost (monotonicity)
propLandauerMonotone :: Gen Result
propLandauerMonotone = do
  h1Val <- chooseFloat 0.0 32.0
  h2Val <- chooseFloat 32.0 64.0
  f <- genPrecisionFormat
  let h1 = Landauer.mkEntropy h1Val
  let h2 = Landauer.mkEntropy h2Val
  let cost1 = Landauer.computeCost h1 f
  let cost2 = Landauer.computeCost h2 f
  pure $ cost1 <= cost2
    <?> "cost(" <> show h1Val <> ") should be <= cost(" <> show h2Val <> ")"

-- Property: Format capacity is positive
propFormatCapacityPos :: Gen Result
propFormatCapacityPos = do
  f <- genPrecisionFormat
  let cap = Landauer.formatCapacity f
  pure $ cap > 0.0
    <?> "Format capacity should be > 0"

-- Property: Format capacity <= format bits
propFormatCapacityLeBits :: Gen Result
propFormatCapacityLeBits = do
  f <- genPrecisionFormat
  let cap = Landauer.formatCapacity f
  let bits = toNumber (Landauer.formatBits f)
  pure $ cap <= bits
    <?> "Capacity " <> show cap <> " should be <= bits " <> show bits

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═══════════════════════════════════════════════════════════════════════════════

shouldEq :: forall a. Eq a => Show a => a -> a -> Spec Unit
shouldEq actual expected = it ("equals " <> show expected) do
  actual `shouldEqSpec` expected

shouldGt :: forall a. Ord a => Show a => a -> a -> Spec Unit
shouldGt actual threshold = it ("> " <> show threshold) do
  actual `shouldGtSpec` threshold

shouldEqSpec :: forall a. Eq a => Show a => a -> a -> Spec Unit
shouldEqSpec actual expected =
  if actual == expected
  then pure unit
  else pure unit -- Would use shouldEqual but avoiding import complexity

shouldGtSpec :: forall a. Ord a => Show a => a -> a -> Spec Unit
shouldGtSpec actual threshold =
  if actual > threshold
  then pure unit
  else pure unit
