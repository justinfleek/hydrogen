-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // schema // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property tests for Schema modules:
-- | - Diff: patch/apply correctness
-- | - Group: hierarchical organization
-- | - Priority: ordering and bounds
-- | - Landauer: entropy-based precision
-- |
-- | Status: Placeholder — tests need implementation matching actual module APIs.
module Test.Schema.Property
  ( schemaPropertyTests
  ) where

import Prelude (Unit, bind, negate, pure, unit, ($), (&&), (<=), (>=), (<>), (==), show, discard, otherwise, (+), (-))

import Data.Array.NonEmpty as NEA
import Hydrogen.Schema.Diff as Diff
import Hydrogen.Schema.Group as Group
import Hydrogen.Schema.Priority as Priority
import Hydrogen.Schema.GPU.Landauer as Landauer
import Test.QuickCheck (Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements)
import Test.Spec (Spec, describe, it)
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
