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

import Prelude (Unit, bind, negate, pure, unit, ($), (&&), (<=), (>=), (<>), (==), show, discard)

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
