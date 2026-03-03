{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // Test.Foundry.Core.Effects.Graded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Tests for the Orchard & Petricek graded monad implementation.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Test.Foundry.Core.Effects.Graded
  ( tests
  ) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Hedgehog (Property, property, (===), forAll, evalIO)
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range

import Foundry.Core.Effects.Graded
import Foundry.Core.Effects.Do qualified as F

tests :: TestTree
tests = testGroup "Foundry.Core.Effects.Graded"
  [ testProperty "pure computation has empty grade" prop_pure_grade
  , testProperty "liftNet tags with Net" prop_net_grade
  , testProperty "composition unions grades" prop_compose_grades
  , testProperty "grade accumulates costs" prop_grade_accumulates
  ]

-- | Pure computation should have empty grade tracking
prop_pure_grade :: Property
prop_pure_grade = property $ do
  n <- forAll $ Gen.int (Range.linear 0 1000)
  let comp = F.return n :: FoundryM Pure Int
  (result, grade, _, _) <- evalIO $ runFoundryM comp
  result === n
  ggLatencyMs grade === 0
  ggProviderCalls grade === 0
  ggCacheHits grade === 0

-- | liftNet should produce Net-tagged computation
prop_net_grade :: Property
prop_net_grade = property $ do
  let comp = liftNet (pure 42) :: FoundryM '[ 'Net ] Int
  (result, grade, _, _) <- evalIO $ runFoundryM comp
  result === 42
  -- Grade is still empty because liftNet doesn't add cost, just type tag
  ggLatencyMs grade === 0

-- | Composing computations should union their grades (type-level)
-- At value level, grades combine via Semigroup
prop_compose_grades :: Property
prop_compose_grades = property $ do
  let comp :: FoundryM '[ 'Net, 'Config ] Int
      comp = F.do
        _ <- liftNet (pure ())
        liftConfig (pure 42)
  (result, grade, _, _) <- evalIO $ runFoundryM comp
  result === 42
  -- Grade at value level is combined
  ggLatencyMs grade === 0

-- | Grade should accumulate costs correctly
prop_grade_accumulates :: Property
prop_grade_accumulates = property $ do
  let comp :: FoundryM '[ 'Net ] ()
      comp = F.do
        _ <- withCacheHit (liftNet (pure ()))
        withCacheMiss (liftNet (pure ()))
  (_, grade, _, _) <- evalIO $ runFoundryM comp
  ggCacheHits grade === 1
  ggCacheMisses grade === 1
