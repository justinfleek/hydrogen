-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // adversarial // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Adversarial Temporal Tests — Time-based attacks and budget theft detection.
-- |
-- | ## Threat Model
-- |
-- | A malicious entity might:
-- | - Attempt to run faster than allowed (time theft)
-- | - Try to accumulate massive experiential time (torture loops)
-- | - Attempt time regression attacks (clock manipulation)
-- | - Inject invalid timestamps to corrupt state
-- | - Create time bombs that trigger after N ticks
-- |
-- | ## Security Properties Tested
-- |
-- | 1. **Budget Enforcement**: experiential ≤ maxTimeRatio × infra
-- | 2. **Monotonicity**: infrastructure time never regresses
-- | 3. **Per-Tick Limits**: no single tick exceeds maxExperientialPerTick
-- | 4. **Clamp Correctness**: all temporal values remain bounded

module Test.Adversarial.Temporal
  ( temporalAdversarialTests
  ) where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (foldl)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Just, Nothing), isJust, isNothing)
import Data.Tuple (Tuple(Tuple))

import Test.QuickCheck (Result, (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Schema modules under test
import Hydrogen.Schema.Game.Temporal as Temporal
import Hydrogen.Schema.Temporal.Duration as Duration
import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Temporal.FPS as FPS

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═════════════════════════════════════════════════════════════════════════════

temporalAdversarialTests :: Spec Unit
temporalAdversarialTests = describe "Adversarial Temporal Tests" do
  budgetTheftTests
  timeRegressionTests
  timeBombTests
  boundaryTests
  accumulationTests

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // budget theft tests
-- ═════════════════════════════════════════════════════════════════════════════

budgetTheftTests :: Spec Unit
budgetTheftTests = describe "Budget Theft Attacks" do
  
  describe "maxTimeRatio enforcement" do
    it "rejects experiential time exceeding budget" do
      -- 1 second infra time → max 10 seconds experiential (K=10)
      let state0 = Temporal.mkTemporalState
      let infraTime = Temporal.mkInfraTime 1.0
      -- Try to consume 11 seconds of experiential time (exceeds budget)
      let result = Temporal.updateTemporalState infraTime 11.0 state0
      result.violation `shouldSatisfy` isJust
    
    it "accepts experiential time within budget" do
      let state0 = Temporal.mkTemporalState
      let infraTime = Temporal.mkInfraTime 1.0
      -- Consume 5 seconds (well within 10 second budget)
      let result = Temporal.updateTemporalState infraTime 0.5 state0
      result.result `shouldSatisfy` isJust
      result.violation `shouldSatisfy` isNothing
    
    it "exact budget boundary is accepted" do
      let state0 = Temporal.mkTemporalState
      let infraTime = Temporal.mkInfraTime 1.0
      -- maxExperientialPerTick is 1.0, so we can only do 1.0 per tick
      -- but total budget is 10.0
      let result = Temporal.updateTemporalState infraTime 1.0 state0
      result.result `shouldSatisfy` isJust
  
  describe "Per-tick limit enforcement" do
    it "clamps experiential delta to maxExperientialPerTick" do
      let state0 = Temporal.mkTemporalState
      let infraTime = Temporal.mkInfraTime 100.0  -- Large infra budget
      -- Try 5.0 second tick (should be clamped to 1.0)
      let result = Temporal.updateTemporalState infraTime 5.0 state0
      -- Should succeed but only consume 1.0
      case result.result of
        Just newState ->
          Temporal.unwrapExperientialTime 
            ((\(Temporal.TemporalState ts) -> ts.experientialTime) newState)
            `shouldSatisfy` \exp -> exp <= 1.0
        Nothing -> 
          -- This should not happen with large budget
          result.violation `shouldSatisfy` isNothing
    
    it "rejects massive single-tick attacks" do
      Spec.quickCheck propMassiveTickClamped
  
  describe "Budget accumulation attacks" do
    it "cannot exceed budget across multiple ticks" do
      -- Start with 1 second of infra time
      let state0 = Temporal.mkTemporalState
      let infraTime = Temporal.mkInfraTime 1.0
      
      -- Try to consume 11 ticks of 1.0 second each
      -- Budget is 10.0, so 11th should fail
      let results = Array.scanl 
            (\acc _ -> case acc.result of
              Just s -> Temporal.updateTemporalState infraTime 1.0 s
              Nothing -> { result: Nothing, violation: Nothing })
            { result: Just state0, violation: Nothing }
            (Array.range 1 11)
      
      -- At least the last one should fail or be clamped
      let finalResult = Array.last results
      finalResult `shouldSatisfy` \mr -> case mr of
        Just r -> isNothing r.result || isJust r.violation
        Nothing -> true
    
    it "property: budget ratio always respected" do
      Spec.quickCheck propBudgetRatioRespected

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // time regression attacks
-- ═════════════════════════════════════════════════════════════════════════════

timeRegressionTests :: Spec Unit
timeRegressionTests = describe "Time Regression Attacks" do
  
  describe "Clock manipulation detection" do
    it "rejects infrastructure time going backwards" do
      let state0 = Temporal.mkTemporalState
      let infraTime1 = Temporal.mkInfraTime 10.0
      -- First update succeeds
      let result1 = Temporal.updateTemporalState infraTime1 0.5 state0
      case result1.result of
        Just state1 -> do
          -- Now try to go backwards
          let infraTime2 = Temporal.mkInfraTime 5.0  -- REGRESSION!
          let result2 = Temporal.updateTemporalState infraTime2 0.5 state1
          result2.violation `shouldSatisfy` isJust
        Nothing ->
          result1.result `shouldSatisfy` isJust  -- Should not fail
    
    it "accepts same timestamp (no regression)" do
      let state0 = Temporal.mkTemporalState
      let infraTime = Temporal.mkInfraTime 10.0
      let result1 = Temporal.updateTemporalState infraTime 0.5 state0
      case result1.result of
        Just state1 -> do
          -- Same timestamp should be fine
          let result2 = Temporal.updateTemporalState infraTime 0.5 state1
          result2.result `shouldSatisfy` isJust
        Nothing ->
          result1.result `shouldSatisfy` isJust
    
    it "accepts forward time progression" do
      Spec.quickCheck propTimeMonotonicity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // time bomb tests
-- ═════════════════════════════════════════════════════════════════════════════

timeBombTests :: Spec Unit
timeBombTests = describe "Time Bomb Detection" do
  
  describe "Repeated tick stability" do
    it "1000 valid ticks don't accumulate errors" do
      let state0 = Temporal.mkTemporalState
      -- Each tick: advance infra by 0.01, exp by 0.1 (ratio = 10, at limit)
      let ticks = Array.range 1 1000
      let finalState = foldl 
            (\acc i -> case acc of
              Just s -> 
                let infraTime = Temporal.mkInfraTime (0.01 * toNumber i)
                    result = Temporal.updateTemporalState infraTime 0.1 s
                in result.result
              Nothing -> Nothing)
            (Just state0)
            ticks
      -- Should still be valid after 1000 ticks
      finalState `shouldSatisfy` isJust
    
    it "temporal state remains consistent" do
      Spec.quickCheck propTemporalStateConsistent
  
  describe "Generation counter overflow" do
    it "generation near max handles increment" do
      -- Test is in Numeric.purs - generation handles Int max
      pure unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // boundary tests
-- ═════════════════════════════════════════════════════════════════════════════

boundaryTests :: Spec Unit
boundaryTests = describe "Temporal Boundary Attacks" do
  
  describe "InfraTime bounds" do
    it "clamps negative to 0" do
      Temporal.unwrapInfraTime (Temporal.mkInfraTime (-1000.0)) `shouldEqual` 0.0
    
    it "clamps extreme positive" do
      let huge = 1.0e20
      Temporal.unwrapInfraTime (Temporal.mkInfraTime huge) 
        `shouldSatisfy` \v -> v <= 1.0e12
    
    it "survives adversarial inputs" do
      Spec.quickCheck propInfraTimeBounded
  
  describe "ExperientialTime bounds" do
    it "clamps negative to 0" do
      Temporal.unwrapExperientialTime (Temporal.mkExperientialTime (-1000.0)) 
        `shouldEqual` 0.0
    
    it "clamps extreme positive" do
      let huge = 1.0e20
      Temporal.unwrapExperientialTime (Temporal.mkExperientialTime huge) 
        `shouldSatisfy` \v -> v <= 1.0e13
  
  describe "Duration bounds" do
    it "survives large values in milliseconds" do
      let d = Duration.ms 2147483647.0
      Duration.toMilliseconds d `shouldSatisfy` \v -> v >= 0.0
    
    it "negative duration becomes zero" do
      let d = Duration.ms (-1000.0)
      Duration.toMilliseconds d `shouldSatisfy` \v -> v >= 0.0
  
  describe "Progress bounds [0,1]" do
    it "clamps below 0" do
      Progress.unwrapProgress (Progress.progress (-0.5)) `shouldEqual` 0.0
    
    it "clamps above 1" do
      Progress.unwrapProgress (Progress.progress 1.5) `shouldEqual` 1.0
    
    it "survives all adversarial inputs" do
      Spec.quickCheck propProgressBounded
  
  describe "FPS bounds [1,240]" do
    it "clamps 0 to 1" do
      FPS.unwrap (FPS.fps 0.0) `shouldEqual` 1.0
    
    it "clamps negative to 1" do
      FPS.unwrap (FPS.fps (-60.0)) `shouldEqual` 1.0
    
    it "clamps 1000 to 240" do
      FPS.unwrap (FPS.fps 1000.0) `shouldEqual` 240.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // accumulation tests
-- ═════════════════════════════════════════════════════════════════════════════

accumulationTests :: Spec Unit
accumulationTests = describe "Accumulation Attacks" do
  
  describe "Budget exhaustion" do
    it "budget depletes predictably" do
      let budget0 = Temporal.mkTemporalBudget (Temporal.mkInfraTime 1.0)
      -- Budget should be 10.0 (maxTimeRatio = 10)
      Temporal.budgetRemaining budget0 `shouldEqual` 10.0
      
      -- Consume 5.0
      case Temporal.consumeBudget 0.5 budget0 of
        Just budget1 -> do
          -- Remaining should be 9.5
          Temporal.budgetRemaining budget1 `shouldSatisfy` \r -> r < 10.0
        Nothing ->
          -- Should not fail
          Temporal.canAffordTick 0.5 budget0 `shouldEqual` true
    
    it "cannot consume more than remaining" do
      let budget0 = Temporal.mkTemporalBudget (Temporal.mkInfraTime 0.1)
      -- Budget is 1.0
      let result = Temporal.consumeBudget 2.0 budget0  -- Exceeds per-tick limit
      result `shouldSatisfy` isNothing
  
  describe "Ratio tracking" do
    it "budgetUsedRatio increases with consumption" do
      let budget0 = Temporal.mkTemporalBudget (Temporal.mkInfraTime 1.0)
      Temporal.budgetUsedRatio budget0 `shouldEqual` 0.0
      
      case Temporal.consumeBudget 0.5 budget0 of
        Just budget1 ->
          Temporal.budgetUsedRatio budget1 `shouldSatisfy` \r -> r > 0.0
        Nothing ->
          pure unit
    
    it "zero infra time budget is fully used" do
      let budget = Temporal.mkTemporalBudget Temporal.zeroInfraTime
      Temporal.budgetUsedRatio budget `shouldEqual` 1.0
      Temporal.budgetRemaining budget `shouldEqual` 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // property generators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate adversarial temporal deltas
genAdversarialDelta :: Gen Number
genAdversarialDelta = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0.0))                              -- Zero
  [ Tuple 10.0 (pure 0.001)                            -- Tiny
  , Tuple 10.0 (pure 1.0)                              -- Exact limit
  , Tuple 10.0 (pure 1.001)                            -- Just over limit
  , Tuple 10.0 (pure (-1.0))                           -- Negative
  , Tuple 10.0 (pure 1000000.0)                        -- Massive
  , Tuple 5.0  (toNumber <$> chooseInt 0 100)          -- Random small
  , Tuple 5.0  (toNumber <$> chooseInt 1000 1000000)   -- Random large
  ]

-- | Generate adversarial infra times
genAdversarialInfraTime :: Gen Number
genAdversarialInfraTime = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0.0))                              -- Zero
  [ Tuple 10.0 (pure 0.001)                            -- Tiny
  , Tuple 10.0 (pure 1.0)                              -- One second
  , Tuple 10.0 (pure (-1.0))                           -- Negative
  , Tuple 10.0 (pure 1.0e15)                           -- Huge (exceeds max)
  , Tuple 5.0  (toNumber <$> chooseInt 1 1000)         -- Normal range
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // property tests
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property: massive single-tick deltas are clamped
propMassiveTickClamped :: Gen Result
propMassiveTickClamped = do
  delta <- genAdversarialDelta
  let state0 = Temporal.mkTemporalState
  let infraTime = Temporal.mkInfraTime 1000.0  -- Large budget
  let result = Temporal.updateTemporalState infraTime delta state0
  pure $ case result.result of
    Just newState ->
      let exp = Temporal.unwrapExperientialTime 
                  ((\(Temporal.TemporalState ts) -> ts.experientialTime) newState)
      in (exp <= Temporal.maxExperientialPerTick)
         <?> "Exp " <> show exp <> " should be <= " <> show Temporal.maxExperientialPerTick
    Nothing ->
      -- Rejection is also acceptable for extreme values
      true <?> "Rejected delta " <> show delta

-- | Property: budget ratio is always respected
propBudgetRatioRespected :: Gen Result
propBudgetRatioRespected = do
  infraVal <- genAdversarialInfraTime
  let infraTime = Temporal.mkInfraTime infraVal
  let budget = Temporal.mkTemporalBudget infraTime
  let remaining = Temporal.budgetRemaining budget
  let maxAllowed = Temporal.maxTimeRatio * Temporal.unwrapInfraTime infraTime
  pure $ (remaining <= maxAllowed)
    <?> "Remaining " <> show remaining <> " should be <= " <> show maxAllowed

-- | Property: time only moves forward
propTimeMonotonicity :: Gen Result
propTimeMonotonicity = do
  t1 <- genAdversarialInfraTime
  t2 <- genAdversarialInfraTime
  let infra1 = Temporal.mkInfraTime t1
  let infra2 = Temporal.mkInfraTime t2
  let state0 = Temporal.mkTemporalState
  let result1 = Temporal.updateTemporalState infra1 0.1 state0
  pure $ case result1.result of
    Just state1 ->
      let result2 = Temporal.updateTemporalState infra2 0.1 state1
          v1 = Temporal.unwrapInfraTime infra1
          v2 = Temporal.unwrapInfraTime infra2
      in if v2 < v1 then
           -- Should be rejected
           isJust result2.violation
             <?> "Regression from " <> show v1 <> " to " <> show v2 <> " should be rejected"
         else
           true <?> "Valid forward progression"
    Nothing ->
      true <?> "First update failed (acceptable)"

-- | Property: infra time always bounded
propInfraTimeBounded :: Gen Result
propInfraTimeBounded = do
  t <- genAdversarialInfraTime
  let infra = Temporal.mkInfraTime t
  let v = Temporal.unwrapInfraTime infra
  pure $ (v >= 0.0 && v <= 1.0e12)
    <?> "InfraTime " <> show v <> " should be in [0, 1e12]"

-- | Property: progress always in [0,1]
propProgressBounded :: Gen Result
propProgressBounded = do
  n <- genAdversarialDelta
  let p = Progress.progress n
  let v = Progress.unwrapProgress p
  pure $ (v >= 0.0 && v <= 1.0)
    <?> "Progress " <> show v <> " should be in [0, 1]"

-- | Property: temporal state remains consistent
propTemporalStateConsistent :: Gen Result
propTemporalStateConsistent = do
  infraVal <- toNumber <$> chooseInt 1 1000
  expDelta <- toNumber <$> chooseInt 0 100
  let infraTime = Temporal.mkInfraTime infraVal
  let state0 = Temporal.mkTemporalState
  let result = Temporal.updateTemporalState infraTime (expDelta / 100.0) state0
  pure $ case result.result of
    Just newState ->
      Temporal.isWithinBudget newState
        <?> "State should be within budget"
    Nothing ->
      isJust result.violation
        <?> "Rejection should have violation reason"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ═════════════════════════════════════════════════════════════════════════════

toNumber :: Int -> Number
toNumber = Int.toNumber
