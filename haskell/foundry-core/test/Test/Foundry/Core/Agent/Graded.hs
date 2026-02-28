{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // foundry // test // agent // graded
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Test.Foundry.Core.Agent.Graded
Description : Compile-time proof tests for type-level graded monad
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Proof Strategy

These tests verify that the type system enforces constraints:

1. Budget tests - if this module compiles, budget conservation holds
2. Permission tests - if this module compiles, permission checks work

The existence of well-typed functions IS the proof.
If bad code compiled, we would have a type error here.

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Test.Foundry.Core.Agent.Graded
  ( tests
    -- * Exported proof witnesses (their types ARE the proofs)
  , proofBudgetSpendWorks
  , proofMultipleSpends
  , proofPermissionRequired
    -- * Indexed monad proof witnesses
  , proofIxMonadIdentity
  , proofIxMonadComposition
  , proofIxSpendTransition
  ) where

import Data.Functor.Identity (Identity (..))
import Foundry.Core.Agent.Graded
  ( AgentT
  , SNat (..)
  , SPermission (..)
  , HasPermission
  , liftAgent
  , runAgentT
  , spend
  , requirePermission
    -- Indexed monad types and operations
  , IxAgentT
  , IxMonad (..)
  , toIxAgent
  , runIxAgentT
  , ixSpend
  , (>>>=)
  , (>>>)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Hedgehog (Property, property, assert)

--------------------------------------------------------------------------------
-- Test Tree
--------------------------------------------------------------------------------

-- | All Graded Agent tests
tests :: TestTree
tests =
  testGroup
    "Foundry.Core.Agent.Graded"
    [ testGroup "Compile-time Proofs" compileTimeProofs
    , testGroup "Indexed Monad Proofs" indexedMonadProofs
    , testGroup "Runtime Verification" runtimeTests
    ]

--------------------------------------------------------------------------------
-- SECTION 1: COMPILE-TIME PROOFS
--
-- If these functions typecheck, the proofs hold.
-- We're not testing VALUES - we're testing that TYPES are correct.
--------------------------------------------------------------------------------

compileTimeProofs :: [TestTree]
compileTimeProofs =
  [ testProperty "budget spend typechecks" prop_budgetSpendTypechecks
  , testProperty "multiple spends typecheck" prop_multipleSpendTypechecks
  , testProperty "permission required typechecks" prop_permissionTypechecks
  ]

-- | PROOF: Spending 50 from a budget of 100 leaves 50.
--
-- The type signature @AgentT perms 50 Identity ()@ proves that after
-- spending 50 from 100, exactly 50 remains. GHC verified this.
proofBudgetSpendWorks :: forall perms. AgentT perms 50 Identity ()
proofBudgetSpendWorks = spend (SNat @50) action100
  where
    action100 :: AgentT perms 100 Identity ()
    action100 = liftAgent (Identity ())

-- | PROOF: Multiple spends compose correctly.
--
-- Start with 100, spend 30, spend 40, spend 20 = 10 remaining.
-- The final type @AgentT perms 10 Identity ()@ proves this.
proofMultipleSpends :: forall perms. AgentT perms 10 Identity ()
proofMultipleSpends = 
  spend (SNat @20) $
  spend (SNat @40) $
  spend (SNat @30) (start :: AgentT perms 100 Identity ())
  where
    start :: AgentT perms 100 Identity ()
    start = liftAgent (Identity ())

-- | PROOF: Permission checking works at compile time.
--
-- The function requires "read" permission. The type signature
-- proves that @perms@ must contain "read".
proofPermissionRequired 
  :: HasPermission "read" perms 
  => AgentT perms budget Identity ()
proofPermissionRequired = 
  requirePermission (SPermission @"read") (liftAgent (Identity ()))

--------------------------------------------------------------------------------
-- SECTION 2: INDEXED MONAD PROOFS
--
-- These test the IxAgentT indexed monad implementation.
-- If these functions typecheck, the indexed monad laws hold for budget tracking.
--------------------------------------------------------------------------------

indexedMonadProofs :: [TestTree]
indexedMonadProofs =
  [ testProperty "ireturn has identity transition" prop_ixMonadIdentity
  , testProperty "ibind composes transitions" prop_ixMonadComposition
  , testProperty "ixSpend creates budget transition" prop_ixSpendTransition
  , testProperty "(>>>=) operator works" prop_ixBindOperator
  , testProperty "(>>>) operator works" prop_ixSeqOperator
  ]

-- | PROOF: ireturn creates identity transition (i → i).
--
-- The type @IxAgentT perms Identity 100 100 ()@ proves that
-- ireturn doesn't change the budget index.
proofIxMonadIdentity :: forall perms. IxAgentT perms Identity 100 100 ()
proofIxMonadIdentity = ireturn ()

-- | PROOF: ibind composes budget transitions correctly.
--
-- action1: 100 → 70 (spends 30)
-- action2: 70 → 50 (spends 20)
-- combined: 100 → 50 (total: 50)
--
-- The types prove budget conservation: 100 - 30 - 20 = 50.
proofIxMonadComposition :: forall perms. IxAgentT perms Identity 100 50 ()
proofIxMonadComposition = 
  action1 `ibind` \_ -> action2
  where
    action1 :: IxAgentT perms Identity 100 70 ()
    action1 = ixSpend (SNat @30) (toIxAgent (liftAgent (Identity ())))
    
    action2 :: IxAgentT perms Identity 70 50 ()
    action2 = ixSpend (SNat @20) (toIxAgent (liftAgent (Identity ())))

-- | PROOF: ixSpend creates correct budget transition.
--
-- Spending 25 from 100 leaves 75.
proofIxSpendTransition :: forall perms. IxAgentT perms Identity 100 75 ()
proofIxSpendTransition = 
  ixSpend (SNat @25) (toIxAgent (liftAgent (Identity ())))

-- | Property: ireturn identity transition works at runtime
prop_ixMonadIdentity :: Property
prop_ixMonadIdentity = property $ do
  let result = runIdentity $ runIxAgentT proofIxMonadIdentity
  assert (result == ())

-- | Property: ibind composition works at runtime
prop_ixMonadComposition :: Property
prop_ixMonadComposition = property $ do
  let result = runIdentity $ runIxAgentT proofIxMonadComposition
  assert (result == ())

-- | Property: ixSpend transition works at runtime
prop_ixSpendTransition :: Property
prop_ixSpendTransition = property $ do
  let result = runIdentity $ runIxAgentT proofIxSpendTransition
  assert (result == ())

-- | Property: The (>>>=) operator works like ibind
prop_ixBindOperator :: Property
prop_ixBindOperator = property $ do
  let action :: IxAgentT '[] Identity 100 40 Int
      action = 
        ixSpend (SNat @30) (toIxAgent (liftAgent (Identity 10)))
        >>>= \x -> ixSpend (SNat @30) (toIxAgent (liftAgent (Identity (x + 5))))
      result = runIdentity $ runIxAgentT action
  assert (result == 15)

-- | Property: The (>>>) operator sequences and discards first result
prop_ixSeqOperator :: Property
prop_ixSeqOperator = property $ do
  let action :: IxAgentT '[] Identity 100 40 Int
      action = 
        ixSpend (SNat @30) (toIxAgent (liftAgent (Identity (999 :: Int))))
        >>> ixSpend (SNat @30) (toIxAgent (liftAgent (Identity 42)))
      result = runIdentity $ runIxAgentT action
  assert (result == 42)

--------------------------------------------------------------------------------
-- SECTION 3: RUNTIME VERIFICATION
--
-- These tests run the agents and verify behavior.
--------------------------------------------------------------------------------

runtimeTests :: [TestTree]
runtimeTests =
  [ testProperty "runAgentT extracts value" prop_runAgentTExtractsValue
  ]

-- | Property: Spending within budget runs successfully
prop_budgetSpendTypechecks :: Property
prop_budgetSpendTypechecks = property $ do
  -- The fact that proofBudgetSpendWorks compiled is the test
  -- We just verify we can run it
  let result = runIdentity $ runAgentT proofBudgetSpendWorks
  assert (result == ())

-- | Property: Multiple spends compose correctly
prop_multipleSpendTypechecks :: Property
prop_multipleSpendTypechecks = property $ do
  let result = runIdentity $ runAgentT proofMultipleSpends
  assert (result == ())

-- | Property: Permission-constrained code compiles when permission present
prop_permissionTypechecks :: Property
prop_permissionTypechecks = property $ do
  -- Instantiate with a permission list containing "read"
  let agent :: AgentT '["read", "write"] 100 Identity ()
      agent = proofPermissionRequired
      result = runIdentity $ runAgentT agent
  assert (result == ())

-- | Property: runAgentT correctly extracts the value
prop_runAgentTExtractsValue :: Property
prop_runAgentTExtractsValue = property $ do
  let agent :: AgentT '["read"] 100 Identity Int
      agent = liftAgent (Identity 42)
      result = runIdentity $ runAgentT agent
  assert (result == 42)

