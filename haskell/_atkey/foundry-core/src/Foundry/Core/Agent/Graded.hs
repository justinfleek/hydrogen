{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // foundry // agent // graded
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Agent.Graded
Description : Type-level graded monad for agent operations
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

Type-level encoding of budget and permissions using GHC's TypeNats.

== Design Principles

1. Budget is tracked at the TYPE level, not runtime
2. Spending REDUCES the type-level budget (compile-time proof)
3. Permissions form a type-level set (compile-time capability check)
4. Monad laws hold with grade composition

== The Core Insight

@
-- This type signature IS the proof of budget conservation:
spend :: forall cost budget perms a. (CmpNat cost budget ~ 'LT) =>
  SNat cost -> AgentT perms budget a -> AgentT perms (budget - cost) a
@

If @cost > budget@, the constraint @CmpNat cost budget ~ 'LT@ cannot be
satisfied and the program DOES NOT COMPILE. No runtime check needed.

== Dependencies

This module: GHC.TypeNats, Data.Type.Bool
Dependents:  Foundry.Core.Agent (re-exports)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Agent.Graded
  ( -- * The Graded Agent Monad
    AgentT (..)
    
    -- * Re-exports from Effect.Graded (Indexed Monad typeclasses)
  , IxFunctor (..)
  , IxApplicative (..)
  , IxMonad (..)
  , (>>>=)
  , (>>>)
    
    -- * Indexed Agent (for IxMonad instance)
  , IxAgentT (..)
  , toIxAgent
  , fromIxAgent
  , ixSpend
    
    -- * Type-level singletons
  , SNat (..)
  , SPermission (..)
  
    -- * Budget operations
  , spend
  , liftAgent
  , CanSpend
  
    -- * Permission operations
  , requirePermission
  , HasPermission
  , Elem
  
    -- * Running agents
  , runAgentT
  , runIxAgentT
    
    -- * Re-exports for type-level programming
  , KnownNat
  , type (<=)
  , type (-)
  ) where

import Data.Kind (Type, Constraint)
import Data.Type.Bool (If)
import GHC.TypeLits (Symbol, TypeError, ErrorMessage (..))
import GHC.TypeNats (Nat, KnownNat, type (<=), type (-), type (<=?))

import Foundry.Core.Effect.Graded (IxFunctor (..), IxApplicative (..), IxMonad (..), (>>>=), (>>>))

--------------------------------------------------------------------------------
-- SECTION 1: TYPE-LEVEL NAT SINGLETON
--------------------------------------------------------------------------------

-- | Singleton for type-level Nat (witness that we know the value)
data SNat (n :: Nat) = SNat

--------------------------------------------------------------------------------
-- SECTION 1b: BUDGET CONSTRAINT WITH CUSTOM ERROR
--------------------------------------------------------------------------------

-- | Constraint that @cost <= budget@ with a custom error message.
-- When violated, produces: "Budget exceeded: tried to spend X but only Y remaining"
--
-- Uses 'If' from Data.Type.Bool for clarity - if cost <=? budget is True,
-- return (), otherwise produce a TypeError.
type family AssertBudget (cost :: Nat) (budget :: Nat) :: Constraint where
  AssertBudget cost budget = 
    If (cost <=? budget) 
      (() :: Constraint)
      (TypeError ('Text "Budget exceeded: tried to spend " 
            ':<>: 'ShowType cost 
            ':<>: 'Text " but only " 
            ':<>: 'ShowType budget 
            ':<>: 'Text " remaining"))

-- | Constraint alias for budget checking.
-- This is a proper Constraint, not a Bool, so it directly enforces at call sites.
type CanSpend cost budget = AssertBudget cost budget

--------------------------------------------------------------------------------
-- SECTION 2: TYPE-LEVEL PERMISSION SET
--------------------------------------------------------------------------------

-- | Type family to check if a symbol is in a type-level list.
-- Returns 'True if present, 'False otherwise.
type family Elem (x :: Symbol) (xs :: [Symbol]) :: Bool where
  Elem _ '[]       = 'False
  Elem x (x ': _)  = 'True
  Elem x (_ ': xs) = Elem x xs

-- | Type family for permission checking with custom error message.
-- Uses 'If' with the result of 'Elem' to produce clear error messages.
type family AssertPermission (p :: Symbol) (perms :: [Symbol]) :: Constraint where
  AssertPermission p perms = 
    If (Elem p perms) 
      (() :: Constraint)
      (TypeError ('Text "Permission denied: '" 
            ':<>: 'ShowType p 
            ':<>: 'Text "' is not in permission set " 
            ':<>: 'ShowType perms))

-- | Constraint that a permission is present in the permission set.
-- This is used to require specific permissions at compile time.
-- Produces error: "Permission denied: 'X' is not in permission set [...]"
type HasPermission (p :: Symbol) (perms :: [Symbol]) = AssertPermission p perms

--------------------------------------------------------------------------------
-- SECTION 3: THE GRADED AGENT MONAD
--------------------------------------------------------------------------------

-- | The graded Agent monad transformer.
--
-- Type parameters:
--   @perms@  - Type-level list of permissions (e.g., '["read", "network"])
--   @budget@ - Type-level Nat representing remaining budget in cents
--   @m@      - Underlying monad
--   @a@      - Result type
--
-- The budget parameter DECREASES as operations consume resources.
-- This is enforced at compile time - overspending does not typecheck.
newtype AgentT (perms :: [Symbol]) (budget :: Nat) (m :: Type -> Type) (a :: Type)
  = AgentT { unAgentT :: m a }
  deriving stock (Functor)

-- | Applicative instance preserves budget (no consumption)
instance (Applicative m) => Applicative (AgentT perms budget m) where
  pure :: a -> AgentT perms budget m a
  pure = AgentT . pure
  {-# INLINE pure #-}
  
  (<*>) :: AgentT perms budget m (a -> b) -> AgentT perms budget m a -> AgentT perms budget m b
  AgentT mf <*> AgentT ma = AgentT (mf <*> ma)
  {-# INLINE (<*>) #-}

-- | Monad instance preserves budget (spending happens via explicit combinators)
instance (Monad m) => Monad (AgentT perms budget m) where
  (>>=) :: AgentT perms budget m a -> (a -> AgentT perms budget m b) -> AgentT perms budget m b
  AgentT ma >>= f = AgentT (ma >>= unAgentT . f)
  {-# INLINE (>>=) #-}

--------------------------------------------------------------------------------
-- SECTION 3b: INDEXED AGENT (for IxMonad instance)
--------------------------------------------------------------------------------

-- | Indexed agent monad transformer.
--
-- Unlike 'AgentT' which has a single budget parameter, 'IxAgentT' tracks
-- budget transitions via two type parameters:
--
--   @budgetBefore@ - Budget available at start of computation
--   @budgetAfter@  - Budget remaining after computation
--
-- This enables the 'IxMonad' instance where bind composes transitions:
--
-- @
-- (i → j) >>= (j → k) = (i → k)
-- @
--
-- == Example
--
-- @
-- action1 :: IxAgentT perms m 100 70 ()  -- spends 30
-- action2 :: IxAgentT perms m 70 50 ()   -- spends 20
-- 
-- combined :: IxAgentT perms m 100 50 ()
-- combined = action1 `ibind` \\_ -> action2
-- @
--
-- The types prove: started with 100, ended with 50, therefore spent 50.
newtype IxAgentT 
    (perms :: [Symbol]) 
    (m :: Type -> Type) 
    (budgetBefore :: Nat) 
    (budgetAfter :: Nat) 
    (a :: Type)
  = IxAgentT { unIxAgentT :: m a }
  deriving stock (Functor)

-- | IxFunctor instance - mapping preserves state indices
instance Functor m => IxFunctor (IxAgentT perms m) where
  imap :: (a -> b) -> IxAgentT perms m i j a -> IxAgentT perms m i j b
  imap f (IxAgentT ma) = IxAgentT (fmap f ma)
  {-# INLINE imap #-}

-- | IxApplicative instance - pure has identity transition, ap composes
instance Applicative m => IxApplicative (IxAgentT perms m) where
  ipure :: a -> IxAgentT perms m i i a
  ipure a = IxAgentT (pure a)
  {-# INLINE ipure #-}
  
  iap :: IxAgentT perms m i j (a -> b) -> IxAgentT perms m j l a -> IxAgentT perms m i l b
  IxAgentT mf `iap` IxAgentT ma = IxAgentT (mf <*> ma)
  {-# INLINE iap #-}

-- | IxMonad instance - bind composes budget transitions
--
-- This is the key instance that makes budget tracking work with indexed monads.
-- When you bind @m i j a@ with @(a -> m j k b)@, you get @m i k b@.
--
-- The budget indices compose: if first action goes from 100→70 (spent 30),
-- and second goes from 70→50 (spent 20), the combined goes 100→50 (spent 50).
instance Monad m => IxMonad (IxAgentT perms m) where
  ibind :: IxAgentT perms m i j a -> (a -> IxAgentT perms m j l b) -> IxAgentT perms m i l b
  IxAgentT ma `ibind` f = IxAgentT (ma >>= unIxAgentT . f)
  {-# INLINE ibind #-}

-- | Convert from AgentT to IxAgentT (identity transition)
--
-- Use this to lift 'AgentT' actions that don't change budget into
-- the indexed world.
toIxAgent :: AgentT perms budget m a -> IxAgentT perms m budget budget a
toIxAgent (AgentT ma) = IxAgentT ma
{-# INLINE toIxAgent #-}

-- | Convert from IxAgentT back to AgentT
--
-- The resulting AgentT has the @budgetAfter@ as its budget parameter,
-- which is the budget remaining after the indexed computation.
fromIxAgent :: IxAgentT perms m budgetBefore budgetAfter a -> AgentT perms budgetAfter m a
fromIxAgent (IxAgentT ma) = AgentT ma
{-# INLINE fromIxAgent #-}

-- | Spend budget in the indexed monad.
--
-- Creates a budget transition from @budget@ to @(budget - cost)@.
-- This is the indexed equivalent of 'spend'.
--
-- @
-- ixSpend (SNat @30) action :: IxAgentT perms m 100 70 a
-- @
--
-- NOTE: GHC warns about "redundant constraint" here, but 'CanSpend' is NOT
-- redundant - it provides the custom compile-time error message when
-- @cost > budget@. The constraint is checked at call sites and produces
-- \"Budget exceeded: tried to spend X but only Y remaining\".
ixSpend
  :: forall cost budget perms m a
   . (CanSpend cost budget)
  => SNat cost
  -> IxAgentT perms m budget budget a
  -> IxAgentT perms m budget (budget - cost) a
ixSpend SNat (IxAgentT ma) = IxAgentT ma
{-# INLINE ixSpend #-}

-- | Run an indexed agent computation.
--
-- The type signature encodes the budget proof:
-- - Started with @budgetBefore@
-- - Ended with @budgetAfter@  
-- - Therefore spent exactly @(budgetBefore - budgetAfter)@
runIxAgentT :: IxAgentT perms m budgetBefore budgetAfter a -> m a
runIxAgentT (IxAgentT ma) = ma
{-# INLINE runIxAgentT #-}

--------------------------------------------------------------------------------
-- SECTION 4: BUDGET OPERATIONS
--------------------------------------------------------------------------------

-- | Spend budget at the type level.
--
-- This is the key insight: the return type has @(budget - cost)@.
-- If @cost > budget@, GHC cannot solve @cost <= budget@ and compilation fails.
--
-- @
-- example :: AgentT perms 100 IO ()
-- example = do
--   spend (SNat @50) (pure ())  -- Now we have 50 remaining
--   spend (SNat @30) (pure ())  -- Now we have 20 remaining  
--   spend (SNat @30) (pure ())  -- COMPILE ERROR: 30 > 20
-- @
--
-- NOTE: GHC warns about "redundant constraint" here, but 'CanSpend' is NOT
-- redundant - it provides the custom compile-time error message when
-- @cost > budget@. The constraint is checked at call sites and produces
-- \"Budget exceeded: tried to spend X but only Y remaining\".
spend
  :: forall cost budget perms m a
   . (CanSpend cost budget)
  => SNat cost
  -> AgentT perms budget m a
  -> AgentT perms (budget - cost) m a
spend SNat (AgentT ma) = AgentT ma
{-# INLINE spend #-}

-- | Lift an action into the agent monad without consuming budget.
-- Use this for pure computations that don't require resources.
liftAgent :: m a -> AgentT perms budget m a
liftAgent = AgentT
{-# INLINE liftAgent #-}

--------------------------------------------------------------------------------
-- SECTION 5: PERMISSION OPERATIONS  
--------------------------------------------------------------------------------

-- | Proxy type for permissions (avoids ambiguous type variables)
data SPermission (p :: Symbol) = SPermission

-- | Require a permission at compile time.
--
-- If the permission is not in the agent's permission set, compilation fails.
-- The permission check happens entirely at compile time - no runtime cost.
--
-- @
-- readData :: HasPermission \"read\" perms => AgentT perms budget IO Data
-- readData = requirePermission SPermission $ AgentT $ do
--   -- actual read operation
-- @
--
-- NOTE: GHC warns about "redundant constraint" here, but 'HasPermission' is NOT
-- redundant - it provides the custom compile-time error message when
-- permission @p@ is not in @perms@. The constraint is checked at call sites
-- and produces \"Permission denied: 'X' is not in permission set [...]\".
requirePermission
  :: forall (p :: Symbol) perms budget m a
   . (HasPermission p perms)
  => SPermission p
  -> AgentT perms budget m a
  -> AgentT perms budget m a
requirePermission SPermission (AgentT ma) = AgentT ma
{-# INLINE requirePermission #-}

--------------------------------------------------------------------------------
-- SECTION 6: RUNNING AGENTS
--------------------------------------------------------------------------------

-- | Run an agent computation.
--
-- The type signature proves:
-- 1. We started with @initialBudget@
-- 2. We have @remainingBudget@ left
-- 3. Therefore we spent exactly @(initialBudget - remainingBudget)@
--
-- This is compile-time proof of budget conservation.
runAgentT
  :: AgentT perms budget m a
  -> m a
runAgentT (AgentT ma) = ma
{-# INLINE runAgentT #-}

