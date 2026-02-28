{- |
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // foundry // effect // graded
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Module      : Foundry.Core.Effect.Graded
Description : Type-level indexed monad for graded effect tracking
Copyright   : (c) Straylight Software, 2026
License     : BSD-3-Clause

== Indexed Monads (Parameterized Monads)

Standard monads have type @m a@. Indexed monads have type @m i j a@ where:
  - @i@ is the "input" or "pre" state/grade
  - @j@ is the "output" or "post" state/grade
  - @a@ is the result type

This enables tracking state transitions at the type level:

@
-- ireturn doesn't change state: i → i
ireturn :: a -> m i i a

-- ibind composes state transitions: (i → j) >> (j → k) = (i → k)
ibind :: m i j a -> (a -> m j k b) -> m i k b
@

== Application to Budget Tracking

For budget tracking:
  - @i@ = budget before operation
  - @j@ = budget after operation

@
spend50 :: Agent 100 50 ()   -- Starts with 100, ends with 50
spend30 :: Agent 50 20 ()    -- Starts with 50, ends with 20

combined :: Agent 100 20 ()
combined = spend50 `ibind` \_ -> spend30
@

The types prove budget conservation: 100 - 50 - 30 = 20.

== References

- Atkey, R. "Parameterised Notions of Computation" (2009)
- Katsumata, S. "Parametric Effect Monads" POPL 2014

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-}
module Foundry.Core.Effect.Graded
  ( -- * Indexed Monad (Type-Level Grades)
    IxFunctor (..)
  , IxApplicative (..)
  , IxMonad (..)
  
    -- * Indexed Operators
  , (>>>=)
  , (>>>)
  
    -- * Indexed Monad Laws (documentation)
    -- $laws
  ) where

import Data.Kind (Type)

--------------------------------------------------------------------------------
-- SECTION 1: INDEXED FUNCTOR
--------------------------------------------------------------------------------

-- | Indexed functor - functor that preserves state indices.
--
-- Laws:
-- @
-- imap id = id
-- imap (f . g) = imap f . imap g
-- @
class IxFunctor (m :: k -> k -> Type -> Type) where
  -- | Map over the result while preserving state indices
  imap :: (a -> b) -> m i j a -> m i j b

--------------------------------------------------------------------------------
-- SECTION 2: INDEXED APPLICATIVE
--------------------------------------------------------------------------------

-- | Indexed applicative - applicative that composes state transitions.
--
-- Note: Unlike standard Applicative, state indices compose in sequence.
--
-- Laws:
-- @
-- ipure id `iap` v = v
-- ipure (.) `iap` u `iap` v `iap` w = u `iap` (v `iap` w)
-- ipure f `iap` ipure x = ipure (f x)
-- @
class IxFunctor m => IxApplicative (m :: k -> k -> Type -> Type) where
  -- | Lift a pure value with identity state transition
  ipure :: a -> m i i a
  
  -- | Apply function with composed state transitions
  -- (i → j) applied to (j → l) gives (i → l)
  iap :: m i j (a -> b) -> m j l a -> m i l b

--------------------------------------------------------------------------------
-- SECTION 3: INDEXED MONAD
--------------------------------------------------------------------------------

-- | Indexed monad - monad with type-level state/grade tracking.
--
-- This is the foundation for type-level effect tracking. The indices
-- represent "before" and "after" states, which compose via bind.
--
-- Laws:
-- @
-- ireturn a `ibind` f  ≡  f a                        -- Left identity
-- m `ibind` ireturn    ≡  m                          -- Right identity  
-- (m `ibind` f) `ibind` g  ≡  m `ibind` (\\x -> f x `ibind` g)  -- Associativity
-- @
class IxApplicative m => IxMonad (m :: k -> k -> Type -> Type) where
  -- | Lift a pure value (identity state transition)
  ireturn :: a -> m i i a
  ireturn = ipure
  {-# INLINE ireturn #-}
  
  -- | Bind with composed state transitions
  -- If @ma@ goes from @i@ to @j@, and @f@ goes from @j@ to @l@,
  -- then @ma `ibind` f@ goes from @i@ to @l@.
  ibind :: m i j a -> (a -> m j l b) -> m i l b

-- | Flipped bind for do-notation-like chaining
(>>>=) :: IxMonad m => m i j a -> (a -> m j k b) -> m i k b
(>>>=) = ibind
{-# INLINE (>>>=) #-}
infixl 1 >>>=

-- | Sequence, discarding first result
(>>>) :: IxMonad m => m i j a -> m j k b -> m i k b
ma >>> mb = ma `ibind` const mb
{-# INLINE (>>>) #-}
infixl 1 >>>

--------------------------------------------------------------------------------
-- $laws
-- 
-- == Indexed Monad Laws
--
-- The indexed monad must satisfy these laws:
--
-- === Left Identity
-- @ireturn a `ibind` f  ≡  f a@
--
-- Returning a value and immediately binding is the same as applying directly.
--
-- === Right Identity  
-- @m `ibind` ireturn  ≡  m@
--
-- Binding to return is a no-op.
--
-- === Associativity
-- @(m `ibind` f) `ibind` g  ≡  m `ibind` (\\x -> f x `ibind` g)@
--
-- Bind is associative - grouping doesn't matter.
--
-- === State Composition
-- The key property: if @m :: M i j a@ and @f :: a -> M j k b@,
-- then @m `ibind` f :: M i k b@.
--
-- This means state transitions compose: @(i → j) >> (j → k) = (i → k)@.
--------------------------------------------------------------------------------

