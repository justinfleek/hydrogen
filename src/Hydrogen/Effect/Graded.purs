-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // Effects.Graded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--     "The sky above the port was the color of television, tuned to a dead
--      channel."
--
--                                                              — Neuromancer
--
-- Graded monad for Hydrogen operations, built on Orchard & Petricek's
-- effect-monad pattern.
--
-- The grade parameter is a type-level sorted set of GradeLabel atoms
-- from Hydrogen.Effect.Grade. Composition unions the sets:
--
--     f : HydrogenM '[Net] a
--     g : HydrogenM '[Auth] b
--     f >>= \_ -> g : HydrogenM '[Net, Auth] b    -- via Union
--
-- Runtime tracking (latency, tokens, provenance, coeffects) is still
-- accumulated at the value level — the type-level grade is a *static
-- upper bound* on what effects are permitted, while the value-level
-- data records what actually happened.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Effect.Graded
  ( -- * Graded Monad (type-level indexed)
    HydrogenM(HydrogenM)
  , runHydrogenM
  , runHydrogenMPure

  -- * Value-level Grade (cost tracking)
  , HydrogenGrade
  , emptyGrade
  , combineGrades

  -- * Value-level CoEffect (resource tracking)
  , HydrogenCoEffect
  , emptyCoEffect

  -- * Primitive effect operations (each tags the type-level grade)
  , liftPure
  , liftNet
  , liftAuth
  , liftConfig
  , liftLog
  , liftCrypto
  , liftAff

  -- * Re-exports for grade construction
  , module Hydrogen.Effect.Grade
  ) where

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // imports
-- ════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , pure
  , bind
  , (<>)
  , (+)
  , ($)
  , (>>=)
  )

import Data.Tuple (Tuple(Tuple))
import Effect.Aff (Aff)
import Type.Data.List (type (:>), List', Nil')

import Hydrogen.Effect.Grade
  ( GradeLabel
  , Net
  , Auth
  , Config
  , Log
  , Crypto
  , Fs
  , class Union
  , Pure
  , Full
  )
import Hydrogen.Effect.Class as Effect

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // hydrogen grade
-- ════════════════════════════════════════════════════════════════════════════

-- | Value-level cost accumulator. Tracks what actually happened at runtime.
-- This is orthogonal to the type-level grade — the grade says what's
-- *permitted*, this records what *occurred*.
type HydrogenGrade =
  { latencyMs     :: Int
  , inputTokens   :: Int
  , outputTokens  :: Int
  , providerCalls :: Int
  , retries       :: Int
  , cacheHits     :: Int
  , cacheMisses   :: Int
  }

emptyGrade :: HydrogenGrade
emptyGrade =
  { latencyMs: 0
  , inputTokens: 0
  , outputTokens: 0
  , providerCalls: 0
  , retries: 0
  , cacheHits: 0
  , cacheMisses: 0
  }

combineGrades :: HydrogenGrade -> HydrogenGrade -> HydrogenGrade
combineGrades g1 g2 =
  { latencyMs: g1.latencyMs + g2.latencyMs
  , inputTokens: g1.inputTokens + g2.inputTokens
  , outputTokens: g1.outputTokens + g2.outputTokens
  , providerCalls: g1.providerCalls + g2.providerCalls
  , retries: g1.retries + g2.retries
  , cacheHits: g1.cacheHits + g2.cacheHits
  , cacheMisses: g1.cacheMisses + g2.cacheMisses
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // hydrogen co-effect
-- ════════════════════════════════════════════════════════════════════════════

-- | Value-level resource tracking. Records what resources were accessed.
type HydrogenCoEffect =
  { httpAccesses   :: Array String  -- URLs accessed
  , authUsages     :: Array String  -- Auth providers used
  , configAccesses :: Array String  -- Config keys read
  }

emptyCoEffect :: HydrogenCoEffect
emptyCoEffect =
  { httpAccesses: []
  , authUsages: []
  , configAccesses: []
  }

combineCoEffects :: HydrogenCoEffect -> HydrogenCoEffect -> HydrogenCoEffect
combineCoEffects ce1 ce2 =
  { httpAccesses: ce1.httpAccesses <> ce2.httpAccesses
  , authUsages: ce1.authUsages <> ce2.authUsages
  , configAccesses: ce1.configAccesses <> ce2.configAccesses
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                               // graded monad (the core)
-- ════════════════════════════════════════════════════════════════════════════

-- | The Hydrogen graded monad.
--
-- @HydrogenM es a@ is a computation that:
--   - May perform effects in the set @es@ (type-level, checked at compile time)
--   - Produces a value of type @a@
--   - Accumulates runtime cost data in HydrogenGrade and HydrogenCoEffect
--     (value-level, available at runtime)
--
-- The phantom type parameter @es@ is the grade.
-- It's a sorted set of effect labels. PureScript enforces at compile time that
-- operations requiring Net are only called from contexts where Net is
-- in the grade.
newtype HydrogenM :: List' GradeLabel -> Type -> Type
newtype HydrogenM es a = HydrogenM
  (Aff { result :: a, grade :: HydrogenGrade, coeffect :: HydrogenCoEffect })

-- | HydrogenM is an Orchard & Petricek graded monad.
--
-- The grade algebra:
--   Unit  = Pure (Nil')         — pure computation, no effects
--   Plus  = Union               — set union of effect labels
instance effectHydrogenM :: Effect.Effect HydrogenM where
  return a = HydrogenM $ pure { result: a, grade: emptyGrade, coeffect: emptyCoEffect }
  
  bind (HydrogenM m) f = HydrogenM $ do
    r1 <- m
    let (HydrogenM m2) = f r1.result
    r2 <- m2
    pure
      { result: r2.result
      , grade: combineGrades r1.grade r2.grade
      , coeffect: combineCoEffects r1.coeffect r2.coeffect
      }

-- | Run a graded computation. The grade @es@ is erased at runtime —
-- it exists only to constrain composition at compile time.
runHydrogenM :: forall es a
              . HydrogenM es a 
             -> Aff { result :: a, grade :: HydrogenGrade, coeffect :: HydrogenCoEffect }
runHydrogenM (HydrogenM m) = m

-- | Run discarding tracking data.
runHydrogenMPure :: forall es a. HydrogenM es a -> Aff a
runHydrogenMPure m = do
  r <- runHydrogenM m
  pure r.result

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // primitive lift points
-- ════════════════════════════════════════════════════════════════════════════

-- Each lift point tags the type-level grade with exactly the label(s)
-- corresponding to the kind of effect being performed. Callers of these
-- functions get their grade widened automatically by the Effect instance's
-- Plus (= Union).

-- | Lift a pure (no-Aff) value. Grade: Pure (Nil').
liftPure :: forall a. a -> HydrogenM Pure a
liftPure a = HydrogenM $ pure { result: a, grade: emptyGrade, coeffect: emptyCoEffect }

-- | Lift an Aff action that performs network access.
-- Grade: '[Net]. This is the *only* way to introduce Net into the grade.
liftNet :: forall a. Aff a -> HydrogenM (Net :> Nil') a
liftNet action = HydrogenM $ do
  result <- action
  pure { result, grade: emptyGrade, coeffect: emptyCoEffect }

-- | Lift an Aff action that uses authentication credentials.
liftAuth :: forall a. Aff a -> HydrogenM (Auth :> Nil') a
liftAuth action = HydrogenM $ do
  result <- action
  pure { result, grade: emptyGrade, coeffect: emptyCoEffect }

-- | Lift an Aff action that reads configuration.
liftConfig :: forall a. Aff a -> HydrogenM (Config :> Nil') a
liftConfig action = HydrogenM $ do
  result <- action
  pure { result, grade: emptyGrade, coeffect: emptyCoEffect }

-- | Lift a logging action.
liftLog :: forall a. Aff a -> HydrogenM (Log :> Nil') a
liftLog action = HydrogenM $ do
  result <- action
  pure { result, grade: emptyGrade, coeffect: emptyCoEffect }

-- | Lift a cryptographic operation.
liftCrypto :: forall a. Aff a -> HydrogenM (Crypto :> Nil') a
liftCrypto action = HydrogenM $ do
  result <- action
  pure { result, grade: emptyGrade, coeffect: emptyCoEffect }

-- | Escape hatch: lift arbitrary Aff with full effect set.
-- Use sparingly — this defeats the purpose of grading.
-- Every use should have a comment justifying why.
liftAff :: forall a. Aff a -> HydrogenM Full a
liftAff action = HydrogenM $ do
  result <- action
  pure { result, grade: emptyGrade, coeffect: emptyCoEffect }
