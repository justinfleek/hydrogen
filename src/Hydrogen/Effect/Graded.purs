-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // Hydrogen.Effect.Graded
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--     "The sky above the port was the color of television, tuned to a dead
--      channel."
--
--                                                              — Neuromancer
--
-- Graded monad for Hydrogen operations, ported from CTO's Haskell impl.
-- Source: docs/reference/straylight-integration/Effects/Graded.hs
--
-- The grade parameter is a type-level sorted set of GradeLabel atoms.
-- Composition unions the sets:
--
--     f : HydrogenM NetOnly a
--     g : HydrogenM AuthOnly b
--     f >>= \_ -> g : HydrogenM NetAuth b    -- via GradeUnion
--
-- Runtime tracking (latency, tokens, provenance, coeffects) is accumulated
-- at the value level — the type-level grade is a *static upper bound* on
-- what effects are permitted, while value-level data records what happened.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Effect.Graded
  ( -- * Graded Monad
    HydrogenM(..)
  , HydrogenResult
  , unHydrogenM
  , runHydrogenM
  , runHydrogenMPure
  
  -- * Value-level Grade (cost tracking)
  , HydrogenGrade
  , emptyGrade
  , combineGrades
  , gradeFromLatency
  
  -- * Value-level CoEffect (resource tracking)
  , HydrogenCoEffect
  , HttpAccess
  , AuthUsage
  , ConfigAccess
  , emptyCoEffect
  
  -- * Value-level Provenance
  , HydrogenProvenance
  , emptyProvenance
  
  -- * Re-exports
  , module Hydrogen.Effect.Grade
  ) where

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // imports
-- ════════════════════════════════════════════════════════════════════════════

import Prelude

import Effect (Effect)

import Hydrogen.Effect.Grade
  ( Grade
  , GradeLabel
  , Pure
  , NetOnly
  , AuthOnly
  , NetAuth
  , Full
  , Net
  , Auth
  , Config
  , Log
  , Crypto
  , Fs
  , class GradeUnion
  , class GradeMember
  , class GradeSubset
  )

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // hydrogen grade
-- ════════════════════════════════════════════════════════════════════════════

-- | Value-level cost accumulator. Tracks what actually happened at runtime.
-- Orthogonal to the type-level grade — grade says what's *permitted*,
-- this records what *occurred*.
type HydrogenGrade =
  { latencyMs :: Int
  , inputTokens :: Int
  , outputTokens :: Int
  , providerCalls :: Int
  , retries :: Int
  , cacheHits :: Int
  , cacheMisses :: Int
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

gradeFromLatency :: Int -> HydrogenGrade
gradeFromLatency ms = emptyGrade { latencyMs = ms, providerCalls = 1 }

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // hydrogen co-effect
-- ════════════════════════════════════════════════════════════════════════════

-- Placeholder types - will expand in next edit
type HttpAccess = { url :: String, method :: String }
type AuthUsage = { provider :: String, scope :: String }
type ConfigAccess = { key :: String }

type HydrogenCoEffect =
  { httpAccesses :: Array HttpAccess
  , authUsages :: Array AuthUsage
  , configAccesses :: Array ConfigAccess
  }

emptyCoEffect :: HydrogenCoEffect
emptyCoEffect =
  { httpAccesses: []
  , authUsages: []
  , configAccesses: []
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // hydrogen provenance
-- ════════════════════════════════════════════════════════════════════════════

-- Placeholder - will expand in next edit
type HydrogenProvenance =
  { requestId :: String
  , providersUsed :: Array String
  , modelsUsed :: Array String
  }

emptyProvenance :: HydrogenProvenance
emptyProvenance =
  { requestId: ""
  , providersUsed: []
  , modelsUsed: []
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // graded monad
-- ════════════════════════════════════════════════════════════════════════════

-- | Result type returned by running a graded computation.
type HydrogenResult a =
  { result :: a
  , grade :: HydrogenGrade
  , coeffect :: HydrogenCoEffect
  , provenance :: HydrogenProvenance
  }

-- | The Hydrogen graded monad.
--
-- @HydrogenM g a@ is a computation that:
--   - May perform effects in the grade @g@ (type-level, checked at compile time)
--   - Produces a value of type @a@
--   - Accumulates runtime cost data in HydrogenGrade, HydrogenCoEffect,
--     and HydrogenProvenance (value-level, available at runtime)
--
-- The phantom type parameter @g@ is the grade. It's a canonical sorted set
-- of effect labels. PureScript enforces at compile time that operations
-- requiring Net are only called from contexts where Net is in the grade.
--
-- Mirrors CTO's Haskell impl:
--   newtype GatewayM (es :: [GradeLabel]) a = GatewayM
--     { unGatewayM :: IO (a, GatewayGrade, GatewayProvenance, GatewayCoEffect) }
newtype HydrogenM :: Grade -> Type -> Type
newtype HydrogenM g a = HydrogenM (Effect (HydrogenResult a))

-- | Unwrap the inner Effect.
unHydrogenM :: forall g a. HydrogenM g a -> Effect (HydrogenResult a)
unHydrogenM (HydrogenM m) = m

-- | Run a graded computation. The grade @g@ is erased at runtime —
-- it exists only to constrain composition at compile time.
runHydrogenM :: forall g a. HydrogenM g a -> Effect (HydrogenResult a)
runHydrogenM = unHydrogenM

-- | Run discarding tracking data.
runHydrogenMPure :: forall g a. HydrogenM g a -> Effect a
runHydrogenMPure m = do
  r <- runHydrogenM m
  pure r.result
