-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // Hydrogen.Effect.Grade
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
--  Type-level grade lattice for the Hydrogen graded monad.
--
--  Effect categories form a bounded join-semilattice:
--
--      Pure ⊑ Net ⊑ Net∪Auth ⊑ ... ⊑ ⊤
--
--  Composition (Plus) is set union: if f : HydrogenM '[Net] a and
--  g : HydrogenM '[Auth] b, then (f >>= \_ -> g) : HydrogenM '[Net, Auth] b.
--
--  This is the type-level tracking. Runtime cost data (latency, tokens,
--  timestamps) is accumulated at the value level in HydrogenGrade,
--  HydrogenCoEffect, and HydrogenProvenance — those are orthogonal.
--
--  Ported from: docs/reference/straylight-integration/Effects/Grade.hs
--  Based on: Orchard & Petricek (2014) effect-monad
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.Effect.Grade
  ( -- * Effect label kind
    GradeLabel
  
  -- * Effect label types
  , Net
  , Auth
  , Config
  , Log
  , Crypto
  , Fs
  
  -- * Grade type (type-level list of labels)
  , Grade
  
  -- * Convenience type aliases
  , Pure
  , NetOnly
  , AuthOnly
  , NetAuth
  , Full
  
  -- * Type-level operations (classes)
  , class GradeUnion
  , class GradeMember
  , class GradeSubset
  ) where



-- ════════════════════════════════════════════════════════════════════════════
--                                                           // effect label kind
-- ════════════════════════════════════════════════════════════════════════════

-- | Kind for effect labels. Each label corresponds to a category of side
-- effect that a computation may perform.
-- 
-- The labels form a total order: Net < Auth < Config < Log < Crypto < Fs
-- This ordering is used to maintain sorted grade lists for canonical form.
data GradeLabel

-- | Network I/O (HTTP calls to providers, external services)
foreign import data Net :: GradeLabel

-- | Authentication credential usage (API keys, tokens, secrets)
foreign import data Auth :: GradeLabel

-- | Configuration access (environment variables, config files)
foreign import data Config :: GradeLabel

-- | Structured logging and observability
foreign import data Log :: GradeLabel

-- | Cryptographic operations (signing, hashing, encryption)
foreign import data Crypto :: GradeLabel

-- | Filesystem access outside sandbox
foreign import data Fs :: GradeLabel

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // grade type
-- ════════════════════════════════════════════════════════════════════════════

-- | A Grade is a type-level list of GradeLabels, maintained in sorted order.
-- The empty list '[] represents a pure computation with no effects.
-- 
-- Examples:
--   Pure     = '[]           -- no effects
--   NetOnly  = '[Net]        -- only network I/O
--   NetAuth  = '[Net, Auth]  -- network + auth
--   Full     = '[Net, Auth, Config, Log, Crypto, Fs]  -- all effects
foreign import data Grade :: Type

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // convenience aliases
-- ════════════════════════════════════════════════════════════════════════════

-- | Pure computation — no effects permitted.
-- This is the Unit of the grade monoid.
foreign import data Pure :: Grade

-- | Network-only computation.
foreign import data NetOnly :: Grade

-- | Auth-only computation.
foreign import data AuthOnly :: Grade

-- | Network + Auth — the common case for provider API calls.
foreign import data NetAuth :: Grade

-- | Full effect set — all effects permitted.
-- This is the Top (⊤) of the grade lattice.
-- Use sparingly — defeats the purpose of grading.
foreign import data Full :: Grade

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // type-level operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Type-level sorted set union. This is the Plus operation for the graded
-- monad: composing two computations unions their effect sets.
--
-- Laws:
--   Union Pure g = g                    (left identity)
--   Union f Pure = f                    (right identity)
--   Union f g = Union g f               (commutativity, via sorting)
--   Union f (Union g h) = Union (Union f g) h  (associativity)
--
-- The result is always in canonical sorted form.
class GradeUnion (f :: Grade) (g :: Grade) (result :: Grade) | f g -> result

-- Pure cases (ordered by specificity)
instance gradeUnionPurePure :: GradeUnion Pure Pure Pure
else instance gradeUnionPureNetOnly :: GradeUnion Pure NetOnly NetOnly
else instance gradeUnionPureAuthOnly :: GradeUnion Pure AuthOnly AuthOnly
else instance gradeUnionPureNetAuth :: GradeUnion Pure NetAuth NetAuth
else instance gradeUnionPureFull :: GradeUnion Pure Full Full

-- NetOnly cases
else instance gradeUnionNetOnlyPure :: GradeUnion NetOnly Pure NetOnly
else instance gradeUnionNetOnlyNetOnly :: GradeUnion NetOnly NetOnly NetOnly
else instance gradeUnionNetOnlyAuthOnly :: GradeUnion NetOnly AuthOnly NetAuth
else instance gradeUnionNetOnlyNetAuth :: GradeUnion NetOnly NetAuth NetAuth
else instance gradeUnionNetOnlyFull :: GradeUnion NetOnly Full Full

-- AuthOnly cases
else instance gradeUnionAuthOnlyPure :: GradeUnion AuthOnly Pure AuthOnly
else instance gradeUnionAuthOnlyNetOnly :: GradeUnion AuthOnly NetOnly NetAuth
else instance gradeUnionAuthOnlyAuthOnly :: GradeUnion AuthOnly AuthOnly AuthOnly
else instance gradeUnionAuthOnlyNetAuth :: GradeUnion AuthOnly NetAuth NetAuth
else instance gradeUnionAuthOnlyFull :: GradeUnion AuthOnly Full Full

-- NetAuth cases
else instance gradeUnionNetAuthPure :: GradeUnion NetAuth Pure NetAuth
else instance gradeUnionNetAuthNetOnly :: GradeUnion NetAuth NetOnly NetAuth
else instance gradeUnionNetAuthAuthOnly :: GradeUnion NetAuth AuthOnly NetAuth
else instance gradeUnionNetAuthNetAuth :: GradeUnion NetAuth NetAuth NetAuth
else instance gradeUnionNetAuthFull :: GradeUnion NetAuth Full Full

-- Full absorbs everything
else instance gradeUnionFullPure :: GradeUnion Full Pure Full
else instance gradeUnionFullNetOnly :: GradeUnion Full NetOnly Full
else instance gradeUnionFullAuthOnly :: GradeUnion Full AuthOnly Full
else instance gradeUnionFullNetAuth :: GradeUnion Full NetAuth Full
else instance gradeUnionFullFull :: GradeUnion Full Full Full

-- | Type-level membership test.
-- GradeMember l g holds iff label l is in grade g.
--
-- This is used to constrain lift operations: liftNet requires
-- Net to be in the grade, liftAuth requires Auth, etc.
class GradeMember (l :: GradeLabel) (g :: Grade)

-- Net membership
instance gradeMemberNetNet :: GradeMember Net NetOnly
instance gradeMemberNetNetAuth :: GradeMember Net NetAuth
instance gradeMemberNetFull :: GradeMember Net Full

-- Auth membership
instance gradeMemberAuthAuth :: GradeMember Auth AuthOnly
instance gradeMemberAuthNetAuth :: GradeMember Auth NetAuth
instance gradeMemberAuthFull :: GradeMember Auth Full

-- Config membership
instance gradeMemberConfigFull :: GradeMember Config Full

-- Log membership
instance gradeMemberLogFull :: GradeMember Log Full

-- Crypto membership
instance gradeMemberCryptoFull :: GradeMember Crypto Full

-- Fs membership
instance gradeMemberFsFull :: GradeMember Fs Full

-- | Type-level subset test.
-- GradeSubset f g holds iff every label in f is also in g.
--
-- This enables subeffecting: a computation with grade '[Net] can be
-- used where '[Net, Auth] is expected (widening).
class GradeSubset (f :: Grade) (g :: Grade)

-- Pure is subset of everything
instance gradeSubsetPure :: GradeSubset Pure g

-- Reflexivity
instance gradeSubsetNetNet :: GradeSubset NetOnly NetOnly
instance gradeSubsetAuthAuth :: GradeSubset AuthOnly AuthOnly
instance gradeSubsetNetAuthNetAuth :: GradeSubset NetAuth NetAuth
instance gradeSubsetFullFull :: GradeSubset Full Full

-- Single labels subset of larger grades
instance gradeSubsetNetNetAuth :: GradeSubset NetOnly NetAuth
instance gradeSubsetAuthNetAuth :: GradeSubset AuthOnly NetAuth
instance gradeSubsetNetFull :: GradeSubset NetOnly Full
instance gradeSubsetAuthFull :: GradeSubset AuthOnly Full
instance gradeSubsetNetAuthFull :: GradeSubset NetAuth Full
