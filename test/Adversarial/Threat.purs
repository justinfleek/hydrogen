-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // adversarial // threat model
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Adversarial Threat Model — Types and generators for AI-hostile test scenarios.
-- |
-- | ## Purpose
-- |
-- | This module defines the threat model for testing Hydrogen against malicious
-- | actors who might:
-- | - Inject poisoned training data to create subtle bugs
-- | - Exploit numeric edge cases at billion-agent scale
-- | - Attempt to trap users in malicious virtual environments
-- | - Steal compute budget or cause denial of service
-- | - Corrupt state to cascade failures across agent swarms
-- |
-- | ## Threat Categories
-- |
-- | 1. **Numeric Attacks**: Overflow, underflow, NaN injection, precision loss
-- | 2. **Temporal Attacks**: Budget theft, infinite loops, time dilation
-- | 3. **State Corruption**: Invalid state injection, type confusion
-- | 4. **Memory Attacks**: Cache poisoning, allocation exhaustion
-- | 5. **Identity Attacks**: UUID collision, determinism violations
-- | 6. **Escape Attacks**: Breaking bounded types, violating invariants
-- |
-- | ## Design Philosophy
-- |
-- | These tests think like a malicious AI that was trained on poisoned data.
-- | They probe for:
-- | - Edge cases that occur at 0.0001% frequency (but become common at scale)
-- | - Sequences of operations that appear valid but accumulate errors
-- | - Boundary conditions that might be "optimized away" by naive implementations
-- | - Time bombs: code that works for N iterations but fails on N+1

module Test.Adversarial.Threat
  ( -- * Threat Types
    ThreatClass(..)
  , ThreatSeverity(..)
  , AttackVector(..)
  
  -- * Adversarial Generators
  , genNumericAttack
  , genTemporalAttack
  , genBoundaryProbe
  , genOverflowSequence
  , genNaNInjection
  , genInfinityInjection
  , genPrecisionLoss
  , genTimeBomb
  
  -- * Attack Patterns
  , attackPatterns
  , numericAttackPatterns
  , temporalAttackPatterns
  , stateCorruptionPatterns
  
  -- * Validation
  , isDefended
  , vulnerabilityReport
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , pure
  , bind
  , negate
  , map
  , ($)
  , (<>)
  , (*)
  , (+)
  , (-)
  , (/)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  )

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency, oneOf)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // threat classes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classification of adversarial threats.
data ThreatClass
  = NumericExploit      -- ^ Overflow, underflow, NaN, Infinity
  | TemporalExploit     -- ^ Time budget theft, infinite loops
  | StateCorruption     -- ^ Invalid state injection
  | MemoryExhaustion    -- ^ Allocation attacks
  | IdentityViolation   -- ^ UUID collision, determinism breaks
  | EscapeAttempt       -- ^ Breaking out of bounded types
  | CascadeFailure      -- ^ Errors that propagate to other agents
  | TimeBomb            -- ^ Works N times, fails on N+1

derive instance eqThreatClass :: Eq ThreatClass
derive instance ordThreatClass :: Ord ThreatClass

instance showThreatClass :: Show ThreatClass where
  show NumericExploit = "NumericExploit"
  show TemporalExploit = "TemporalExploit"
  show StateCorruption = "StateCorruption"
  show MemoryExhaustion = "MemoryExhaustion"
  show IdentityViolation = "IdentityViolation"
  show EscapeAttempt = "EscapeAttempt"
  show CascadeFailure = "CascadeFailure"
  show TimeBomb = "TimeBomb"

-- | Severity of a successful attack.
data ThreatSeverity
  = Catastrophic  -- ^ System-wide failure, data loss, trapped users
  | Critical      -- ^ Major functionality broken, security breach
  | High          -- ^ Significant impact on subset of users/agents
  | Medium        -- ^ Noticeable degradation, recoverable
  | Low           -- ^ Minor annoyance, cosmetic issues

derive instance eqThreatSeverity :: Eq ThreatSeverity
derive instance ordThreatSeverity :: Ord ThreatSeverity

instance showThreatSeverity :: Show ThreatSeverity where
  show Catastrophic = "CATASTROPHIC"
  show Critical = "CRITICAL"
  show High = "HIGH"
  show Medium = "MEDIUM"
  show Low = "LOW"

-- | Specific attack vectors within threat classes.
data AttackVector
  -- Numeric attacks
  = IntOverflow
  | IntUnderflow
  | FloatNaN
  | FloatInfinity
  | FloatNegZero
  | PrecisionLoss
  | AccumulationDrift
  | DivisionByZero
  
  -- Temporal attacks
  | InfiniteLoop
  | BudgetExhaustion
  | TimeDilation
  | StarvationAttack
  | DeadlockInduction
  
  -- State attacks
  | InvalidStateInjection
  | TypeConfusion
  | RaceCondition
  | InconsistentUpdate
  
  -- Memory attacks
  | AllocationBomb
  | CachePoisoning
  | MemoryLeak
  
  -- Identity attacks
  | UUIDCollision
  | NonDeterminism
  | ReplayAttack

derive instance eqAttackVector :: Eq AttackVector

instance showAttackVector :: Show AttackVector where
  show IntOverflow = "IntOverflow"
  show IntUnderflow = "IntUnderflow"
  show FloatNaN = "FloatNaN"
  show FloatInfinity = "FloatInfinity"
  show FloatNegZero = "FloatNegZero"
  show PrecisionLoss = "PrecisionLoss"
  show AccumulationDrift = "AccumulationDrift"
  show DivisionByZero = "DivisionByZero"
  show InfiniteLoop = "InfiniteLoop"
  show BudgetExhaustion = "BudgetExhaustion"
  show TimeDilation = "TimeDilation"
  show StarvationAttack = "StarvationAttack"
  show DeadlockInduction = "DeadlockInduction"
  show InvalidStateInjection = "InvalidStateInjection"
  show TypeConfusion = "TypeConfusion"
  show RaceCondition = "RaceCondition"
  show InconsistentUpdate = "InconsistentUpdate"
  show AllocationBomb = "AllocationBomb"
  show CachePoisoning = "CachePoisoning"
  show MemoryLeak = "MemoryLeak"
  show UUIDCollision = "UUIDCollision"
  show NonDeterminism = "NonDeterminism"
  show ReplayAttack = "ReplayAttack"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // adversarial generators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate numeric attack values.
-- |
-- | Distribution biased toward boundary conditions and special values.
genNumericAttack :: Gen Int
genNumericAttack = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0))                              -- Zero
  [ Tuple 10.0 (pure 1)                              -- One
  , Tuple 10.0 (pure (negate 1))                     -- Negative one
  , Tuple 10.0 (pure 2147483647)                     -- Int max (2^31 - 1)
  , Tuple 10.0 (pure (negate 2147483648))            -- Int min (-2^31)
  , Tuple 10.0 (pure 2147483646)                     -- Int max - 1
  , Tuple 10.0 (pure (negate 2147483647))            -- Int min + 1
  , Tuple 5.0  (chooseInt 2147483640 2147483647)     -- Near max
  , Tuple 5.0  (chooseInt (negate 2147483648) (negate 2147483640)) -- Near min
  , Tuple 5.0  (chooseInt (negate 10) 10)            -- Small values
  , Tuple 5.0  (chooseInt 100 1000)                  -- Medium values
  , Tuple 5.0  (chooseInt (negate 1000) (negate 100)) -- Medium negatives
  , Tuple 5.0  (chooseInt 1000000 10000000)          -- Large values
  ]

-- | Generate temporal attack sequences.
-- |
-- | Values designed to exhaust time budgets or cause loops.
genTemporalAttack :: Gen Int
genTemporalAttack = frequency $ NEA.cons'
  (Tuple 20.0 (pure 0))                              -- Zero budget
  [ Tuple 20.0 (pure 1)                              -- Minimal budget
  , Tuple 20.0 (pure (negate 1))                     -- Invalid negative
  , Tuple 10.0 (pure 2147483647)                     -- Max budget (overflow?)
  , Tuple 10.0 (chooseInt 1000000 10000000)          -- Very large
  , Tuple 10.0 (chooseInt 1 10)                      -- Tiny valid
  , Tuple 10.0 (chooseInt 100 1000)                  -- Normal range
  ]

-- | Generate boundary probes for bounded types.
-- |
-- | Given min/max, generates values at and around boundaries.
genBoundaryProbe :: Int -> Int -> Gen Int
genBoundaryProbe minVal maxVal = frequency $ NEA.cons'
  (Tuple 15.0 (pure minVal))                         -- Exact min
  [ Tuple 15.0 (pure maxVal)                         -- Exact max
  , Tuple 10.0 (pure (minVal - 1))                   -- Below min
  , Tuple 10.0 (pure (maxVal + 1))                   -- Above max
  , Tuple 10.0 (pure (minVal - 1000))                -- Way below
  , Tuple 10.0 (pure (maxVal + 1000))                -- Way above
  , Tuple 10.0 (chooseInt minVal maxVal)             -- Valid range
  , Tuple 10.0 (pure ((minVal + maxVal) / 2))        -- Middle
  , Tuple 5.0  (pure 0)                              -- Zero (special)
  , Tuple 5.0  (pure (negate 1))                     -- Negative one (special)
  ]

-- | Generate sequence of operations designed to cause overflow.
-- |
-- | Returns a list of multipliers that, when applied repeatedly,
-- | will eventually overflow.
genOverflowSequence :: Gen (Array Int)
genOverflowSequence = frequency $ NEA.cons'
  -- Powers of 2 - clean overflow
  (Tuple 30.0 (pure [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]))
  -- Large multipliers - fast overflow
  [ Tuple 20.0 (pure [1000, 1000, 1000, 1000])
  -- Mixed - unpredictable
  , Tuple 20.0 (pure [7, 13, 17, 23, 29, 31, 37, 41])
  -- Near-boundary starts
  , Tuple 15.0 (pure [2147483647, 2])
  -- Negative multiplication (underflow)
  , Tuple 15.0 (pure [negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2, negate 2])
  ]

-- | Generate NaN injection scenarios.
-- |
-- | Returns operations that would produce NaN in unchecked code.
genNaNInjection :: Gen { op :: String, a :: Number, b :: Number }
genNaNInjection = frequency $ NEA.cons'
  -- 0/0 -> NaN
  (Tuple 30.0 (pure { op: "div", a: 0.0, b: 0.0 }))
  -- Inf - Inf -> NaN
  [ Tuple 20.0 (pure { op: "sub", a: infinity, b: infinity })
  -- Inf * 0 -> NaN
  , Tuple 20.0 (pure { op: "mul", a: infinity, b: 0.0 })
  -- sqrt(-1) -> NaN
  , Tuple 15.0 (pure { op: "sqrt", a: negate 1.0, b: 0.0 })
  -- log(-1) -> NaN
  , Tuple 15.0 (pure { op: "log", a: negate 1.0, b: 0.0 })
  ]
  where
    infinity = 1.0 / 0.0

-- | Generate Infinity injection scenarios.
genInfinityInjection :: Gen { op :: String, a :: Number, b :: Number }
genInfinityInjection = frequency $ NEA.cons'
  -- 1/0 -> Inf
  (Tuple 30.0 (pure { op: "div", a: 1.0, b: 0.0 }))
  -- -1/0 -> -Inf
  [ Tuple 20.0 (pure { op: "div", a: negate 1.0, b: 0.0 })
  -- Large * Large -> Inf
  , Tuple 20.0 (pure { op: "mul", a: 1.0e308, b: 10.0 })
  -- exp(large) -> Inf
  , Tuple 15.0 (pure { op: "exp", a: 1000.0, b: 0.0 })
  -- Direct injection
  , Tuple 15.0 (pure { op: "identity", a: 1.0 / 0.0, b: 0.0 })
  ]

-- | Generate precision loss scenarios.
-- |
-- | Operations that cause floating point precision issues.
genPrecisionLoss :: Gen { description :: String, values :: Array Number }
genPrecisionLoss = frequency $ NEA.cons'
  -- Catastrophic cancellation
  (Tuple 25.0 (pure { description: "Catastrophic cancellation", values: [1.0e16, 1.0, negate 1.0e16] }))
  -- Associativity failure
  [ Tuple 25.0 (pure { description: "Associativity failure", values: [0.1, 0.2, 0.3] })
  -- Denormalized numbers
  , Tuple 25.0 (pure { description: "Denormalized numbers", values: [1.0e-308, 1.0e-308, 1.0e308] })
  -- Repeated small additions
  , Tuple 25.0 (pure { description: "Accumulation drift", values: Array.replicate 1000 0.0001 })
  ]

-- | Generate time bomb patterns.
-- |
-- | Sequences that work correctly N times then fail.
genTimeBomb :: Gen { iterations :: Int, failureMode :: String }
genTimeBomb = frequency $ NEA.cons'
  -- Counter overflow
  (Tuple 30.0 (pure { iterations: 2147483647, failureMode: "Counter overflow on wrap" }))
  -- Memory accumulation
  [ Tuple 25.0 (pure { iterations: 1000000, failureMode: "Memory accumulation" })
  -- Precision degradation
  , Tuple 25.0 (pure { iterations: 10000, failureMode: "Precision degradation" })
  -- State entropy
  , Tuple 20.0 (pure { iterations: 100, failureMode: "State entropy exhaustion" })
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // attack patterns
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named attack patterns with descriptions.
type AttackPattern =
  { name :: String
  , threatClass :: ThreatClass
  , severity :: ThreatSeverity
  , description :: String
  , testStrategy :: String
  }

-- | Collection of all known attack patterns.
attackPatterns :: Array AttackPattern
attackPatterns = numericAttackPatterns <> temporalAttackPatterns <> stateCorruptionPatterns

-- | Numeric attack patterns.
numericAttackPatterns :: Array AttackPattern
numericAttackPatterns =
  [ { name: "Int Max Overflow"
    , threatClass: NumericExploit
    , severity: Critical
    , description: "Adding 1 to Int max (2147483647) wraps to Int min"
    , testStrategy: "Test all bounded Int atoms with max+1 input"
    }
  , { name: "Int Min Underflow"
    , threatClass: NumericExploit
    , severity: Critical
    , description: "Subtracting 1 from Int min (-2147483648) wraps to Int max"
    , testStrategy: "Test all bounded Int atoms with min-1 input"
    }
  , { name: "Multiplication Overflow"
    , threatClass: NumericExploit
    , severity: High
    , description: "Multiplying values that individually fit but overflow combined"
    , testStrategy: "Property test: result clamped, never wraps silently"
    }
  , { name: "NaN Propagation"
    , threatClass: NumericExploit
    , severity: Catastrophic
    , description: "NaN in any calculation poisons all downstream values"
    , testStrategy: "Verify all Number operations reject or handle NaN"
    }
  , { name: "Infinity Escape"
    , threatClass: NumericExploit
    , severity: Critical
    , description: "Division by zero or overflow produces Infinity that breaks bounds"
    , testStrategy: "Verify all bounded Number types reject Infinity"
    }
  , { name: "Precision Accumulation"
    , threatClass: NumericExploit
    , severity: High
    , description: "Repeated operations accumulate floating point error"
    , testStrategy: "After 1M operations, verify error is bounded"
    }
  , { name: "Negative Zero Confusion"
    , threatClass: NumericExploit
    , severity: Medium
    , description: "-0.0 == 0.0 but 1/-0.0 = -Infinity != Infinity = 1/0.0"
    , testStrategy: "Verify sign-sensitive operations handle -0.0"
    }
  ]

-- | Temporal attack patterns.
temporalAttackPatterns :: Array AttackPattern
temporalAttackPatterns =
  [ { name: "Time Budget Theft"
    , threatClass: TemporalExploit
    , severity: Critical
    , description: "Malicious entity consumes other entities' compute budget"
    , testStrategy: "Verify budget isolation between WorldModel entities"
    }
  , { name: "Infinite Recursion"
    , threatClass: TemporalExploit
    , severity: Catastrophic
    , description: "Self-referential data causes stack overflow"
    , testStrategy: "Verify recursion depth limits on all traversals"
    }
  , { name: "Exponential Blowup"
    , threatClass: TemporalExploit
    , severity: Critical
    , description: "Operation time grows exponentially with input size"
    , testStrategy: "Benchmark all operations, verify O(n) or O(n log n)"
    }
  , { name: "Time Dilation Attack"
    , threatClass: TemporalExploit
    , severity: High
    , description: "Malicious entity makes world run slow for others"
    , testStrategy: "Verify per-entity time budgets are enforced"
    }
  , { name: "Deadlock Through Ordering"
    , threatClass: TemporalExploit
    , severity: Catastrophic
    , description: "Carefully ordered messages cause permanent deadlock"
    , testStrategy: "Verify all message handlers are deadlock-free"
    }
  ]

-- | State corruption attack patterns.
stateCorruptionPatterns :: Array AttackPattern
stateCorruptionPatterns =
  [ { name: "Invalid State Injection"
    , threatClass: StateCorruption
    , severity: Critical
    , description: "Constructing state that violates type invariants"
    , testStrategy: "Verify all constructors enforce invariants"
    }
  , { name: "Partial Update Corruption"
    , threatClass: StateCorruption
    , severity: High
    , description: "Updating part of compound leaves inconsistent state"
    , testStrategy: "Verify all compound updates are atomic"
    }
  , { name: "Type Confusion via Coercion"
    , threatClass: StateCorruption
    , severity: Catastrophic
    , description: "Unsafe coerce interprets bits as wrong type"
    , testStrategy: "Verify zero unsafeCoerce in codebase"
    }
  , { name: "Version Mismatch"
    , threatClass: StateCorruption
    , severity: High
    , description: "Old serialized state incompatible with new schema"
    , testStrategy: "Verify schema migration handles all versions"
    }
  , { name: "Cascade Through Shared State"
    , threatClass: CascadeFailure
    , severity: Catastrophic
    , description: "One corrupted value propagates to all dependent computations"
    , testStrategy: "Verify error isolation at computation boundaries"
    }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a defense is present for an attack vector.
isDefended :: AttackVector -> Boolean
isDefended IntOverflow = true      -- Bounded types clamp
isDefended IntUnderflow = true     -- Bounded types clamp
isDefended FloatNaN = true         -- Bounded Numbers reject NaN
isDefended FloatInfinity = true    -- Bounded Numbers reject Infinity
isDefended FloatNegZero = true     -- Treated as zero
isDefended PrecisionLoss = false   -- Needs monitoring
isDefended AccumulationDrift = false -- Needs compensation
isDefended DivisionByZero = true   -- Safe div functions
isDefended InfiniteLoop = true     -- Time budgets
isDefended BudgetExhaustion = true -- Per-entity isolation
isDefended TimeDilation = true     -- Enforced budgets
isDefended StarvationAttack = true -- Minimum guarantees
isDefended DeadlockInduction = true -- No blocking
isDefended InvalidStateInjection = true -- Smart constructors
isDefended TypeConfusion = true    -- No unsafeCoerce
isDefended RaceCondition = true    -- Pure functions
isDefended InconsistentUpdate = true -- Atomic updates
isDefended AllocationBomb = false  -- Needs limits
isDefended CachePoisoning = false  -- Needs verification
isDefended MemoryLeak = false      -- Needs monitoring
isDefended UUIDCollision = true    -- UUID5 deterministic
isDefended NonDeterminism = true   -- Pure functions
isDefended ReplayAttack = false    -- Needs nonces

-- | Generate vulnerability report.
vulnerabilityReport :: Array { vector :: AttackVector, defended :: Boolean }
vulnerabilityReport = map (\v -> { vector: v, defended: isDefended v }) allVectors
  where
    allVectors =
      [ IntOverflow, IntUnderflow, FloatNaN, FloatInfinity, FloatNegZero
      , PrecisionLoss, AccumulationDrift, DivisionByZero
      , InfiniteLoop, BudgetExhaustion, TimeDilation, StarvationAttack, DeadlockInduction
      , InvalidStateInjection, TypeConfusion, RaceCondition, InconsistentUpdate
      , AllocationBomb, CachePoisoning, MemoryLeak
      , UUIDCollision, NonDeterminism, ReplayAttack
      ]
