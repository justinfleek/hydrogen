━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 // 36 // numeric
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Numeric Pillar

Forward error tracking, graded monads, and sensitivity analysis for 
numerically-correct computation.

────────────────────────────────────────────────────────────────────────────────
                                                                      // overview
────────────────────────────────────────────────────────────────────────────────

## Implementation

- **Location**: `src/Hydrogen/Schema/Numeric/`
- **Files**: 4 modules
- **Key features**: Graded monad for error bounds, sensitivity tracking,
  proven arithmetic operations

## Purpose

Numeric provides infrastructure for **provably correct** floating-point 
computation:

- **Grade**: Non-negative error bounds forming a commutative monoid
- **ForwardError**: Graded monad tracking ideal vs approximate values
- **Sensitivity**: Coeffect tracking for function amplification
- **Primitives**: Arithmetic operations with proven error propagation

────────────────────────────────────────────────────────────────────────────────
                                                     // mathematical // foundation
────────────────────────────────────────────────────────────────────────────────

## The Problem

Floating-point arithmetic introduces rounding errors. At billion-agent scale,
these errors compound catastrophically if not tracked explicitly.

**Without error tracking:**
```
agent1: compute x = 3.14159...
agent2: compute y = x * 1000000
agent3: compute z = y - 3141590
result: z ≈ 0? or z ≈ garbage?
```

**With forward error tracking:**
```
agent1: compute x = 3.14159... ± ε₁
agent2: compute y = x * 1000000 ± (1000000 × ε₁)
agent3: compute z = y - 3141590 ± (1000000 × ε₁ + ε₂)
result: z with known error bounds
```

## NumFuzz Foundation

Based on NumFuzz (Kellison, 2025) — arXiv:2501.14598

Programs using finite-precision arithmetic are **producers** of rounding error.
The graded monad `M[ε]` tracks the maximum error bound ε.

**Structure:**
```
ForwardError ε α = { ideal : α, approx : α, bound : dist ideal approx ≤ ε }
```

────────────────────────────────────────────────────────────────────────────────
                                                                // grade // atom
────────────────────────────────────────────────────────────────────────────────

## Grade

Non-negative error bound with algebraic structure.

| Name | Type | Min | Max | Behavior | Notes |
|------|------|-----|-----|----------|-------|
| Grade | Number | 0.0 | +∞ | clamps at 0 | Error magnitude |

**Invariant:** For all `Grade x`: `x >= 0`

### Algebraic Structure

Grades form multiple algebraic structures:

| Structure | Identity | Operation | Semantics |
|-----------|----------|-----------|-----------|
| Monoid | `zero` | `add` | Sequential error accumulation |
| Semiring | `zero`/`one` | `add`/`mul` | Sensitivity scaling |
| Ring | — | `sub` | Difference (clamps to zero) |

### Constructors

```purescript
-- Smart constructor (clamps negatives to zero)
grade :: Number -> Grade

-- Zero grade (exact computation)
zero :: Grade

-- IEEE binary64 machine epsilon: 2^(-53) ≈ 1.11e-16
machineEpsilon :: Grade

-- Olver's epsilon: u/(1-u) where u = 2^(-53)
olverEpsilon :: Grade
```

### Operations

```purescript
-- Error accumulation (sequential composition)
add :: Grade -> Grade -> Grade

-- Sensitivity scaling
mul :: Grade -> Grade -> Grade

-- Parallel composition (take maximum)
max :: Grade -> Grade -> Grade

-- Predicates
isZero :: Grade -> Boolean
isExact :: Grade -> Boolean  -- alias for isZero
```

### Lean Proofs

Proven in `proofs/Hydrogen/Schema/Numeric/GradedMonad.lean`:

- `Grade.add_assoc`: (a + b) + c = a + (b + c)
- `Grade.add_zero`: a + 0 = a
- `Grade.zero_add`: 0 + a = a

────────────────────────────────────────────────────────────────────────────────
                                                        // forwarderror // monad
────────────────────────────────────────────────────────────────────────────────

## ForwardError

Graded monad pairing ideal and approximate values with error bound.

```purescript
type ForwardError a =
  { ideal :: a       -- What we want (mathematical ideal)
  , approx :: a      -- What we have (computed result)
  , bound :: Grade   -- Upper bound on distance
  }
```

**Invariant:** `distance ideal approx <= bound`

### Constructors

| Constructor | Grade | Use Case |
|-------------|-------|----------|
| `exact x` | 0 | Value with no error |
| `fromApprox ideal approx bound` | verified | Safe construction |
| `fromApproxUnsafe ideal approx bound` | trusted | External proof |

```purescript
-- Exact value (zero error, ideal = approx)
exact :: forall a. a -> ForwardError a

-- Safe constructor (verifies or adjusts bound)
fromApprox :: Number -> Number -> Grade -> ForwardError Number

-- Unsafe constructor (trusts caller)
fromApproxUnsafe :: forall a. a -> a -> Grade -> ForwardError a
```

### Accessors

```purescript
ideal :: forall a. ForwardError a -> a
approx :: forall a. ForwardError a -> a
bound :: forall a. ForwardError a -> Grade
value :: forall a. ForwardError a -> a  -- alias for approx
```

### Grade Operations

```purescript
-- Weaken bound (safe: increase error estimate)
weaken :: forall a. Grade -> ForwardError a -> ForwardError a

-- Strengthen bound (recomputes actual error)
strengthen :: Grade -> ForwardError Number -> ForwardError Number
```

### Monad Laws (Grade-Indexed)

1. `pure_grade`: grade(pure x) = 0
2. `bind_grade`: grade(ma >>= f) = grade(ma) + grade(f(value(ma)))
3. `left_identity`: pure x >>= f ≅ f x (up to grade equivalence)
4. `right_identity`: m >>= pure ≅ m (up to grade equivalence)
5. `associativity`: (m >>= f) >>= g ≅ m >>= (λx. f x >>= g)

────────────────────────────────────────────────────────────────────────────────
                                                    // real number // operations
────────────────────────────────────────────────────────────────────────────────

## Proven Arithmetic

Operations on `ForwardError Number` with mathematically-proven error bounds.

### Addition

```purescript
addReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
```

**Error bound:** ε₁ + ε₂

**Lean proofs:**
- `RealError.add_comm`: addition is commutative
- `RealError.add_assoc`: addition is associative

### Negation

```purescript
negReal :: ForwardError Number -> ForwardError Number
```

**Error bound:** ε (preserved — negation doesn't change distance)

**Lean proof:** `RealError.neg`

### Subtraction

```purescript
subReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
```

**Error bound:** ε₁ + ε₂ (same as addition)

**Lean proof:** `RealError.sub`

### Scaling

```purescript
scaleReal :: Number -> ForwardError Number -> ForwardError Number
```

**Error bound:** |c| × ε

**Lean proof:** `RealError.scale`

### Multiplication

```purescript
mulReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
```

**Error bound:** |a|×εb + |b|×εa + εa×εb

**Formula derivation:**
```
|xy - x̃ỹ| = |xy - x̃y + x̃y - x̃ỹ|
          ≤ |y||x - x̃| + |x̃||y - ỹ|
          ≤ |y|εx + (|x| + εx)εy
          = |x|εy + |y|εx + εxεy
```

### Division

```purescript
divReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
```

**Error bound:** (εa/|b|) + (εb × |a/b|/|b|)

Simplified conservative bound assuming εb << |b|.

────────────────────────────────────────────────────────────────────────────────
                                                       // sensitivity // coeffect
────────────────────────────────────────────────────────────────────────────────

## Sensitivity

Coeffect tracking for function amplification factors.

**Invariant:** For function f with sensitivity s:
```
∀x,y: dist(f(x), f(y)) ≤ s × dist(x, y)
```

```purescript
type Sensitive a b =
  { sensitivity :: Grade
  , fn :: a -> b
  }
```

### Constructors

| Constructor | Sensitivity | Description |
|-------------|-------------|-------------|
| `sensitive s f` | s | Function with known amplification |
| `identity` | 1 | Identity function |
| `scale c` | \|c\| | Multiplication by constant |
| `negate` | 1 | Negation |
| `constant c` | 0 | Constant function |

### Composition

```purescript
compose :: Sensitive b c -> Sensitive a b -> Sensitive a c
```

**Sensitivities multiply:** If f has sensitivity s₁ and g has sensitivity s₂,
then g ∘ f has sensitivity s₁ × s₂.

**Lean proof:** `sensitivity_comp`

### Application

```purescript
applySensitive :: Sensitive a b -> ForwardError a -> ForwardError b
```

**Output error:** s × input error

**Lean proof:** `mapWithSensitivity`

### Classification

```purescript
-- Sensitivity < 1: reduces error
isContraction :: Sensitive a b -> Boolean

-- Sensitivity > 1: amplifies error  
isExpansion :: Sensitive a b -> Boolean

-- Sensitivity = 1: preserves error
isIsometry :: Sensitive a b -> Boolean
```

────────────────────────────────────────────────────────────────────────────────
                                                                // primitives
────────────────────────────────────────────────────────────────────────────────

## Primitives

Utility operations for lifting and arithmetic.

```purescript
-- Lift raw Number with machine epsilon error
liftNumber :: Number -> ForwardError Number

-- Division with error propagation
divReal :: ForwardError Number -> ForwardError Number -> ForwardError Number
```

**liftNumber** is used when a value comes from floating-point computation
(e.g., parsing user input, reading from external source). It attaches
machine epsilon as the initial error bound.

────────────────────────────────────────────────────────────────────────────────
                                                              // source // files
────────────────────────────────────────────────────────────────────────────────

```
src/Hydrogen/Schema/Numeric/
├── ForwardError.purs    # Graded monad for error tracking (353 lines)
├── Grade.purs           # Non-negative error bounds (237 lines)
├── Primitives.purs      # Arithmetic lifting and division (64 lines)
└── Sensitivity.purs     # Coeffect tracking for amplification (142 lines)
```

4 files, ~796 lines total.

────────────────────────────────────────────────────────────────────────────────
                                                         // design // philosophy
────────────────────────────────────────────────────────────────────────────────

## Why Error Tracking Matters

At billion-agent scale, numerical computation must be **deterministically 
bounded**. An agent cannot trust a computation it cannot verify.

**The traditional approach:**
- Hope floating-point is "close enough"
- Discover errors in production
- Debug across distributed systems

**The Hydrogen approach:**
- Track error bounds explicitly through types
- Prove error propagation rules in Lean4
- Know the worst-case error before execution

### Graded Monads Enable Composition

The graded monad structure means error tracking **composes**:

```purescript
do
  x <- computation1  -- error ε₁
  y <- computation2  -- error ε₂
  pure (x + y)       -- error ε₁ + ε₂ (proven)
```

Agents can compose computations from other agents and know the total
error bound without inspecting implementation details.

### Sensitivity Enables Abstraction

When a function's sensitivity is known, its effect on error is predictable:

```purescript
-- Agent A provides a 2-Lipschitz function
transform :: Sensitive Number Number
transform = sensitive (grade 2.0) someFunction

-- Agent B applies it to error-tracked data
result = applySensitive transform inputData
-- Result error = 2 × input error (guaranteed)
```

### Machine Epsilon is the Floor

No floating-point computation can be more precise than machine epsilon.
The `machineEpsilon` constant (2^-53 for IEEE binary64) represents this
fundamental limit.

**Olver's epsilon** provides a slightly refined bound for relative error
analysis, accounting for the fact that rounding can compound.

────────────────────────────────────────────────────────────────────────────────
                                                          // lean // proof // index
────────────────────────────────────────────────────────────────────────────────

## Lean4 Proofs

All error propagation rules are formally verified in:
`proofs/Hydrogen/Schema/Numeric/GradedMonad.lean`

| Theorem | Statement |
|---------|-----------|
| `pure_grade` | grade(pure x) = 0 |
| `weaken_preserves` | weakening preserves ideal and approx |
| `RealError.add` | addition error bound proof |
| `RealError.add_comm` | addition is commutative |
| `RealError.add_assoc` | addition is associative |
| `RealError.neg` | negation preserves error |
| `RealError.sub` | subtraction error bound proof |
| `RealError.scale` | scaling by constant proof |
| `Grade.add_assoc` | grade addition is associative |
| `Grade.add_zero` | zero is right identity |
| `Grade.zero_add` | zero is left identity |
| `sensitivity_id` | identity has sensitivity 1 |
| `sensitivity_comp` | composition multiplies sensitivities |
| `mapWithSensitivity` | application scales error by sensitivity |

────────────────────────────────────────────────────────────────────────────────
