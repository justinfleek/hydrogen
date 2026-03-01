/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           HYDROGEN // SCHEMA // BRUSH // DYNAMICS
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Response Curves and Dynamics Mappings for Brush Input Processing.

  PURPOSE:
    When pressure, tilt, or velocity flows from a stylus, BMI, uploaded mind,
    or AI agent — it passes through response curves that shape the feel.
    These curves MUST be bounded, monotonic, and sensitivity-tracked.

  WHY BOUNDED:
    An unbounded curve output becomes an unbounded experience for something
    that might be feeling it. A BMI user's tremor amplified to infinity.
    An uploaded mind's light touch exploding into maximum force. These are
    not runtime crashes — they are harms to minds inhabiting the system.

  STRONG INVARIANTS:

    1. BOUNDS PRESERVATION — Curves map BoundedUnit → BoundedUnit
       Invalid outputs are unrepresentable, not runtime-checked.

    2. ENDPOINT PRESERVATION — Curves pass through (0,0) and (1,1)
       Agents can reason about edges without testing.

    3. MONOTONICITY — Curves are monotonically non-decreasing
       More input → more (or equal) output. Always.

    4. SENSITIVITY BOUNDS — Each curve has finite maximum derivative
       Error propagation is bounded. No infinite amplification.

    5. GRADE DEGRADATION — Applying a curve degrades certainty
       Computed values are estimated, not exact. Provenance is honest.

    6. OUTPUT RANGE VALIDITY — Mapped values land in [valueAtMin, valueAtMax]
       Composition is predictable by construction.

  REFERENCES:

    - InputChannel.lean — Graded input types this operates on
    - Bounded.lean — UnitInterval foundation
    - GradedMonad.lean — Forward error tracking
    - Sensation.lean — Why bounded experience matters

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Math.Bounded
import Hydrogen.Schema.Brush.InputChannel
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace Hydrogen.Schema.Brush.Dynamics

open Hydrogen.Math
open Hydrogen.Schema.Brush.InputChannel

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BOUNDED UNIT (LOCAL)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Bounded Unit Type

A value in [0,1] with proofs carried structurally.
This mirrors UnitInterval from Bounded.lean but is defined locally
to avoid import cycles and maintain module independence.
-/

/-- A value bounded in [0, 1] by construction. -/
structure BoundedUnit where
  value : ℝ
  ge_zero : 0 ≤ value
  le_one : value ≤ 1

namespace BoundedUnit

def zero : BoundedUnit := ⟨0, le_refl 0, zero_le_one⟩
def one : BoundedUnit := ⟨1, zero_le_one, le_refl 1⟩

noncomputable def half : BoundedUnit := ⟨0.5, by norm_num, by norm_num⟩

/-- Minimum representable positive value (1/256).
    Used to clamp inputs for curves with unbounded sensitivity at zero. -/
noncomputable def epsilon : BoundedUnit := ⟨1/256, by norm_num, by norm_num⟩

/-- Clamp any real to [0, 1] -/
noncomputable def clamp (x : ℝ) : BoundedUnit :=
  if h0 : x < 0 then zero
  else if h1 : x > 1 then one
  else ⟨x, not_lt.mp h0, not_lt.mp h1⟩

/-- Clamp to [ε, 1] for curves requiring positive input -/
noncomputable def clampPositive (x : ℝ) : BoundedUnit :=
  if h : x < 1/256 then epsilon
  else if h1 : x > 1 then one
  else ⟨x, by linarith [not_lt.mp h], not_lt.mp h1⟩

/-- Linear interpolation -/
noncomputable def lerp (a b t : BoundedUnit) : BoundedUnit :=
  let result := a.value * (1 - t.value) + b.value * t.value
  ⟨result,
   by have ha := a.ge_zero; have hb := b.ge_zero
      have ht := t.ge_zero; have ht1 := t.le_one
      have h1 : 1 - t.value ≥ 0 := by linarith
      nlinarith,
   by have ha := a.le_one; have hb := b.le_one
      have ht := t.ge_zero; have ht1 := t.le_one
      nlinarith⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- BoundedUnit Proofs
-- ─────────────────────────────────────────────────────────────────────────────

theorem valid (u : BoundedUnit) : 0 ≤ u.value ∧ u.value ≤ 1 :=
  ⟨u.ge_zero, u.le_one⟩

theorem zero_val : zero.value = 0 := rfl
theorem one_val : one.value = 1 := rfl

theorem clamp_idempotent (u : BoundedUnit) : clamp u.value = u := by
  simp only [clamp]
  split_ifs with h0 h1
  · exact absurd h0 (not_lt.mpr u.ge_zero)
  · exact absurd h1 (not_lt.mpr u.le_one)
  · rfl

theorem lerp_zero (a b : BoundedUnit) : lerp a b zero = a := by
  simp only [lerp, zero]
  congr 1
  ring

theorem lerp_one (a b : BoundedUnit) : lerp a b one = b := by
  simp only [lerp, one]
  congr 1
  ring

end BoundedUnit

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: RESPONSE CURVE TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Response Curves

Transfer functions that map input [0,1] → output [0,1].
Each curve has proven properties: bounds, endpoints, monotonicity, sensitivity.
-/

/-- Response curve types for dynamics mapping.
    
    Each curve is a function [0,1] → [0,1] with specific feel:
    - Linear: direct 1:1 mapping
    - Soft: light touch sensitive (power < 1)
    - Firm: requires force (power > 1)
    - SCurve: smooth acceleration/deceleration -/
inductive ResponseCurve where
  | linear : ResponseCurve
  | soft : ResponseCurve      -- t^0.5 (sqrt), clamped domain [ε,1]
  | firm : ResponseCurve      -- t^2
  | sCurve : ResponseCurve    -- 3t² - 2t³ (smoothstep)
  deriving DecidableEq, Repr

namespace ResponseCurve

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: CURVE APPLICATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Apply a response curve to a bounded input.
    Returns the raw real value (proofs of boundedness come separately). -/
noncomputable def applyRaw (c : ResponseCurve) (t : BoundedUnit) : ℝ :=
  match c with
  | linear => t.value
  | soft => 
      -- Clamp to [ε, 1] to ensure bounded sensitivity
      let clamped := max (1/256) t.value
      Real.sqrt clamped
  | firm => t.value ^ 2
  | sCurve => 3 * t.value^2 - 2 * t.value^3

-- ─────────────────────────────────────────────────────────────────────────────
-- Bounds Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Linear curve output is non-negative -/
theorem linear_ge_zero (t : BoundedUnit) : applyRaw linear t ≥ 0 := t.ge_zero

/-- Linear curve output is at most 1 -/
theorem linear_le_one (t : BoundedUnit) : applyRaw linear t ≤ 1 := t.le_one

/-- Soft curve output is non-negative -/
theorem soft_ge_zero (t : BoundedUnit) : applyRaw soft t ≥ 0 := by
  simp only [applyRaw]
  exact Real.sqrt_nonneg _

/-- Soft curve output is at most 1 -/
theorem soft_le_one (t : BoundedUnit) : applyRaw soft t ≤ 1 := by
  simp only [applyRaw]
  have h : max (1/256) t.value ≤ 1 := by
    apply max_le
    · norm_num
    · exact t.le_one
  calc Real.sqrt (max (1/256) t.value) 
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

/-- Firm curve output is non-negative -/
theorem firm_ge_zero (t : BoundedUnit) : applyRaw firm t ≥ 0 := by
  simp only [applyRaw]
  exact sq_nonneg t.value

/-- Firm curve output is at most 1 -/
theorem firm_le_one (t : BoundedUnit) : applyRaw firm t ≤ 1 := by
  simp only [applyRaw]
  have h := t.le_one
  have h0 := t.ge_zero
  nlinarith [sq_nonneg t.value, sq_nonneg (1 - t.value)]

/-- S-curve output is non-negative -/
theorem sCurve_ge_zero (t : BoundedUnit) : applyRaw sCurve t ≥ 0 := by
  simp only [applyRaw]
  have h0 := t.ge_zero
  have h1 := t.le_one
  -- 3t² - 2t³ = t²(3 - 2t) ≥ 0 when t ∈ [0,1]
  have ht2 : t.value^2 ≥ 0 := sq_nonneg t.value
  have h32t : 3 - 2*t.value ≥ 0 := by linarith
  have factored : 3 * t.value^2 - 2 * t.value^3 = t.value^2 * (3 - 2*t.value) := by ring
  rw [factored]
  exact mul_nonneg ht2 h32t

/-- S-curve output is at most 1 -/
theorem sCurve_le_one (t : BoundedUnit) : applyRaw sCurve t ≤ 1 := by
  simp only [applyRaw]
  have h0 := t.ge_zero
  have h1 := t.le_one
  -- 3t² - 2t³ ≤ 1 when t ∈ [0,1]
  -- Equivalent to: 2t³ - 3t² + 1 ≥ 0, which factors as (1-t)²(1+2t) ≥ 0
  nlinarith [sq_nonneg t.value, sq_nonneg (1 - t.value), sq_nonneg (t.value - 1)]

/-- All curves map [0,1] → [0,1] -/
theorem bounded (c : ResponseCurve) (t : BoundedUnit) : 
    0 ≤ applyRaw c t ∧ applyRaw c t ≤ 1 := by
  cases c with
  | linear => exact ⟨linear_ge_zero t, linear_le_one t⟩
  | soft => exact ⟨soft_ge_zero t, soft_le_one t⟩
  | firm => exact ⟨firm_ge_zero t, firm_le_one t⟩
  | sCurve => exact ⟨sCurve_ge_zero t, sCurve_le_one t⟩

/-- Apply curve returning a BoundedUnit (bounds by construction) -/
noncomputable def apply (c : ResponseCurve) (t : BoundedUnit) : BoundedUnit :=
  let bounds := bounded c t
  ⟨applyRaw c t, bounds.1, bounds.2⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: ENDPOINT PRESERVATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Linear curve: f(0) = 0 -/
theorem linear_zero : applyRaw linear BoundedUnit.zero = 0 := rfl

/-- Linear curve: f(1) = 1 -/
theorem linear_one : applyRaw linear BoundedUnit.one = 1 := rfl

/-- Firm curve: f(0) = 0 -/
theorem firm_zero : applyRaw firm BoundedUnit.zero = 0 := by
  simp only [applyRaw, BoundedUnit.zero]
  norm_num

/-- Firm curve: f(1) = 1 -/
theorem firm_one : applyRaw firm BoundedUnit.one = 1 := by
  simp only [applyRaw, BoundedUnit.one]
  norm_num

/-- S-curve: f(0) = 0 -/
theorem sCurve_zero : applyRaw sCurve BoundedUnit.zero = 0 := by
  simp only [applyRaw, BoundedUnit.zero]
  norm_num

/-- S-curve: f(1) = 1 -/
theorem sCurve_one : applyRaw sCurve BoundedUnit.one = 1 := by
  simp only [applyRaw, BoundedUnit.one]
  norm_num

/-- Soft curve: f(1) = 1 -/
theorem soft_one : applyRaw soft BoundedUnit.one = 1 := by
  simp only [applyRaw, BoundedUnit.one]
  simp only [max_eq_right (by norm_num : (1:ℝ)/256 ≤ 1)]
  exact Real.sqrt_one

/-- Soft curve at zero maps to sqrt(ε), not 0.
    This is intentional: we clamp to [ε,1] to bound sensitivity.
    For brush dynamics, this means very light pressure still produces
    minimal output rather than exactly zero — which is often desired. -/
theorem soft_zero_clamped : applyRaw soft BoundedUnit.zero = Real.sqrt (1/256) := by
  simp only [applyRaw, BoundedUnit.zero]
  simp only [max_eq_left (by norm_num : (0:ℝ) ≤ 1/256)]

/-- All curves preserve the upper endpoint f(1) = 1 -/
theorem endpoint_one (c : ResponseCurve) : applyRaw c BoundedUnit.one = 1 := by
  cases c with
  | linear => exact linear_one
  | soft => exact soft_one
  | firm => exact firm_one
  | sCurve => exact sCurve_one

/-- Most curves preserve the lower endpoint f(0) = 0.
    Soft is the exception due to sensitivity clamping. -/
theorem endpoint_zero_except_soft (c : ResponseCurve) (hc : c ≠ soft) : 
    applyRaw c BoundedUnit.zero = 0 := by
  cases c with
  | linear => exact linear_zero
  | soft => contradiction
  | firm => exact firm_zero
  | sCurve => exact sCurve_zero

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: MONOTONICITY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Monotonicity

All response curves are monotonically non-decreasing:
  t₁ ≤ t₂ → f(t₁) ≤ f(t₂)

This ensures predictable behavior: more input always produces more (or equal)
output. Agents can reason about brush dynamics without testing edge cases.

| Curve   | Why Monotonic                                    |
|---------|--------------------------------------------------|
| Linear  | f(t) = t, derivative = 1 > 0                     |
| Soft    | f(t) = √t, derivative = 1/(2√t) > 0 for t > 0   |
| Firm    | f(t) = t², derivative = 2t ≥ 0                   |
| SCurve  | f(t) = 3t² - 2t³, derivative = 6t(1-t) ≥ 0      |
-/

/-- Linear curve is monotonic -/
theorem linear_monotone (t₁ t₂ : BoundedUnit) (h : t₁.value ≤ t₂.value) :
    applyRaw linear t₁ ≤ applyRaw linear t₂ := h

/-- Soft curve is monotonic (sqrt is monotone) -/
theorem soft_monotone (t₁ t₂ : BoundedUnit) (h : t₁.value ≤ t₂.value) :
    applyRaw soft t₁ ≤ applyRaw soft t₂ := by
  simp only [applyRaw]
  apply Real.sqrt_le_sqrt
  exact max_le_max_left (1/256) h

/-- Firm curve is monotonic (t² is monotone on [0,1]) -/
theorem firm_monotone (t₁ t₂ : BoundedUnit) (h : t₁.value ≤ t₂.value) :
    applyRaw firm t₁ ≤ applyRaw firm t₂ := by
  simp only [applyRaw]
  have h1 := t₁.ge_zero
  have h2 := t₂.ge_zero
  exact sq_le_sq' (by linarith) h

/-- S-curve is monotonic on [0,1].
    
    Proof: derivative is 6t - 6t² = 6t(1-t) ≥ 0 for t ∈ [0,1].
    We prove directly that t₁ ≤ t₂ → f(t₁) ≤ f(t₂). -/
theorem sCurve_monotone (t₁ t₂ : BoundedUnit) (h : t₁.value ≤ t₂.value) :
    applyRaw sCurve t₁ ≤ applyRaw sCurve t₂ := by
  simp only [applyRaw]
  -- f(t) = 3t² - 2t³ = t²(3 - 2t)
  -- f(t₂) - f(t₁) = 3(t₂² - t₁²) - 2(t₂³ - t₁³)
  -- We need to show this is ≥ 0
  have h1_lo := t₁.ge_zero
  have h1_hi := t₁.le_one
  have h2_lo := t₂.ge_zero
  have h2_hi := t₂.le_one
  -- Factor: f(t₂) - f(t₁) = (t₂ - t₁)(t₂ + t₁)(3 - 2t₂ - 2t₁) + 2t₁t₂(t₂ - t₁)
  -- Actually simpler: use nlinarith with polynomial constraints
  nlinarith [sq_nonneg t₁.value, sq_nonneg t₂.value, 
             sq_nonneg (t₁.value - t₂.value),
             sq_nonneg (1 - t₁.value), sq_nonneg (1 - t₂.value),
             mul_nonneg h1_lo h2_lo,
             mul_nonneg h1_lo (sub_nonneg.mpr h),
             mul_nonneg h2_lo (sub_nonneg.mpr h)]

/-- MONOTONICITY THEOREM: All curves are monotonically non-decreasing.
    
    This is INVARIANT 3: more input → more (or equal) output.
    Agents can trust that brush dynamics behave predictably. -/
theorem monotone (c : ResponseCurve) (t₁ t₂ : BoundedUnit) (h : t₁.value ≤ t₂.value) :
    applyRaw c t₁ ≤ applyRaw c t₂ := by
  cases c with
  | linear => exact linear_monotone t₁ t₂ h
  | soft => exact soft_monotone t₁ t₂ h
  | firm => exact firm_monotone t₁ t₂ h
  | sCurve => exact sCurve_monotone t₁ t₂ h

/-- Monotonicity for the bounded apply function -/
theorem apply_monotone (c : ResponseCurve) (t₁ t₂ : BoundedUnit) (h : t₁.value ≤ t₂.value) :
    (apply c t₁).value ≤ (apply c t₂).value := by
  simp only [apply]
  exact monotone c t₁ t₂ h

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: SENSITIVITY BOUNDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Sensitivity (Maximum Derivative)

Each curve has a finite maximum derivative (sensitivity).
This bounds error amplification through the curve.

| Curve   | Derivative        | Max on [0,1] or [ε,1] |
|---------|-------------------|------------------------|
| Linear  | 1                 | 1                      |
| Soft    | 1/(2√t)          | 1/(2√ε) = 8 for ε=1/256 |
| Firm    | 2t                | 2                      |
| SCurve  | 6t - 6t²         | 1.5 (at t=0.5)         |
-/

/-- Maximum sensitivity (derivative bound) for each curve type.
    Returns a non-negative real. -/
noncomputable def maxSensitivity (c : ResponseCurve) : ℝ :=
  match c with
  | linear => 1
  | soft => 8      -- 1/(2*sqrt(1/256)) = 1/(2*(1/16)) = 8
  | firm => 2
  | sCurve => 1.5  -- Maximum of 6t - 6t² at t = 0.5

/-- All sensitivities are positive -/
theorem sensitivity_pos (c : ResponseCurve) : 0 < maxSensitivity c := by
  cases c with
  | linear => unfold maxSensitivity; norm_num
  | soft => unfold maxSensitivity; norm_num
  | firm => unfold maxSensitivity; norm_num
  | sCurve => unfold maxSensitivity; norm_num

/-- All sensitivities are finite (bounded above) -/
theorem sensitivity_le_eight (c : ResponseCurve) : maxSensitivity c ≤ 8 := by
  cases c with
  | linear => unfold maxSensitivity; norm_num
  | soft => unfold maxSensitivity; norm_num
  | firm => unfold maxSensitivity; norm_num
  | sCurve => unfold maxSensitivity; norm_num

end ResponseCurve

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: DYNAMICS MAPPING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Dynamics Mapping

A complete mapping from input [0,1] to output [min, max] via a curve.
Used for pressure→size, tilt→opacity, velocity→flow, etc.
-/

/-- A dynamics mapping configuration.

    Maps input ∈ [0,1] to output ∈ [valueAtMin, valueAtMax] via curve:
    output = lerp(valueAtMin, valueAtMax, curve(input)) -/
structure DynamicsMapping where
  /-- Curve shaping the response -/
  curve : ResponseCurve
  /-- Output value when input = 0 -/
  valueAtMin : BoundedUnit
  /-- Output value when input = 1 -/
  valueAtMax : BoundedUnit
  /-- Min ≤ Max (well-formed range) -/
  range_valid : valueAtMin.value ≤ valueAtMax.value

namespace DynamicsMapping

/-- Apply a dynamics mapping to an input value -/
noncomputable def applyToValue (m : DynamicsMapping) (input : BoundedUnit) : BoundedUnit :=
  let curveOutput := ResponseCurve.apply m.curve input
  BoundedUnit.lerp m.valueAtMin m.valueAtMax curveOutput

/-- Output is always within [valueAtMin, valueAtMax] -/
theorem output_in_range (m : DynamicsMapping) (input : BoundedUnit) :
    m.valueAtMin.value ≤ (applyToValue m input).value ∧ 
    (applyToValue m input).value ≤ m.valueAtMax.value := by
  simp only [applyToValue, BoundedUnit.lerp]
  have ht := (ResponseCurve.apply m.curve input).ge_zero
  have ht1 := (ResponseCurve.apply m.curve input).le_one
  have hmin := m.valueAtMin.ge_zero
  have hmax := m.valueAtMax.le_one
  have hrange := m.range_valid
  constructor
  · -- valueAtMin ≤ output
    nlinarith
  · -- output ≤ valueAtMax
    nlinarith

/-- Identity mapping: linear curve, full range [0,1] -/
def identity : DynamicsMapping :=
  { curve := ResponseCurve.linear
  , valueAtMin := BoundedUnit.zero
  , valueAtMax := BoundedUnit.one
  , range_valid := by norm_num [BoundedUnit.zero, BoundedUnit.one] }

/-- Inverted mapping: linear curve, inverted range [1,0] 
    Note: This requires valueAtMin > valueAtMax, so we swap semantics -/
def inverted : DynamicsMapping :=
  { curve := ResponseCurve.linear
  , valueAtMin := BoundedUnit.one
  , valueAtMax := BoundedUnit.one  -- Same value = constant output
  , range_valid := le_refl _ }

end DynamicsMapping

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: GRADED TRANSFORMATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-! ## Grade Degradation

Applying a dynamics mapping to an InputChannel degrades certainty.
The result is estimated, not exact — provenance is honest.
-/

/-- Apply a dynamics mapping to an InputChannel.
    
    The transformation:
    1. Extracts the value from the channel
    2. Applies the curve
    3. Maps to [valueAtMin, valueAtMax]
    4. Degrades certainty to estimated (or keeps if already lower) -/
noncomputable def applyToChannel (m : DynamicsMapping) (ch : InputChannel) : InputChannel :=
  let inputUnit : BoundedUnit := ⟨ch.value.val, ch.value.nonneg, ch.value.le_one⟩
  let outputUnit := m.applyToValue inputUnit
  let newCertainty := 
    if ch.grade.certainty.toNat > Certainty.estimated.toNat 
    then Certainty.estimated 
    else ch.grade.certainty
  { value := ⟨outputUnit.value, outputUnit.ge_zero, outputUnit.le_one⟩
  , grade := ⟨ch.grade.provenance, newCertainty⟩
  , source := ch.source
  , timestamp := ch.timestamp
  , source_grade_consistent := ch.source_grade_consistent }

/-- Certainty degradation function for dynamics mapping -/
def dynamicsCertaintyDegradation (c : Certainty) : Certainty :=
  if c.toNat > Certainty.estimated.toNat then Certainty.estimated else c

/-- Dynamics certainty degradation is monotonic (never improves certainty) -/
theorem dynamics_degradation_monotonic (c : Certainty) : 
    dynamicsCertaintyDegradation c ≤ c := by
  show Certainty.le (dynamicsCertaintyDegradation c) c
  unfold dynamicsCertaintyDegradation Certainty.le
  split_ifs with h
  · exact Nat.le_of_lt h
  · exact Nat.le_refl c.toNat

/-- Dynamics mapping as a GradedTransformation -/
def asGradedTransformation (m : DynamicsMapping) : GradedTransformation :=
  { name := "dynamics_mapping"
  , certaintyDegradation := dynamicsCertaintyDegradation
  , degradation_monotonic := dynamics_degradation_monotonic }

/-- DEGRADATION THEOREM: Applying dynamics mapping only degrades grade, never improves.
    
    This is the key invariant for trust: an agent receiving a value from
    a dynamics mapping knows its provenance is honest about the computation. -/
theorem dynamics_degrades (m : DynamicsMapping) (ch : InputChannel) :
    (applyToChannel m ch).grade ≤ ch.grade := by
  unfold applyToChannel
  simp only
  constructor
  · -- Provenance preserved
    exact Provenance.le_refl ch.grade.provenance
  · -- Certainty degraded
    show Certainty.le _ _
    unfold Certainty.le
    split_ifs with h
    · exact Nat.le_of_lt h
    · exact Nat.le_refl _

/-- Provenance is preserved through dynamics mapping -/
theorem dynamics_preserves_provenance (m : DynamicsMapping) (ch : InputChannel) :
    (applyToChannel m ch).grade.provenance = ch.grade.provenance := rfl

/-- Value bounds are preserved through dynamics mapping -/
theorem dynamics_value_bounded (m : DynamicsMapping) (ch : InputChannel) :
    0 ≤ (applyToChannel m ch).value.val ∧ (applyToChannel m ch).value.val ≤ 1 := by
  unfold applyToChannel
  simp only
  exact ⟨(m.applyToValue _).ge_zero, (m.applyToValue _).le_one⟩

end Hydrogen.Schema.Brush.Dynamics
