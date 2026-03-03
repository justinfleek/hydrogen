-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // foundry // viewport // clamp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Clamp Function with Proofs
--
-- INVARIANTS PROVEN:
--   clamp_idempotent   : clamp(clamp(x)) = clamp(x)
--   clamp_in_range     : min <= clamp(x, min, max) <= max
--   clamp_preserves    : min <= x <= max → clamp(x) = x
--   clamp_monotonic    : x1 <= x2 → clamp(x1) <= clamp(x2)
--
-- DEPENDENCIES:
--   None (standalone module)
--
-- DEPENDENTS:
--   Foundry.Viewport.Transform - Uses clamp for zoom bounds
--   Dashboard viewport controls
--   Haskell/PureScript implementations
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

namespace Foundry.Viewport.Clamp

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: CLAMP FUNCTION (NAT)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Clamp for Natural Numbers

Clamp a value to a range [min, max].
Note: All proofs require minVal <= maxVal for the range to be valid.
-/

/-- Clamp a natural number to a range -/
def clampNat (x minVal maxVal : Nat) : Nat :=
  if x < minVal then minVal
  else if x > maxVal then maxVal
  else x

namespace ClampNat

/-- Clamp result is at least minVal (when minVal <= maxVal) -/
theorem ge_min (x minVal maxVal : Nat) (h : minVal <= maxVal) :
    clampNat x minVal maxVal >= minVal := by
  simp only [clampNat]
  split
  case isTrue => omega
  case isFalse h1 =>
    split
    case isTrue => omega
    case isFalse h2 => omega

/-- Clamp result is at most maxVal (when minVal <= maxVal) -/
theorem le_max (x minVal maxVal : Nat) (h : minVal <= maxVal) :
    clampNat x minVal maxVal <= maxVal := by
  simp only [clampNat]
  split
  case isTrue => exact h
  case isFalse h1 =>
    split
    case isTrue => omega
    case isFalse h2 => omega

/-- Clamp is in range (when minVal <= maxVal) -/
theorem in_range (x minVal maxVal : Nat) (h : minVal <= maxVal) :
    minVal <= clampNat x minVal maxVal ∧ clampNat x minVal maxVal <= maxVal :=
  ⟨ge_min x minVal maxVal h, le_max x minVal maxVal h⟩

/-- Clamp preserves values already in range -/
theorem preserves_valid (x minVal maxVal : Nat) (hx : minVal <= x ∧ x <= maxVal) :
    clampNat x minVal maxVal = x := by
  simp only [clampNat]
  have hNotLow : ¬(x < minVal) := by omega
  have hNotHigh : ¬(x > maxVal) := by omega
  simp [hNotLow, hNotHigh]

/-- Clamp is idempotent -/
theorem idempotent (x minVal maxVal : Nat) (h : minVal <= maxVal) :
    clampNat (clampNat x minVal maxVal) minVal maxVal = clampNat x minVal maxVal := by
  have hr := in_range x minVal maxVal h
  exact preserves_valid (clampNat x minVal maxVal) minVal maxVal hr

/-- Clamp is monotonic (when minVal <= maxVal) -/
theorem monotonic (x1 x2 minVal maxVal : Nat) (hx : x1 <= x2) (hr : minVal <= maxVal) :
    clampNat x1 minVal maxVal <= clampNat x2 minVal maxVal := by
  simp only [clampNat]
  split
  case isTrue h1 =>
    split
    case isTrue => omega
    case isFalse h2 =>
      split
      case isTrue => exact hr
      case isFalse => omega
  case isFalse h1 =>
    split
    case isTrue h2 =>
      split
      case isTrue => omega
      case isFalse h3 =>
        split
        case isTrue => omega
        case isFalse => omega
    case isFalse h2 =>
      split
      case isTrue => omega
      case isFalse h3 =>
        split
        case isTrue => omega
        case isFalse => omega

/-- Clamping below minimum returns minimum -/
theorem below_returns_min (x minVal maxVal : Nat) (hx : x < minVal) :
    clampNat x minVal maxVal = minVal := by
  simp only [clampNat, hx, ↓reduceIte]

/-- Clamping above maximum returns maximum (when minVal <= maxVal) -/
theorem above_returns_max (x minVal maxVal : Nat) (hx : x > maxVal) (h : minVal <= maxVal) :
    clampNat x minVal maxVal = maxVal := by
  simp only [clampNat]
  have hNotLow : ¬(x < minVal) := by omega
  simp [hNotLow, hx]

end ClampNat

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: CLAMP FUNCTION (INT)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Clamp for Integers

Clamp an integer to a range [min, max].
-/

/-- Clamp an integer to a range -/
def clampInt (x minVal maxVal : Int) : Int :=
  if x < minVal then minVal
  else if x > maxVal then maxVal
  else x

namespace ClampInt

/-- Clamp result is at least minVal (when minVal <= maxVal) -/
theorem ge_min (x minVal maxVal : Int) (h : minVal <= maxVal) :
    clampInt x minVal maxVal >= minVal := by
  simp only [clampInt]
  split
  case isTrue => omega
  case isFalse h1 =>
    split
    case isTrue => omega
    case isFalse h2 => omega

/-- Clamp result is at most maxVal (when minVal <= maxVal) -/
theorem le_max (x minVal maxVal : Int) (h : minVal <= maxVal) :
    clampInt x minVal maxVal <= maxVal := by
  simp only [clampInt]
  split
  case isTrue => exact h
  case isFalse h1 =>
    split
    case isTrue => omega
    case isFalse h2 => omega

/-- Clamp is in range (when minVal <= maxVal) -/
theorem in_range (x minVal maxVal : Int) (h : minVal <= maxVal) :
    minVal <= clampInt x minVal maxVal ∧ clampInt x minVal maxVal <= maxVal :=
  ⟨ge_min x minVal maxVal h, le_max x minVal maxVal h⟩

/-- Clamp preserves values already in range -/
theorem preserves_valid (x minVal maxVal : Int) (hx : minVal <= x ∧ x <= maxVal) :
    clampInt x minVal maxVal = x := by
  simp only [clampInt]
  have hNotLow : ¬(x < minVal) := by omega
  have hNotHigh : ¬(x > maxVal) := by omega
  simp [hNotLow, hNotHigh]

/-- Clamp is idempotent -/
theorem idempotent (x minVal maxVal : Int) (h : minVal <= maxVal) :
    clampInt (clampInt x minVal maxVal) minVal maxVal = clampInt x minVal maxVal := by
  have hr := in_range x minVal maxVal h
  exact preserves_valid (clampInt x minVal maxVal) minVal maxVal hr

/-- Clamp is monotonic (when minVal <= maxVal) -/
theorem monotonic (x1 x2 minVal maxVal : Int) (hx : x1 <= x2) (hr : minVal <= maxVal) :
    clampInt x1 minVal maxVal <= clampInt x2 minVal maxVal := by
  simp only [clampInt]
  split
  case isTrue h1 =>
    split
    case isTrue => omega
    case isFalse h2 =>
      split
      case isTrue => exact hr
      case isFalse => omega
  case isFalse h1 =>
    split
    case isTrue h2 =>
      split
      case isTrue => omega
      case isFalse h3 =>
        split
        case isTrue => omega
        case isFalse => omega
    case isFalse h2 =>
      split
      case isTrue => omega
      case isFalse h3 =>
        split
        case isTrue => omega
        case isFalse => omega

/-- Clamping below minimum returns minimum -/
theorem below_returns_min (x minVal maxVal : Int) (hx : x < minVal) :
    clampInt x minVal maxVal = minVal := by
  simp only [clampInt, hx, ↓reduceIte]

/-- Clamping above maximum returns maximum (when minVal <= maxVal) -/
theorem above_returns_max (x minVal maxVal : Int) (hx : x > maxVal) (h : minVal <= maxVal) :
    clampInt x minVal maxVal = maxVal := by
  simp only [clampInt]
  have hNotLow : ¬(x < minVal) := by omega
  simp [hNotLow, hx]

end ClampInt

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: BOUNDED TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Bounded Integer

An integer with proven bounds.
-/

/-- An integer bounded between minVal and maxVal -/
structure BoundedInt (minVal maxVal : Int) where
  val : Int
  inBounds : minVal <= val ∧ val <= maxVal
deriving Repr, DecidableEq

namespace BoundedInt

/-- Create a bounded integer by clamping -/
def fromInt (minVal maxVal : Int) (h : minVal <= maxVal) (x : Int) : BoundedInt minVal maxVal :=
  ⟨clampInt x minVal maxVal, ClampInt.in_range x minVal maxVal h⟩

/-- Value is at least minimum -/
theorem val_ge_min (b : BoundedInt minVal maxVal) : b.val >= minVal :=
  b.inBounds.1

/-- Value is at most maximum -/
theorem val_le_max (b : BoundedInt minVal maxVal) : b.val <= maxVal :=
  b.inBounds.2

/-- Add to bounded integer (clamped) -/
def add (b : BoundedInt minVal maxVal) (h : minVal <= maxVal) (delta : Int) : BoundedInt minVal maxVal :=
  fromInt minVal maxVal h (b.val + delta)

/-- Subtract from bounded integer (clamped) -/
def sub (b : BoundedInt minVal maxVal) (h : minVal <= maxVal) (delta : Int) : BoundedInt minVal maxVal :=
  fromInt minVal maxVal h (b.val - delta)

end BoundedInt

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: BOUNDED NATURAL
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Bounded Natural

A natural number with proven bounds.
-/

/-- A natural number bounded between minVal and maxVal -/
structure BoundedNat (minVal maxVal : Nat) where
  val : Nat
  inBounds : minVal <= val ∧ val <= maxVal
deriving Repr, DecidableEq

namespace BoundedNat

/-- Create a bounded natural by clamping -/
def fromNat (minVal maxVal : Nat) (h : minVal <= maxVal) (x : Nat) : BoundedNat minVal maxVal :=
  ⟨clampNat x minVal maxVal, ClampNat.in_range x minVal maxVal h⟩

/-- Value is at least minimum -/
theorem val_ge_min (b : BoundedNat minVal maxVal) : b.val >= minVal :=
  b.inBounds.1

/-- Value is at most maximum -/
theorem val_le_max (b : BoundedNat minVal maxVal) : b.val <= maxVal :=
  b.inBounds.2

/-- Value is in bounds -/
theorem val_in_bounds (b : BoundedNat minVal maxVal) : minVal <= b.val ∧ b.val <= maxVal :=
  b.inBounds

end BoundedNat

end Foundry.Viewport.Clamp
