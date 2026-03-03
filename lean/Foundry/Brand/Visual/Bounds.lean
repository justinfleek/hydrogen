-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // foundry // brand // visual // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Bounding Box Type with Proofs
--
-- INVARIANTS PROVEN:
--   bounds_width_nonnegative  : forall b. b.width >= 0
--   bounds_height_nonnegative : forall b. b.height >= 0
--   bounds_area_nonnegative   : forall b. b.width * b.height >= 0
--
-- DESIGN DECISION:
--   We use Nat for dimensions to make non-negativity trivial by construction.
--   Runtime implementations (Haskell/PureScript) use Float with smart constructors.
--
-- DEPENDENCIES:
--   None (standalone module)
--
-- DEPENDENTS:
--   Foundry.Brand.Visual.Element - Uses BoundingBox for element bounds
--   Foundry.Brand.Visual.Layer   - Uses BoundingBox for layer composition
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

namespace Foundry.Brand.Visual.Bounds

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: BOUNDING BOX STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## BoundingBox

A bounding box with position (x, y) and dimensions (width, height).
Width and height use Nat, making non-negativity trivial by construction.
Position uses Int since elements can have negative coordinates.
-/

/-- Bounding box with proven non-negative dimensions.
    x and y can be any integer (negative positions are valid).
    width and height use Nat to guarantee non-negativity by construction. -/
structure BoundingBox where
  x : Int      -- X position (can be negative)
  y : Int      -- Y position (can be negative)
  width : Nat  -- Width >= 0 by construction (Nat is non-negative)
  height : Nat -- Height >= 0 by construction (Nat is non-negative)
deriving Repr, DecidableEq, BEq

namespace BoundingBox

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Create a bounding box at origin with given dimensions -/
def atOrigin (w h : Nat) : BoundingBox :=
  ⟨0, 0, w, h⟩

/-- Create a zero-sized bounding box at a position -/
def point (px py : Int) : BoundingBox :=
  ⟨px, py, 0, 0⟩

/-- Create a unit bounding box at origin -/
def unit : BoundingBox :=
  ⟨0, 0, 1, 1⟩

/-- Create a bounding box from position and dimensions -/
def create (x y : Int) (w h : Nat) : BoundingBox :=
  ⟨x, y, w, h⟩

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Move the bounding box by an offset -/
def translate (b : BoundingBox) (dx dy : Int) : BoundingBox :=
  ⟨b.x + dx, b.y + dy, b.width, b.height⟩

/-- Calculate area (width * height) -/
def area (b : BoundingBox) : Nat :=
  b.width * b.height

/-- Right edge x-coordinate -/
def right (b : BoundingBox) : Int :=
  b.x + b.width

/-- Bottom edge y-coordinate -/
def bottom (b : BoundingBox) : Int :=
  b.y + b.height

/-- Check if a point is inside the bounding box -/
def containsPoint (b : BoundingBox) (px py : Int) : Bool :=
  px >= b.x && px < b.right && py >= b.y && py < b.bottom

/-- Check if this bounding box fully contains another -/
def containsBox (outer inner : BoundingBox) : Bool :=
  inner.x >= outer.x
  && inner.y >= outer.y
  && inner.right <= outer.right
  && inner.bottom <= outer.bottom

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: INVARIANT PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Invariant Proofs

These proofs establish the key invariants that Haskell/PureScript must maintain.
Since width and height are Nat, non-negativity is trivial by construction.
-/

/-- Width is always non-negative (trivial: Nat is non-negative by definition) -/
theorem width_nonneg (b : BoundingBox) : b.width >= 0 :=
  Nat.zero_le b.width

/-- Height is always non-negative (trivial: Nat is non-negative by definition) -/
theorem height_nonneg (b : BoundingBox) : b.height >= 0 :=
  Nat.zero_le b.height

/-- Area is always non-negative -/
theorem area_nonneg (b : BoundingBox) : b.area >= 0 :=
  Nat.zero_le b.area

/-- Translation preserves dimensions -/
theorem translate_preserves_width (b : BoundingBox) (dx dy : Int) :
    (b.translate dx dy).width = b.width := rfl

theorem translate_preserves_height (b : BoundingBox) (dx dy : Int) :
    (b.translate dx dy).height = b.height := rfl

/-- Translation preserves area -/
theorem translate_preserves_area (b : BoundingBox) (dx dy : Int) :
    (b.translate dx dy).area = b.area := rfl

/-- Translation is reversible -/
theorem translate_inverse (b : BoundingBox) (dx dy : Int) :
    (b.translate dx dy).translate (-dx) (-dy) = b := by
  simp only [translate]
  cases b
  simp only [BoundingBox.mk.injEq, and_true]
  omega

/-- Double translation is composition -/
theorem translate_compose (b : BoundingBox) (dx1 dy1 dx2 dy2 : Int) :
    (b.translate dx1 dy1).translate dx2 dy2 = b.translate (dx1 + dx2) (dy1 + dy2) := by
  simp only [translate]
  cases b
  simp only [BoundingBox.mk.injEq, and_true]
  omega

/-- Point bounding box has zero area -/
theorem point_zero_area (px py : Int) :
    (point px py).area = 0 := rfl

/-- Unit bounding box has unit area -/
theorem unit_area : unit.area = 1 := rfl

/-- Zero dimensions means zero area -/
theorem zero_width_zero_area (b : BoundingBox) (h : b.width = 0) :
    b.area = 0 := by
  simp only [area, h, Nat.zero_mul]

theorem zero_height_zero_area (b : BoundingBox) (h : b.height = 0) :
    b.area = 0 := by
  simp only [area, h, Nat.mul_zero]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: BOUNDING BOX COMBINATION
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Union of two bounding boxes (smallest box containing both) -/
def union (a b : BoundingBox) : BoundingBox :=
  let minX := min a.x b.x
  let minY := min a.y b.y
  let maxX := max a.right b.right
  let maxY := max a.bottom b.bottom
  -- Width and height are computed as difference
  -- We use Int.toNat to handle the case where max < min (defensive)
  let w := (maxX - minX).toNat
  let h := (maxY - minY).toNat
  ⟨minX, minY, w, h⟩

/-- Check if two bounding boxes intersect -/
def intersects (a b : BoundingBox) : Bool :=
  a.x < b.right && b.x < a.right && a.y < b.bottom && b.y < a.bottom

end BoundingBox

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: SMART CONSTRUCTOR FOR RUNTIME
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Smart Constructor

For runtime use with signed integers, we provide a smart constructor.
This is the pattern Haskell/PureScript should implement.
-/

/-- Create a bounding box from signed integer inputs.
    Returns None if width or height is negative.
    This smart constructor enforces invariants at runtime. -/
def mkBoundingBox (x y w h : Int) : Option BoundingBox :=
  if w >= 0 && h >= 0 then
    some ⟨x, y, w.toNat, h.toNat⟩
  else
    none

/-- Smart constructor succeeds for valid inputs -/
theorem mkBoundingBox_valid (x y : Int) (w h : Int) (hw : w >= 0) (hh : h >= 0) :
    (mkBoundingBox x y w h).isSome = true := by
  unfold mkBoundingBox
  simp only [ge_iff_le, hw, decide_true, hh, Bool.and_self, ↓reduceIte, Option.isSome_some]

/-- Smart constructor fails for negative width -/
theorem mkBoundingBox_neg_width (x y h w : Int) (hw : w < 0) :
    mkBoundingBox x y w h = none := by
  unfold mkBoundingBox
  have hNotLe : ¬(0 ≤ w) := Int.not_le.mpr hw
  simp only [ge_iff_le, hNotLe, decide_false, Bool.false_and]
  rfl

/-- Smart constructor fails for negative height -/
theorem mkBoundingBox_neg_height (x y w h : Int) (hh : h < 0) :
    mkBoundingBox x y w h = none := by
  unfold mkBoundingBox
  have hNotLe : ¬(0 ≤ h) := Int.not_le.mpr hh
  simp only [ge_iff_le, hNotLe, decide_false, Bool.and_false]
  rfl

/-- Result of smart constructor has correct x position -/
theorem mkBoundingBox_x (x y w h : Int) (hw : w >= 0) (hh : h >= 0) :
    ∃ b : BoundingBox, mkBoundingBox x y w h = some b ∧ b.x = x := by
  refine ⟨⟨x, y, w.toNat, h.toNat⟩, ?_, rfl⟩
  unfold mkBoundingBox
  simp only [ge_iff_le, hw, decide_true, hh, Bool.and_self, ↓reduceIte]

/-- Result of smart constructor has correct y position -/
theorem mkBoundingBox_y (x y w h : Int) (hw : w >= 0) (hh : h >= 0) :
    ∃ b : BoundingBox, mkBoundingBox x y w h = some b ∧ b.y = y := by
  refine ⟨⟨x, y, w.toNat, h.toNat⟩, ?_, rfl⟩
  unfold mkBoundingBox
  simp only [ge_iff_le, hw, decide_true, hh, Bool.and_self, ↓reduceIte]

end Foundry.Brand.Visual.Bounds
