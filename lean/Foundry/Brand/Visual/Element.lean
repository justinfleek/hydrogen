-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // foundry // brand // visual // element
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Visual Element Type with Proofs
--
-- INVARIANTS PROVEN:
--   element_has_valid_bounds  : forall e. e.bounds.width >= 0 ∧ e.bounds.height >= 0
--   element_opacity_bounded   : forall e. 0 <= e.opacity <= 100
--   element_zindex_is_integer : forall e. e.zIndex ∈ ℤ
--
-- DEPENDENCIES:
--   Foundry.Brand.Visual.Bounds - BoundingBox type
--
-- DEPENDENTS:
--   Foundry.Brand.Visual.Layer - Uses VisualElement for layer composition
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Foundry.Brand.Visual.Bounds

namespace Foundry.Brand.Visual.Element

open Foundry.Brand.Visual.Bounds

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: BOUNDED TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Bounded Types

Types with proven bounds for color channels and opacity.
-/

/-- A byte value (0-255) for color channels -/
structure ByteVal where
  val : Nat
  inBounds : val < 256
deriving Repr, DecidableEq

namespace ByteVal

/-- Create a byte, clamping to valid range -/
def fromNat (n : Nat) : ByteVal :=
  if h : n < 256 then
    ⟨n, h⟩
  else
    ⟨255, by native_decide⟩

/-- Zero byte -/
def zero : ByteVal := ⟨0, by native_decide⟩

/-- Max byte -/
def maxVal : ByteVal := ⟨255, by native_decide⟩

/-- Byte is always in valid range -/
theorem inRange (b : ByteVal) : b.val >= 0 ∧ b.val < 256 :=
  ⟨Nat.zero_le b.val, b.inBounds⟩

end ByteVal

/-- Opacity percentage (0-100) -/
structure Opacity where
  val : Nat
  inBounds : val <= 100
deriving Repr, DecidableEq

namespace Opacity

/-- Create an opacity, clamping to valid range -/
def fromNat (n : Nat) : Opacity :=
  if h : n <= 100 then
    ⟨n, h⟩
  else
    ⟨100, by native_decide⟩

/-- Fully transparent -/
def transparent : Opacity := ⟨0, by native_decide⟩

/-- Fully visible (100%) -/
def full : Opacity := ⟨100, by native_decide⟩

/-- Opacity is always in valid range -/
theorem inRange (o : Opacity) : o.val >= 0 ∧ o.val <= 100 :=
  ⟨Nat.zero_le o.val, o.inBounds⟩

end Opacity

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: COLOR TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## RGBA Color

Color with red, green, blue channels (0-255) and alpha (0-100).
All channels are bounded by construction.
-/

/-- RGBA color with proven bounded channels -/
structure RGBA where
  r : ByteVal
  g : ByteVal
  b : ByteVal
  a : Opacity
deriving Repr, DecidableEq

namespace RGBA

/-- Create an opaque color from RGB values -/
def rgb (r g b : Nat) : RGBA :=
  ⟨ByteVal.fromNat r, ByteVal.fromNat g, ByteVal.fromNat b, Opacity.full⟩

/-- Create a color with alpha -/
def rgba (r g b a : Nat) : RGBA :=
  ⟨ByteVal.fromNat r, ByteVal.fromNat g, ByteVal.fromNat b, Opacity.fromNat a⟩

/-- Black (opaque) -/
def black : RGBA := rgb 0 0 0

/-- White (opaque) -/
def white : RGBA := rgb 255 255 255

/-- Fully transparent -/
def clear : RGBA := ⟨ByteVal.zero, ByteVal.zero, ByteVal.zero, Opacity.transparent⟩

/-- All color channels are in valid range -/
theorem channelsInRange (c : RGBA) :
    c.r.val < 256 ∧ c.g.val < 256 ∧ c.b.val < 256 ∧ c.a.val <= 100 :=
  ⟨c.r.inBounds, c.g.inBounds, c.b.inBounds, c.a.inBounds⟩

end RGBA

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: ELEMENT ID (UUID5 PLACEHOLDER)
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Element ID

Unique identifier for visual elements. In production this is UUID5.
For proof purposes we use a simplified string representation.
-/

/-- Element identifier (UUID5 in production) -/
structure ElementId where
  ns : String   -- namespace (avoiding keyword 'namespace')
  name : String
deriving Repr, DecidableEq, BEq

namespace ElementId

/-- Create an element ID from namespace and name -/
def create (ns name : String) : ElementId := ⟨ns, name⟩

/-- Two IDs with same namespace and name are equal -/
theorem eq_of_same_parts (a b : ElementId) (hns : a.ns = b.ns) (hn : a.name = b.name) :
    a = b := by
  cases a; cases b
  simp_all

/-- ID creation is deterministic -/
theorem create_deterministic (ns name : String) :
    ElementId.create ns name = ElementId.create ns name := rfl

end ElementId

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: VISUAL ELEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Visual Element

A visual element extracted from a webpage.
Contains position, dimensions, z-index, and visual properties.
-/

/-- Visual element with all properties bounded by construction -/
structure VisualElement where
  id : ElementId
  bounds : BoundingBox
  zIndex : Int
  backgroundColor : Option RGBA
  borderColor : Option RGBA
  textColor : Option RGBA
  opacity : Opacity
deriving Repr, DecidableEq

namespace VisualElement

/-- Create a basic element with just position and dimensions -/
def create (id : ElementId) (bounds : BoundingBox) (zIndex : Int) : VisualElement :=
  ⟨id, bounds, zIndex, none, none, none, Opacity.full⟩

/-- Create an element with background color -/
def withBackground (e : VisualElement) (color : RGBA) : VisualElement :=
  { e with backgroundColor := some color }

/-- Create an element with opacity -/
def withOpacity (e : VisualElement) (op : Opacity) : VisualElement :=
  { e with opacity := op }

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: VISUAL ELEMENT INVARIANT PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Element bounds width is non-negative (from BoundingBox) -/
theorem bounds_width_nonneg (e : VisualElement) : e.bounds.width >= 0 :=
  BoundingBox.width_nonneg e.bounds

/-- Element bounds height is non-negative (from BoundingBox) -/
theorem bounds_height_nonneg (e : VisualElement) : e.bounds.height >= 0 :=
  BoundingBox.height_nonneg e.bounds

/-- Element has valid bounds -/
theorem has_valid_bounds (e : VisualElement) :
    e.bounds.width >= 0 ∧ e.bounds.height >= 0 :=
  ⟨bounds_width_nonneg e, bounds_height_nonneg e⟩

/-- Element opacity is bounded (0-100) -/
theorem opacity_bounded (e : VisualElement) : e.opacity.val <= 100 :=
  e.opacity.inBounds

/-- Element z-index is an integer (trivial: Int by construction) -/
theorem zindex_is_int (e : VisualElement) : ∃ n : Int, e.zIndex = n :=
  ⟨e.zIndex, rfl⟩

/-- Background color channels are bounded when present -/
theorem backgroundColor_bounded (e : VisualElement) :
    ∀ c, e.backgroundColor = some c →
      c.r.val < 256 ∧ c.g.val < 256 ∧ c.b.val < 256 ∧ c.a.val <= 100 :=
  fun c _ => RGBA.channelsInRange c

/-- withBackground preserves other properties -/
theorem withBackground_preserves_id (e : VisualElement) (c : RGBA) :
    (e.withBackground c).id = e.id := rfl

theorem withBackground_preserves_bounds (e : VisualElement) (c : RGBA) :
    (e.withBackground c).bounds = e.bounds := rfl

theorem withBackground_preserves_zIndex (e : VisualElement) (c : RGBA) :
    (e.withBackground c).zIndex = e.zIndex := rfl

/-- withOpacity preserves other properties -/
theorem withOpacity_preserves_id (e : VisualElement) (o : Opacity) :
    (e.withOpacity o).id = e.id := rfl

theorem withOpacity_preserves_bounds (e : VisualElement) (o : Opacity) :
    (e.withOpacity o).bounds = e.bounds := rfl

theorem withOpacity_preserves_zIndex (e : VisualElement) (o : Opacity) :
    (e.withOpacity o).zIndex = e.zIndex := rfl

end VisualElement

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: ELEMENT ORDERING
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Element Ordering

Ordering for visual elements based on z-index for painter's algorithm.
-/

/-- Compare elements by z-index -/
def compareByZIndex (a b : VisualElement) : Ordering :=
  compare a.zIndex b.zIndex

/-- Element with lower z-index renders first (painter's algorithm) -/
def rendersBefore (a b : VisualElement) : Prop :=
  a.zIndex < b.zIndex

/-- rendersBefore is transitive -/
theorem rendersBefore_trans (a b c : VisualElement)
    (hab : rendersBefore a b) (hbc : rendersBefore b c) :
    rendersBefore a c := by
  unfold rendersBefore at *
  omega

/-- rendersBefore is irreflexive -/
theorem rendersBefore_irrefl (a : VisualElement) :
    ¬rendersBefore a a := by
  unfold rendersBefore
  omega

/-- rendersBefore is asymmetric -/
theorem rendersBefore_asymm (a b : VisualElement)
    (hab : rendersBefore a b) :
    ¬rendersBefore b a := by
  unfold rendersBefore at *
  omega

end Foundry.Brand.Visual.Element
