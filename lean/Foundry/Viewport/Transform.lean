-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // foundry // viewport // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Viewport Transform with Proofs
--
-- INVARIANTS PROVEN:
--   zoom_bounded            : forall v. 25 <= v.zoom <= 400 (percent)
--   pan_inverse             : pan can be reversed
--   pan_zero                : pan with zero is identity
--
-- DEPENDENCIES:
--   None (standalone module)
--
-- DEPENDENTS:
--   Dashboard viewport controls
--   Haskell/PureScript viewport implementations
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

namespace Foundry.Viewport.Transform

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: BOUNDED ZOOM LEVEL
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Zoom Level

Zoom is bounded between 25% (0.25x) and 400% (4.0x).
We represent as percentage (25-400) for integer arithmetic.
-/

/-- Zoom level as percentage (25 = 0.25x, 100 = 1.0x, 400 = 4.0x) -/
structure ZoomLevel where
  percent : Nat
  inBounds : 25 <= percent ∧ percent <= 400
deriving Repr, DecidableEq

namespace ZoomLevel

/-- Clamp a natural number to the zoom range -/
def clamp (p : Nat) : Nat :=
  if p < 25 then 25
  else if p > 400 then 400
  else p

/-- Clamp always returns a value in range -/
theorem clamp_in_range (p : Nat) : 25 <= clamp p ∧ clamp p <= 400 := by
  simp only [clamp]
  split
  · omega
  · split
    · omega
    · omega

/-- Create a zoom level, clamping to valid range -/
def fromPercent (p : Nat) : ZoomLevel :=
  ⟨clamp p, clamp_in_range p⟩

/-- Default zoom (100%) -/
def default : ZoomLevel := ⟨100, by omega⟩

/-- Minimum zoom (25%) -/
def minZoom : ZoomLevel := ⟨25, by omega⟩

/-- Maximum zoom (400%) -/
def maxZoom : ZoomLevel := ⟨400, by omega⟩

/-- Check if at minimum -/
def isMin (z : ZoomLevel) : Bool := z.percent == 25

/-- Check if at maximum -/
def isMax (z : ZoomLevel) : Bool := z.percent == 400

/-- Zoom in by adding 25 percentage points (clamped) -/
def zoomIn (z : ZoomLevel) : ZoomLevel :=
  fromPercent (z.percent + 25)

/-- Zoom out by subtracting 25 percentage points (clamped) -/
def zoomOut (z : ZoomLevel) : ZoomLevel :=
  fromPercent (if z.percent >= 25 then z.percent - 25 else 0)

/-- Reset to default (100%) -/
def reset (_ : ZoomLevel) : ZoomLevel := default

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: ZOOM INVARIANT PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zoom is always at least minimum -/
theorem zoom_ge_min (z : ZoomLevel) : z.percent >= 25 :=
  z.inBounds.1

/-- Zoom is always at most maximum -/
theorem zoom_le_max (z : ZoomLevel) : z.percent <= 400 :=
  z.inBounds.2

/-- Zoom is always in valid range -/
theorem zoom_in_range (z : ZoomLevel) : 25 <= z.percent ∧ z.percent <= 400 :=
  z.inBounds

/-- zoomIn result is always in range -/
theorem zoomIn_in_range (z : ZoomLevel) :
    25 <= (zoomIn z).percent ∧ (zoomIn z).percent <= 400 :=
  (zoomIn z).inBounds

/-- zoomOut result is always in range -/
theorem zoomOut_in_range (z : ZoomLevel) :
    25 <= (zoomOut z).percent ∧ (zoomOut z).percent <= 400 :=
  (zoomOut z).inBounds

/-- Reset returns to default -/
theorem reset_is_default (z : ZoomLevel) :
    (reset z).percent = 100 := rfl

/-- clamp with valid input returns that value -/
theorem clamp_valid (p : Nat) (h : 25 <= p ∧ p <= 400) :
    clamp p = p := by
  simp only [clamp]
  have hNotLow : ¬(p < 25) := by omega
  have hNotHigh : ¬(p > 400) := by omega
  simp [hNotLow, hNotHigh]

/-- fromPercent with valid input returns that value -/
theorem fromPercent_valid (p : Nat) (h : 25 <= p ∧ p <= 400) :
    (fromPercent p).percent = p := by
  simp only [fromPercent]
  exact clamp_valid p h

end ZoomLevel

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: TRANSFORM TYPE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Transform

A 2D affine transform for viewport pan and zoom.
We only support uniform scaling (zoom) and translation (pan).
-/

/-- 2D viewport transform with zoom and pan.
    Represents: scale(zoom) then translate(panX, panY) -/
structure Transform where
  zoom : ZoomLevel
  panX : Int
  panY : Int
deriving Repr, DecidableEq

namespace Transform

/-- Identity transform (no zoom, no pan) -/
def identity : Transform :=
  ⟨ZoomLevel.default, 0, 0⟩

/-- Create a transform with just zoom -/
def fromZoom (z : ZoomLevel) : Transform :=
  ⟨z, 0, 0⟩

/-- Create a transform with just pan -/
def fromPan (px py : Int) : Transform :=
  ⟨ZoomLevel.default, px, py⟩

/-- Apply zoom in -/
def applyZoomIn (t : Transform) : Transform :=
  { t with zoom := t.zoom.zoomIn }

/-- Apply zoom out -/
def applyZoomOut (t : Transform) : Transform :=
  { t with zoom := t.zoom.zoomOut }

/-- Apply zoom reset -/
def applyZoomReset (t : Transform) : Transform :=
  { t with zoom := ZoomLevel.default }

/-- Apply pan -/
def applyPan (t : Transform) (dx dy : Int) : Transform :=
  { t with panX := t.panX + dx, panY := t.panY + dy }

/-- Reset to identity -/
def resetToIdentity (_ : Transform) : Transform := identity

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: TRANSFORM INVARIANT PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Zoom is always bounded -/
theorem zoom_bounded (t : Transform) :
    25 <= t.zoom.percent ∧ t.zoom.percent <= 400 :=
  t.zoom.inBounds

/-- Identity has 100% zoom -/
theorem identity_zoom : identity.zoom.percent = 100 := rfl

/-- Identity has no pan -/
theorem identity_no_pan : identity.panX = 0 ∧ identity.panY = 0 :=
  ⟨rfl, rfl⟩

/-- Applying pan with zero offset is identity -/
theorem pan_zero (t : Transform) : applyPan t 0 0 = t := by
  simp only [applyPan, Int.add_zero]

/-- Pan is reversible (panX component) -/
theorem pan_inverse_x (t : Transform) (dx dy : Int) :
    (applyPan (applyPan t dx dy) (-dx) (-dy)).panX = t.panX := by
  simp only [applyPan]
  omega

/-- Pan is reversible (panY component) -/
theorem pan_inverse_y (t : Transform) (dx dy : Int) :
    (applyPan (applyPan t dx dy) (-dx) (-dy)).panY = t.panY := by
  simp only [applyPan]
  omega

/-- Pan is reversible (zoom preserved) -/
theorem pan_inverse_zoom (t : Transform) (dx dy : Int) :
    (applyPan (applyPan t dx dy) (-dx) (-dy)).zoom = t.zoom := rfl

/-- zoomIn preserves pan -/
theorem zoomIn_preserves_pan (t : Transform) :
    (applyZoomIn t).panX = t.panX ∧ (applyZoomIn t).panY = t.panY :=
  ⟨rfl, rfl⟩

/-- zoomOut preserves pan -/
theorem zoomOut_preserves_pan (t : Transform) :
    (applyZoomOut t).panX = t.panX ∧ (applyZoomOut t).panY = t.panY :=
  ⟨rfl, rfl⟩

/-- pan preserves zoom -/
theorem pan_preserves_zoom (t : Transform) (dx dy : Int) :
    (applyPan t dx dy).zoom = t.zoom := rfl

/-- resetToIdentity returns identity -/
theorem reset_returns_identity (t : Transform) :
    resetToIdentity t = identity := rfl

/-- After zoom reset, zoom is 100% -/
theorem zoomReset_is_default (t : Transform) :
    (applyZoomReset t).zoom.percent = 100 := rfl

end Transform

end Foundry.Viewport.Transform
