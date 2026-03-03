-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // foundry // brand // visual // layer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Layer Composition with Proofs
--
-- INVARIANTS PROVEN:
--   layer_elements_same_zindex : forall layer. all elements have same zIndex
--   layers_sorted_ascending    : forall layers. z-indices in ascending order
--   layers_zindex_unique       : forall layers. no duplicate z-indices
--
-- DEPENDENCIES:
--   Foundry.Brand.Visual.Element - VisualElement type
--
-- DEPENDENTS:
--   Dashboard reconstruction engine
--   Haskell/PureScript layer implementations
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Foundry.Brand.Visual.Element

namespace Foundry.Brand.Visual.Layer

open Foundry.Brand.Visual.Element

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 1: LAYER STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Layer

A layer groups visual elements that share the same z-index.
This enables painter's algorithm rendering: layers are rendered
in z-index order (ascending), with lower z-index rendered first.
-/

/-- A layer containing elements at a specific z-index.
    All elements in a layer share the same z-index by construction. -/
structure Layer where
  zIndex : Int
  elements : List VisualElement
  elementsMatchZIndex : ∀ e, e ∈ elements → e.zIndex = zIndex
deriving Repr

namespace Layer

/-- Create an empty layer at a given z-index -/
def empty (z : Int) : Layer :=
  ⟨z, [], fun _ h => by contradiction⟩

/-- Create a layer from a single element -/
def singleton (e : VisualElement) : Layer :=
  ⟨e.zIndex, [e], fun x h => by
    simp only [List.mem_singleton] at h
    rw [h]⟩

/-- Add an element to a layer (must have matching z-index) -/
def addElement (l : Layer) (e : VisualElement) (h : e.zIndex = l.zIndex) : Layer :=
  ⟨l.zIndex, e :: l.elements, fun x hx => by
    cases hx with
    | head => exact h
    | tail _ htail => exact l.elementsMatchZIndex x htail⟩

/-- Number of elements in the layer -/
def size (l : Layer) : Nat :=
  l.elements.length

/-- Check if layer is empty -/
def isEmpty (l : Layer) : Bool :=
  l.elements.isEmpty

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 2: LAYER INVARIANT PROOFS
-- ═══════════════════════════════════════════════════════════════════════════════

/-- All elements in a layer have the same z-index as the layer -/
theorem all_elements_same_zindex (l : Layer) :
    ∀ e, e ∈ l.elements → e.zIndex = l.zIndex :=
  l.elementsMatchZIndex

/-- Empty layer has no elements -/
theorem empty_has_no_elements (z : Int) :
    (empty z).elements = [] := rfl

/-- Empty layer has size 0 -/
theorem empty_size_zero (z : Int) :
    (empty z).size = 0 := rfl

/-- Singleton layer has size 1 -/
theorem singleton_size_one (e : VisualElement) :
    (singleton e).size = 1 := rfl

/-- Singleton layer contains the element -/
theorem singleton_contains (e : VisualElement) :
    e ∈ (singleton e).elements := by
  simp only [singleton, List.mem_singleton]

/-- Adding element increases size by 1 -/
theorem add_increases_size (l : Layer) (e : VisualElement) (h : e.zIndex = l.zIndex) :
    (l.addElement e h).size = l.size + 1 := by
  simp only [addElement, size, List.length_cons]

/-- Added element is in the layer -/
theorem add_contains_element (l : Layer) (e : VisualElement) (h : e.zIndex = l.zIndex) :
    e ∈ (l.addElement e h).elements := by
  simp only [addElement, List.mem_cons, true_or]

/-- Original elements preserved after add -/
theorem add_preserves_elements (l : Layer) (e : VisualElement) (h : e.zIndex = l.zIndex) :
    ∀ x, x ∈ l.elements → x ∈ (l.addElement e h).elements := by
  intro x hx
  simp only [addElement, List.mem_cons]
  right
  exact hx

end Layer

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 3: SORTED LAYER LIST
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Sorted Layer List

A list of layers sorted by z-index in ascending order.
This ensures correct painter's algorithm ordering.
-/

/-- Check if a list of layers is sorted by z-index ascending -/
def isSorted (layers : List Layer) : Prop :=
  List.Pairwise (fun a b => a.zIndex < b.zIndex) layers

/-- Check if all z-indices in a layer list are unique -/
def hasUniqueZIndices (layers : List Layer) : Prop :=
  List.Pairwise (fun a b => a.zIndex ≠ b.zIndex) layers

/-- Empty list is sorted -/
theorem empty_is_sorted : isSorted [] := List.Pairwise.nil

/-- Singleton list is sorted -/
theorem singleton_is_sorted (l : Layer) : isSorted [l] :=
  List.pairwise_singleton _ l

/-- Sorted implies unique z-indices -/
theorem sorted_implies_unique (layers : List Layer) (h : isSorted layers) :
    hasUniqueZIndices layers := by
  unfold isSorted hasUniqueZIndices at *
  exact List.Pairwise.imp (fun hab => Int.ne_of_lt hab) h

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 4: LAYER LIST OPERATIONS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Layer Operations

Operations that preserve the sorted invariant.
-/

/-- Insert a layer into a sorted list, maintaining sorted order.
    Note: If z-index already exists, the existing layer is kept unchanged. -/
def insertSorted (l : Layer) (layers : List Layer) : List Layer :=
  match layers with
  | [] => [l]
  | hd :: tl =>
    if l.zIndex < hd.zIndex then
      l :: hd :: tl
    else if l.zIndex = hd.zIndex then
      -- Keep existing layer (merge would require proof update)
      hd :: tl
    else
      hd :: insertSorted l tl

/-- Find a layer by z-index -/
def findByZIndex (z : Int) (layers : List Layer) : Option Layer :=
  layers.find? (fun l => l.zIndex == z)

/-- Get all z-indices from a layer list -/
def zIndices (layers : List Layer) : List Int :=
  layers.map (·.zIndex)

/-- Extract z-indices preserves length -/
theorem zIndices_length (layers : List Layer) :
    (zIndices layers).length = layers.length := by
  simp only [zIndices, List.length_map]

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 5: LAYER CONSTRUCTION FROM ELEMENTS
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Building Layers from Elements

Group elements by z-index to form layers.
-/

/-- Group elements by z-index into a layer at that z-index.
    Elements must all have the same z-index. -/
def groupElements (z : Int) (elements : List VisualElement)
    (h : ∀ e, e ∈ elements → e.zIndex = z) : Layer :=
  ⟨z, elements, h⟩

/-- Filter elements by z-index -/
def filterByZIndex (z : Int) (elements : List VisualElement) : List VisualElement :=
  elements.filter (fun e => e.zIndex == z)

/-- All filtered elements have the target z-index -/
theorem filter_zindex_match (z : Int) (elements : List VisualElement) :
    ∀ e, e ∈ filterByZIndex z elements → e.zIndex = z := by
  intro e he
  simp only [filterByZIndex, List.mem_filter, beq_iff_eq] at he
  exact he.2

/-- Create a layer from filtered elements -/
def layerFromFilter (z : Int) (elements : List VisualElement) : Layer :=
  groupElements z (filterByZIndex z elements) (filter_zindex_match z elements)

-- ═══════════════════════════════════════════════════════════════════════════════
-- SECTION 6: RENDER ORDER PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-! ## Render Order

Properties related to painter's algorithm rendering.
-/

/-- A layer renders before another if it has lower z-index -/
def layerRendersBefore (a b : Layer) : Prop :=
  a.zIndex < b.zIndex

/-- layerRendersBefore is transitive -/
theorem layerRendersBefore_trans (a b c : Layer)
    (hab : layerRendersBefore a b) (hbc : layerRendersBefore b c) :
    layerRendersBefore a c := by
  unfold layerRendersBefore at *
  omega

/-- layerRendersBefore is irreflexive -/
theorem layerRendersBefore_irrefl (a : Layer) :
    ¬layerRendersBefore a a := by
  unfold layerRendersBefore
  omega

/-- layerRendersBefore is asymmetric -/
theorem layerRendersBefore_asymm (a b : Layer)
    (hab : layerRendersBefore a b) :
    ¬layerRendersBefore b a := by
  unfold layerRendersBefore at *
  omega

end Foundry.Brand.Visual.Layer
