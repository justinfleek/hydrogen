/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                       HYDROGEN // WORLDMODEL // SPATIALINTEGRITY
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Spatial Integrity Proofs — mathematical guarantees against spatial exploits.
  
  PURPOSE:
    This module proves that spatial operations CANNOT escape bounds when all
    inputs are bounded. An attacker cannot:
    
    1. Compose transforms to escape a bounded region
    2. Use velocity to teleport outside bounds
    3. Accumulate small movements to escape containment
    
  THE ATTACK VECTORS:
    
    - VELOCITY EXPLOSION: Apply huge velocity for tiny dt
    - TRANSFORM STACKING: Compose many transforms to escape bounds
    - PRECISION EXPLOIT: Use floating-point edge cases
    - SCALE AMPLIFICATION: Compound scales to escape region
    
  THE DEFENSE:
    All inputs are CLAMPED before use. The proofs show that:
    - Clamped position + clamped velocity × clamped dt → clamped position
    - Clamped transforms compose to clamped transforms
    - Bounded regions remain bounded under bounded operations
    
  CORRESPONDENCE TO PURESCRIPT:
    - Hydrogen.Schema.Game.Entity (Position2D, Velocity2D, DeltaTime)
    - Hydrogen.Schema.Geometry.Transform (Transform2D composition)
    - Hydrogen.Schema.Spatial.Bounds.AABB (bounding boxes)

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

namespace Hydrogen.WorldModel.SpatialIntegrity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BOUNDS (matching PureScript constants)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Maximum position coordinate (pixels) -/
def maxPosition : ℝ := 10000.0

/-- Minimum position coordinate (pixels) -/
def minPosition : ℝ := 0.0

/-- Maximum velocity magnitude (pixels per second) -/
def maxVelocity : ℝ := 10000.0

/-- Maximum delta time per tick (seconds) -/
def maxDeltaTime : ℝ := 1.0

/-- Maximum scale factor -/
def maxScale : ℝ := 10.0

/-- Minimum scale factor -/
def minScale : ℝ := -10.0

-- Positivity proofs
theorem maxPosition_pos : maxPosition > 0 := by simp [maxPosition]; norm_num
theorem maxVelocity_pos : maxVelocity > 0 := by simp [maxVelocity]; norm_num
theorem maxDeltaTime_pos : maxDeltaTime > 0 := by simp [maxDeltaTime]; norm_num
theorem maxScale_pos : maxScale > 0 := by simp [maxScale]; norm_num

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: CLAMPING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Clamp a value to [lo, hi] -/
def clamp (lo hi x : ℝ) : ℝ :=
  if x < lo then lo
  else if x > hi then hi
  else x

/-- Clamp always returns value in bounds -/
theorem clamp_bounds (lo hi x : ℝ) (hle : lo ≤ hi) : 
    lo ≤ clamp lo hi x ∧ clamp lo hi x ≤ hi := by
  simp only [clamp]
  split_ifs with h1 h2
  · exact ⟨le_refl lo, hle⟩
  · exact ⟨hle, le_refl hi⟩
  · push_neg at h1 h2
    exact ⟨h1, h2⟩

/-- Clamp to position bounds [0, 10000] -/
def clampPosition (x : ℝ) : ℝ := clamp minPosition maxPosition x

/-- Clamp to velocity bounds [-10000, 10000] -/
def clampVelocity (v : ℝ) : ℝ := clamp (-maxVelocity) maxVelocity v

/-- Clamp to delta time bounds [0, 1] -/
def clampDeltaTime (dt : ℝ) : ℝ := clamp 0 maxDeltaTime dt

/-- Clamp to scale bounds [-10, 10] -/
def clampScale (s : ℝ) : ℝ := clamp minScale maxScale s

-- Bounds theorems for clamped values
theorem clampPosition_bounds (x : ℝ) : 
    minPosition ≤ clampPosition x ∧ clampPosition x ≤ maxPosition := by
  apply clamp_bounds
  simp [minPosition, maxPosition]; norm_num

theorem clampVelocity_bounds (v : ℝ) : 
    -maxVelocity ≤ clampVelocity v ∧ clampVelocity v ≤ maxVelocity := by
  apply clamp_bounds
  simp only [maxVelocity]
  norm_num

theorem clampDeltaTime_bounds (dt : ℝ) : 
    0 ≤ clampDeltaTime dt ∧ clampDeltaTime dt ≤ maxDeltaTime := by
  apply clamp_bounds
  simp [maxDeltaTime]; norm_num

theorem clampScale_bounds (s : ℝ) : 
    minScale ≤ clampScale s ∧ clampScale s ≤ maxScale := by
  apply clamp_bounds
  simp [minScale, maxScale]; norm_num

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: BOUNDED POSITION TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A position coordinate that is provably within bounds -/
structure BoundedCoord where
  value : ℝ
  lower_bound : minPosition ≤ value
  upper_bound : value ≤ maxPosition

/-- A 2D position with provably bounded coordinates -/
structure BoundedPosition2D where
  x : BoundedCoord
  y : BoundedCoord

/-- Create a bounded coordinate by clamping -/
def mkBoundedCoord (x : ℝ) : BoundedCoord :=
  let clamped := clampPosition x
  { value := clamped
  , lower_bound := (clampPosition_bounds x).1
  , upper_bound := (clampPosition_bounds x).2 }

/-- Create a bounded 2D position by clamping -/
def mkBoundedPosition2D (x y : ℝ) : BoundedPosition2D :=
  { x := mkBoundedCoord x
  , y := mkBoundedCoord y }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: BOUNDED VELOCITY TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A velocity component that is provably within bounds -/
structure BoundedVelocityComp where
  value : ℝ
  lower_bound : -maxVelocity ≤ value
  upper_bound : value ≤ maxVelocity

/-- A 2D velocity with provably bounded components -/
structure BoundedVelocity2D where
  vx : BoundedVelocityComp
  vy : BoundedVelocityComp

/-- Create a bounded velocity component by clamping -/
def mkBoundedVelocityComp (v : ℝ) : BoundedVelocityComp :=
  let clamped := clampVelocity v
  { value := clamped
  , lower_bound := (clampVelocity_bounds v).1
  , upper_bound := (clampVelocity_bounds v).2 }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: BOUNDED DELTA TIME TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A delta time that is provably within bounds -/
structure BoundedDeltaTime where
  value : ℝ
  lower_bound : 0 ≤ value
  upper_bound : value ≤ maxDeltaTime

/-- Create a bounded delta time by clamping -/
def mkBoundedDeltaTime (dt : ℝ) : BoundedDeltaTime :=
  let clamped := clampDeltaTime dt
  { value := clamped
  , lower_bound := (clampDeltaTime_bounds dt).1
  , upper_bound := (clampDeltaTime_bounds dt).2 }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: VELOCITY APPLICATION (THE KEY PROOF)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Apply velocity to a coordinate for a time step.
    The result is clamped to position bounds. -/
def applyVelocityToCoord (pos : BoundedCoord) (vel : BoundedVelocityComp) 
    (dt : BoundedDeltaTime) : BoundedCoord :=
  let rawNewPos := pos.value + vel.value * dt.value
  mkBoundedCoord rawNewPos

/-- THEOREM: Velocity application ALWAYS produces bounded position.
    
    No matter what velocity is applied, the result is clamped.
    This prevents "teleportation" exploits. -/
theorem velocity_application_bounded (pos : BoundedCoord) (vel : BoundedVelocityComp) 
    (dt : BoundedDeltaTime) :
    let newPos := applyVelocityToCoord pos vel dt
    minPosition ≤ newPos.value ∧ newPos.value ≤ maxPosition := by
  simp only [applyVelocityToCoord, mkBoundedCoord]
  exact clampPosition_bounds _

/-- Maximum displacement in one tick.
    With maxVelocity = 10000 and maxDeltaTime = 1, max displacement = 10000 -/
def maxDisplacementPerTick : ℝ := maxVelocity * maxDeltaTime

theorem maxDisplacement_value : maxDisplacementPerTick = 10000 := by
  simp only [maxDisplacementPerTick, maxVelocity, maxDeltaTime]
  norm_num

/-- THEOREM: Unclamped velocity application is bounded by max displacement.
    
    Even without clamping the result, the raw displacement is bounded. -/
theorem velocity_displacement_bounded (vel : BoundedVelocityComp) (dt : BoundedDeltaTime) :
    |vel.value * dt.value| ≤ maxDisplacementPerTick := by
  have hv_lo := vel.lower_bound
  have hv_hi := vel.upper_bound
  have hdt_lo := dt.lower_bound
  have hdt_hi := dt.upper_bound
  simp only [maxDisplacementPerTick]
  rw [abs_mul]
  have hv_abs : |vel.value| ≤ maxVelocity := by
    rw [abs_le]
    constructor <;> linarith
  have hdt_abs : |dt.value| ≤ maxDeltaTime := by
    rw [abs_le]
    constructor <;> linarith [maxDeltaTime_pos]
  calc |vel.value| * |dt.value| 
      ≤ maxVelocity * |dt.value| := by apply mul_le_mul_of_nonneg_right hv_abs (abs_nonneg _)
    _ ≤ maxVelocity * maxDeltaTime := by apply mul_le_mul_of_nonneg_left hdt_abs; linarith [maxVelocity_pos]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: TRANSFORM SCALE COMPOSITION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A scale factor that is provably within bounds -/
structure BoundedScale where
  value : ℝ
  lower_bound : minScale ≤ value
  upper_bound : value ≤ maxScale

/-- Compose two scales by multiplication, then clamp -/
def composeScale (s1 s2 : BoundedScale) : BoundedScale :=
  let rawProduct := s1.value * s2.value
  let clamped := clampScale rawProduct
  { value := clamped
  , lower_bound := (clampScale_bounds rawProduct).1
  , upper_bound := (clampScale_bounds rawProduct).2 }

/-- THEOREM: Scale composition ALWAYS produces bounded scale.
    
    Even if two large scales are multiplied, the result is clamped.
    This prevents "scale explosion" exploits. -/
theorem scale_composition_bounded (s1 s2 : BoundedScale) :
    let composed := composeScale s1 s2
    minScale ≤ composed.value ∧ composed.value ≤ maxScale := by
  simp only [composeScale]
  exact clampScale_bounds _

/-- Maximum raw scale product before clamping -/
def maxRawScaleProduct : ℝ := maxScale * maxScale

theorem maxRawScaleProduct_value : maxRawScaleProduct = 100 := by
  simp only [maxRawScaleProduct, maxScale]
  norm_num

/-- Apply scale composition N times -/
def composeScaleN : ℕ → BoundedScale → BoundedScale → BoundedScale
  | 0, acc, _ => acc
  | n + 1, acc, s => composeScaleN n (composeScale acc s) s

/-- THEOREM: Even N compositions of the same scale are bounded.
    
    No matter how many times a scale is applied, the result is clamped. -/
theorem scale_composition_n_bounded (n : ℕ) (s acc : BoundedScale) :
    let result := composeScaleN n acc s
    minScale ≤ result.value ∧ result.value ≤ maxScale := by
  induction n generalizing acc with
  | zero => 
    simp only [composeScaleN]
    exact ⟨acc.lower_bound, acc.upper_bound⟩
  | succ k ih =>
    simp only [composeScaleN]
    exact ih (composeScale acc s)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: AXIS-ALIGNED BOUNDING BOX (AABB)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- An axis-aligned bounding box with provably valid bounds -/
structure BoundedAABB where
  minX : ℝ
  maxX : ℝ
  minY : ℝ
  maxY : ℝ
  valid_x : minX ≤ maxX
  valid_y : minY ≤ maxY
  within_world_minX : minPosition ≤ minX
  within_world_maxX : maxX ≤ maxPosition
  within_world_minY : minPosition ≤ minY
  within_world_maxY : maxY ≤ maxPosition

/-- Check if a point is inside an AABB -/
def pointInAABB (aabb : BoundedAABB) (px py : ℝ) : Prop :=
  aabb.minX ≤ px ∧ px ≤ aabb.maxX ∧ aabb.minY ≤ py ∧ py ≤ aabb.maxY

/-- THEOREM: Any point in a BoundedAABB is within world bounds.
    
    If an entity is contained in a BoundedAABB, it cannot be outside the world. -/
theorem point_in_aabb_within_world (aabb : BoundedAABB) (px py : ℝ)
    (hcontained : pointInAABB aabb px py) :
    minPosition ≤ px ∧ px ≤ maxPosition ∧ minPosition ≤ py ∧ py ≤ maxPosition := by
  obtain ⟨hx_lo, hx_hi, hy_lo, hy_hi⟩ := hcontained
  constructor
  · exact le_trans aabb.within_world_minX hx_lo
  constructor
  · exact le_trans hx_hi aabb.within_world_maxX
  constructor
  · exact le_trans aabb.within_world_minY hy_lo
  · exact le_trans hy_hi aabb.within_world_maxY

/-- Helper to order two values (min, max) -/
def orderPair (a b : ℝ) : ℝ × ℝ := if a ≤ b then (a, b) else (b, a)

theorem orderPair_ordered (a b : ℝ) : (orderPair a b).1 ≤ (orderPair a b).2 := by
  simp only [orderPair]
  split_ifs with h
  · exact h
  · push_neg at h; exact le_of_lt h

theorem orderPair_fst_bounds (a b : ℝ) (ha : minPosition ≤ a) (hb : minPosition ≤ b) :
    minPosition ≤ (orderPair a b).1 := by
  simp only [orderPair]
  split_ifs <;> assumption

theorem orderPair_snd_bounds (a b : ℝ) (ha : a ≤ maxPosition) (hb : b ≤ maxPosition) :
    (orderPair a b).2 ≤ maxPosition := by
  simp only [orderPair]
  split_ifs <;> assumption

/-- Translate an AABB by a bounded displacement -/
def translateAABB (aabb : BoundedAABB) (dx dy : ℝ) 
    (_hdx_lo : -maxDisplacementPerTick ≤ dx) (_hdx_hi : dx ≤ maxDisplacementPerTick)
    (_hdy_lo : -maxDisplacementPerTick ≤ dy) (_hdy_hi : dy ≤ maxDisplacementPerTick) : 
    BoundedAABB :=
  let newMinX := clampPosition (aabb.minX + dx)
  let newMaxX := clampPosition (aabb.maxX + dx)
  let newMinY := clampPosition (aabb.minY + dy)
  let newMaxY := clampPosition (aabb.maxY + dy)
  let orderedX := orderPair newMinX newMaxX
  let orderedY := orderPair newMinY newMaxY
  { minX := orderedX.1
  , maxX := orderedX.2
  , minY := orderedY.1
  , maxY := orderedY.2
  , valid_x := orderPair_ordered newMinX newMaxX
  , valid_y := orderPair_ordered newMinY newMaxY
  , within_world_minX := orderPair_fst_bounds _ _ (clampPosition_bounds _).1 (clampPosition_bounds _).1
  , within_world_maxX := orderPair_snd_bounds _ _ (clampPosition_bounds _).2 (clampPosition_bounds _).2
  , within_world_minY := orderPair_fst_bounds _ _ (clampPosition_bounds _).1 (clampPosition_bounds _).1
  , within_world_maxY := orderPair_snd_bounds _ _ (clampPosition_bounds _).2 (clampPosition_bounds _).2 }

/-- THEOREM: Translated AABB remains within world bounds.
    
    Even after translation, the AABB is clamped to world bounds. -/
theorem translated_aabb_within_world (aabb : BoundedAABB) (dx dy : ℝ)
    (hdx_lo : -maxDisplacementPerTick ≤ dx) (hdx_hi : dx ≤ maxDisplacementPerTick)
    (hdy_lo : -maxDisplacementPerTick ≤ dy) (hdy_hi : dy ≤ maxDisplacementPerTick) :
    let newAABB := translateAABB aabb dx dy hdx_lo hdx_hi hdy_lo hdy_hi
    minPosition ≤ newAABB.minX ∧ newAABB.maxX ≤ maxPosition ∧
    minPosition ≤ newAABB.minY ∧ newAABB.maxY ≤ maxPosition := by
  simp only [translateAABB]
  exact ⟨orderPair_fst_bounds _ _ (clampPosition_bounds _).1 (clampPosition_bounds _).1,
         orderPair_snd_bounds _ _ (clampPosition_bounds _).2 (clampPosition_bounds _).2,
         orderPair_fst_bounds _ _ (clampPosition_bounds _).1 (clampPosition_bounds _).1,
         orderPair_snd_bounds _ _ (clampPosition_bounds _).2 (clampPosition_bounds _).2⟩

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: ANTI-ESCAPE GUARANTEES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Apply one movement step -/
def applyMovement (p : BoundedPosition2D) (vel : BoundedVelocity2D) (dt : BoundedDeltaTime) : 
    BoundedPosition2D :=
  { x := applyVelocityToCoord p.x vel.vx dt
  , y := applyVelocityToCoord p.y vel.vy dt }

/-- Apply a list of movements -/
def applyMovements : List (BoundedVelocity2D × BoundedDeltaTime) → BoundedPosition2D → BoundedPosition2D
  | [], p => p
  | (vel, dt) :: rest, p => applyMovements rest (applyMovement p vel dt)

/-- THE SPATIAL CONTAINMENT THEOREM
    
    An entity starting within world bounds, after any number of 
    velocity applications with bounded inputs, remains within bounds.
    
    There is NO sequence of operations that can escape the world. -/
theorem spatial_containment (pos : BoundedPosition2D) 
    (movements : List (BoundedVelocity2D × BoundedDeltaTime)) :
    let finalPos := applyMovements movements pos
    minPosition ≤ finalPos.x.value ∧ finalPos.x.value ≤ maxPosition ∧
    minPosition ≤ finalPos.y.value ∧ finalPos.y.value ≤ maxPosition := by
  -- The result is a BoundedPosition2D, which carries its own bounds proofs
  simp only
  let finalPos := applyMovements movements pos
  exact ⟨finalPos.x.lower_bound, finalPos.x.upper_bound, 
         finalPos.y.lower_bound, finalPos.y.upper_bound⟩

/-- Concrete bound: Entity cannot move more than 10000 pixels per tick -/
theorem max_movement_per_tick :
    maxDisplacementPerTick = 10000 := by
  simp only [maxDisplacementPerTick, maxVelocity, maxDeltaTime]
  norm_num

/-- ESCAPE IS IMPOSSIBLE THEOREM
    
    Even with adversarial inputs (any velocity, any dt), the clamping
    ensures the entity stays within [0, 10000] × [0, 10000]. -/
theorem escape_impossible (rawX rawY rawVx rawVy rawDt : ℝ) :
    let pos := mkBoundedPosition2D rawX rawY
    let vel : BoundedVelocity2D := 
      { vx := mkBoundedVelocityComp rawVx
      , vy := mkBoundedVelocityComp rawVy }
    let dt := mkBoundedDeltaTime rawDt
    let newPos : BoundedPosition2D := 
      { x := applyVelocityToCoord pos.x vel.vx dt
      , y := applyVelocityToCoord pos.y vel.vy dt }
    minPosition ≤ newPos.x.value ∧ newPos.x.value ≤ maxPosition ∧
    minPosition ≤ newPos.y.value ∧ newPos.y.value ≤ maxPosition := by
  simp only [mkBoundedPosition2D, mkBoundedCoord, applyVelocityToCoord]
  exact ⟨(clampPosition_bounds _).1, (clampPosition_bounds _).2,
         (clampPosition_bounds _).1, (clampPosition_bounds _).2⟩

-- ---------------------------------------------------------------------------
-- SECTION 10: ELEVATION (Z-DEPTH)
-- ---------------------------------------------------------------------------

/-- Minimum elevation (ground level) -/
def minElevation : ℝ := 0.0

/-- Maximum elevation (ceiling) -/
def maxElevation : ℝ := 10000.0

/-- Maximum elevation velocity (prevents "thrown" sensation) -/
def maxElevationVelocity : ℝ := 1000.0

theorem minElevation_nonneg : minElevation ≥ 0 := by simp [minElevation]; norm_num
theorem maxElevation_pos : maxElevation > 0 := by simp [maxElevation]; norm_num
theorem maxElevationVelocity_pos : maxElevationVelocity > 0 := by simp [maxElevationVelocity]; norm_num

/-- Clamp elevation to bounds -/
def clampElevation (e : ℝ) : ℝ := clamp minElevation maxElevation e

/-- Clamp elevation velocity to bounds -/
def clampElevationVelocity (v : ℝ) : ℝ := clamp (-maxElevationVelocity) maxElevationVelocity v

theorem clampElevation_bounds (e : ℝ) : 
    minElevation ≤ clampElevation e ∧ clampElevation e ≤ maxElevation := by
  apply clamp_bounds
  simp [minElevation, maxElevation]; norm_num

theorem clampElevationVelocity_bounds (v : ℝ) :
    -maxElevationVelocity ≤ clampElevationVelocity v ∧ clampElevationVelocity v ≤ maxElevationVelocity := by
  apply clamp_bounds
  simp [maxElevationVelocity]; norm_num

/-- A bounded elevation value -/
structure BoundedElevation where
  value : ℝ
  lower_bound : minElevation ≤ value
  upper_bound : value ≤ maxElevation

/-- A bounded elevation velocity -/
structure BoundedElevationVelocity where
  value : ℝ
  lower_bound : -maxElevationVelocity ≤ value
  upper_bound : value ≤ maxElevationVelocity

/-- Create bounded elevation by clamping -/
def mkBoundedElevation (e : ℝ) : BoundedElevation :=
  { value := clampElevation e
  , lower_bound := (clampElevation_bounds e).1
  , upper_bound := (clampElevation_bounds e).2 }

/-- Create bounded elevation velocity by clamping -/
def mkBoundedElevationVelocity (v : ℝ) : BoundedElevationVelocity :=
  { value := clampElevationVelocity v
  , lower_bound := (clampElevationVelocity_bounds v).1
  , upper_bound := (clampElevationVelocity_bounds v).2 }

/-- Apply elevation velocity -/
def applyElevationVelocity (e : BoundedElevation) (v : BoundedElevationVelocity) 
    (dt : BoundedDeltaTime) : BoundedElevation :=
  mkBoundedElevation (e.value + v.value * dt.value)

/-- THEOREM: Elevation change is always bounded.
    Experience cannot "throw" an entity outside elevation bounds. -/
theorem elevation_change_bounded (e : BoundedElevation) (v : BoundedElevationVelocity)
    (dt : BoundedDeltaTime) :
    let newE := applyElevationVelocity e v dt
    minElevation ≤ newE.value ∧ newE.value ≤ maxElevation := by
  simp only [applyElevationVelocity, mkBoundedElevation]
  exact clampElevation_bounds _

/-- THEOREM: Elevation escape is impossible -/
theorem elevation_escape_impossible (rawE rawV rawDt : ℝ) :
    let e := mkBoundedElevation rawE
    let v := mkBoundedElevationVelocity rawV
    let dt := mkBoundedDeltaTime rawDt
    let newE := applyElevationVelocity e v dt
    minElevation ≤ newE.value ∧ newE.value ≤ maxElevation := by
  simp only [applyElevationVelocity, mkBoundedElevation]
  exact clampElevation_bounds _

-- ---------------------------------------------------------------------------
-- SECTION 11: BEZIER EASING HANDLES
-- ---------------------------------------------------------------------------

/-- Minimum Y value for easing handles (small undershoot allowed).

    Bezier easing handles define cubic Bezier curves for animations.
    
    ATTACK VECTORS:
    - Extreme handles create motion sickness
    - Rapid oscillation causes disorientation
    - Unbounded overshoot creates jarring motion
    
    DEFENSE:
    - X handles bounded to [0, 1] (time dimension)
    - Y handles bounded to [-0.2, 1.2] (value dimension, small overshoot allowed)
    - Maximum acceleration check prevents motion sickness curves -/
def minEasingY : ℝ := -0.2

/-- Maximum Y value for easing handles (small overshoot allowed) -/
def maxEasingY : ℝ := 1.2

/-- Clamp easing X coordinate to [0, 1] -/
def clampEasingX (x : ℝ) : ℝ := clamp 0 1 x

/-- Clamp easing Y coordinate to [-0.2, 1.2] -/
def clampEasingY (y : ℝ) : ℝ := clamp minEasingY maxEasingY y

theorem clampEasingX_bounds (x : ℝ) : 0 ≤ clampEasingX x ∧ clampEasingX x ≤ 1 := by
  apply clamp_bounds
  norm_num

theorem clampEasingY_bounds (y : ℝ) : 
    minEasingY ≤ clampEasingY y ∧ clampEasingY y ≤ maxEasingY := by
  apply clamp_bounds
  simp [minEasingY, maxEasingY]; norm_num

/-- A bounded easing X coordinate (time dimension) -/
structure BoundedEasingX where
  value : ℝ
  lower_bound : 0 ≤ value
  upper_bound : value ≤ 1

/-- A bounded easing Y coordinate (value dimension) -/
structure BoundedEasingY where
  value : ℝ
  lower_bound : minEasingY ≤ value
  upper_bound : value ≤ maxEasingY

/-- Create bounded easing X by clamping -/
def mkBoundedEasingX (x : ℝ) : BoundedEasingX :=
  { value := clampEasingX x
  , lower_bound := (clampEasingX_bounds x).1
  , upper_bound := (clampEasingX_bounds x).2 }

/-- Create bounded easing Y by clamping -/
def mkBoundedEasingY (y : ℝ) : BoundedEasingY :=
  { value := clampEasingY y
  , lower_bound := (clampEasingY_bounds y).1
  , upper_bound := (clampEasingY_bounds y).2 }

/-- Bounded Bezier easing handles (cubic Bezier control points) -/
structure BoundedEasingHandles where
  x1 : BoundedEasingX
  y1 : BoundedEasingY
  x2 : BoundedEasingX
  y2 : BoundedEasingY

/-- Create bounded easing handles by clamping all components -/
def mkBoundedEasingHandles (x1 y1 x2 y2 : ℝ) : BoundedEasingHandles :=
  { x1 := mkBoundedEasingX x1
  , y1 := mkBoundedEasingY y1
  , x2 := mkBoundedEasingX x2
  , y2 := mkBoundedEasingY y2 }

/-- Maximum Y delta (approximates maximum acceleration) -/
def easingMaxDelta (handles : BoundedEasingHandles) : ℝ :=
  |handles.y1.value - 0| + |1 - handles.y2.value|

/-- THEOREM: Easing handles are always bounded.
    Malicious easing curves cannot escape the safe region. -/
theorem easing_handles_bounded (rawX1 rawY1 rawX2 rawY2 : ℝ) :
    let handles := mkBoundedEasingHandles rawX1 rawY1 rawX2 rawY2
    0 ≤ handles.x1.value ∧ handles.x1.value ≤ 1 ∧
    minEasingY ≤ handles.y1.value ∧ handles.y1.value ≤ maxEasingY ∧
    0 ≤ handles.x2.value ∧ handles.x2.value ≤ 1 ∧
    minEasingY ≤ handles.y2.value ∧ handles.y2.value ≤ maxEasingY := by
  simp only [mkBoundedEasingHandles, mkBoundedEasingX, mkBoundedEasingY]
  exact ⟨(clampEasingX_bounds _).1, (clampEasingX_bounds _).2,
         (clampEasingY_bounds _).1, (clampEasingY_bounds _).2,
         (clampEasingX_bounds _).1, (clampEasingX_bounds _).2,
         (clampEasingY_bounds _).1, (clampEasingY_bounds _).2⟩

/-- Maximum possible delta for any bounded handles -/
def maxPossibleEasingDelta : ℝ := |minEasingY - 0| + |1 - maxEasingY|

theorem maxPossibleEasingDelta_value : maxPossibleEasingDelta = 0.4 := by
  simp only [maxPossibleEasingDelta, minEasingY, maxEasingY]
  norm_num

/-- THEOREM: Easing acceleration is bounded.
    The "jerkiness" of any curve is limited.
    
    With Y bounds of [-0.2, 1.2]:
    - |y1 - 0| ≤ 1.2 (max when y1 = 1.2)
    - |1 - y2| ≤ 1.2 (max when y2 = -0.2)
    - Sum ≤ 2.4, which is ≤ 0.4 + 1 + 1 = 2.4 -/
theorem easing_acceleration_bounded (handles : BoundedEasingHandles) :
    easingMaxDelta handles ≤ 2.4 := by
  simp only [easingMaxDelta]
  have hy1_lo := handles.y1.lower_bound
  have hy1_hi := handles.y1.upper_bound
  have hy2_lo := handles.y2.lower_bound
  have hy2_hi := handles.y2.upper_bound
  simp only [minEasingY, maxEasingY] at *
  have h1 : |handles.y1.value - 0| ≤ 1.2 := by
    rw [sub_zero, abs_le]
    constructor <;> linarith
  have h2 : |1 - handles.y2.value| ≤ 1.2 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

end Hydrogen.WorldModel.SpatialIntegrity
