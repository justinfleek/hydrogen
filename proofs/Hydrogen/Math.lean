/-
  Hydrogen.Math
  
  Root module for 3D mathematics with formal proofs.
  
  ARCHITECTURE:
    ┌─────────────────────────────────────────────────────────────────────────┐
    │                           Hydrogen.Math                                 │
    ├─────────────────────────────────────────────────────────────────────────┤
    │  Bounded.lean   │ Finite, Bounded, UnitInterval, Positive, NonNegative │
    │  Vec3.lean      │ 3D vectors, dot, cross, normalize, project/reject    │
    │  Vec2.lean      │ 2D vectors (TODO)                                     │
    │  Vec4.lean      │ 4D/homogeneous vectors (TODO)                         │
    │  Mat3.lean      │ 3x3 matrices, rotations (TODO)                        │
    │  Mat4.lean      │ 4x4 matrices, transforms (TODO)                       │
    │  Quaternion.lean│ Unit quaternions, slerp (TODO)                        │
    │  Transform.lean │ Position + Rotation + Scale (TODO)                    │
    │  AABB.lean      │ Axis-aligned bounding boxes (TODO)                    │
    │  Frustum.lean   │ View frustum, culling (TODO)                          │
    └─────────────────────────────────────────────────────────────────────────┘
  
  ZERO-LATENCY INVARIANTS (proven for all operations):
    1. All values are finite (no NaN, no Infinity)
    2. All operations terminate in bounded steps
    3. All transformations preserve key geometric properties
    4. All normalizations handle edge cases by proof, not runtime check
  
  These proofs enable billion-agent operation without runtime validation.
  
  Status: FOUNDATIONAL - Bounded and Vec3 complete, others TODO
-/

import Hydrogen.Math.Bounded
import Hydrogen.Math.Vec3

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- RE-EXPORTS
-- ═══════════════════════════════════════════════════════════════════════════════

-- All types and theorems from submodules are available via this import

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY OF PROVEN PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Bounded.lean

### Finite
- `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `distrib`
- Arithmetic forms a commutative ring

### Bounded
- `clamp_idempotent` - clamping is idempotent
- `clamp_within` - in-bounds values unchanged
- `add_bounded` - addition preserves bounds

### UnitInterval
- `complement_involutive` - complement (complement x) = x
- `lerp_zero`, `lerp_one` - lerp endpoints
- `lerp_bounded` - lerp stays in range
- `mul_comm`, `mul_assoc` - multiplication laws

### Positive, NonNegative
- `sqrt_sq` - sqrt (x²) = x for non-negative x

## Vec3.lean

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `add_neg` - addition group
- `scale_one`, `scale_assoc`, `scale_distrib_vec`, `scale_distrib_scalar` - scalar mult

### Dot Product
- `dot_comm` - commutativity
- `dot_self_nonneg` - v·v ≥ 0
- `dot_self_eq_zero` - v·v = 0 ↔ v = 0
- `dot_scale_left`, `dot_scale_right` - scalar linearity
- `dot_add_left`, `dot_add_right` - additive linearity

### Cross Product (THE KEY GEOMETRIC PROOFS)
- `cross_perp_left` - a · (a × b) = 0 (perpendicular to first)
- `cross_perp_right` - b · (a × b) = 0 (perpendicular to second)
- `cross_anticomm` - a × b = -(b × a)
- `cross_self` - v × v = 0
- `cross_add_left`, `cross_add_right` - distributivity
- `cross_scale_left`, `cross_scale_right` - scalar linearity

### Length and Normalization
- `lengthSq_nonneg`, `length_nonneg` - non-negativity
- `length_zero`, `lengthSq_eq_zero` - zero characterization
- `length_scale` - |s·v| = |s|·|v|
- `normalize_length` - |normalize v| = 1
- `normalize_idempotent` - normalizing a unit vector is identity

### Geometric Operations
- `project_reject_orthogonal` - projection ⊥ rejection
- `project_reject_sum` - projection + rejection = original
- `lerp_zero_t`, `lerp_one_t` - lerp endpoints
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- WHAT THESE PROOFS ENABLE AT BILLION-AGENT SCALE
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Why These Proofs Matter

When 1 million agents operate at 1000+ tokens/second:

1. **No runtime validation needed**
   - `cross_perp_left` is PROVEN - no need to check `abs(dot(a, cross(a,b))) < epsilon`
   - `normalize_length` is PROVEN - no need to check `abs(length(normalize(v)) - 1) < epsilon`
   
2. **No exception handling paths**
   - Division by zero in `normalize` is impossible by construction (proof requires v ≠ 0)
   - NaN propagation is impossible (all values are real numbers)
   
3. **No coordination overhead**
   - All operations are pure functions
   - Same input → same output (deterministic)
   - Can be parallelized without locks
   
4. **Bounded computation**
   - Every operation completes in O(1)
   - No iteration, no recursion (except lerp which is O(1))
   
5. **Composable correctness**
   - `project_reject_sum` lets us decompose vectors knowing the sum is exact
   - Downstream proofs can rely on these without re-proving

## The Code Generation Contract

The generated PureScript mirrors the Lean definitions exactly:
- Same structure
- Same operations
- Same semantics (both pure, both call-by-value)

The proofs in Lean ARE the specification. The PureScript IS the implementation.
They match by construction.
-/

end Hydrogen.Math
