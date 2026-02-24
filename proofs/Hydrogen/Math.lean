/-
  Hydrogen.Math
  
  Root module for 3D mathematics with formal proofs.
  
  ARCHITECTURE:
    ┌─────────────────────────────────────────────────────────────────────────┐
    │                           Hydrogen.Math                                 │
    ├─────────────────────────────────────────────────────────────────────────┤
    │  Bounded.lean   │ Finite, Bounded, UnitInterval, Positive, NonNegative │
    │  Vec2.lean      │ 2D vectors, dot, perp, lerp (particle physics)        │
    │  Vec3.lean      │ 3D vectors, dot, cross, normalize, project/reject    │
    │  Vec4.lean      │ 4D/homogeneous vectors (TODO)                         │
    │  Mat3.lean      │ 3x3 matrices, rotations (TODO)                        │
    │  Mat4.lean      │ 4x4 matrices, transforms, determinant                 │
    │  Mat4Inverse    │ Matrix inversion, adjugate, cofactors                 │
    │  Mat4Projection │ Perspective, orthographic, look-at matrices           │
    │  Quaternion.lean│ Unit quaternions, SLERP, rotation matrices            │
    │  Integration    │ Euler, Verlet, velocity Verlet (particle physics)     │
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
  
  Status: FOUNDATIONAL - Bounded, Vec2, Vec3, Mat4, Quaternion, Integration complete; others TODO
-/

import Hydrogen.Math.Bounded
import Hydrogen.Math.Vec2
import Hydrogen.Math.Vec3
import Hydrogen.Math.Mat4
import Hydrogen.Math.Mat4Inverse
import Hydrogen.Math.Mat4Projection
import Hydrogen.Math.Quaternion
import Hydrogen.Math.Integration

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

## Vec2.lean (Particle Physics Foundation)

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg` - addition group
- `sub_def` - a - b = a + (-b)
- `scale_one`, `scale_zero`, `zero_scale` - scalar multiplication
- `scale_neg_one`, `neg_scale`, `scale_neg` - negation laws
- `scale_assoc`, `scale_add_left`, `scale_add_right` - scalar linearity

### Dot Product
- `dot_comm` - commutativity
- `dot_self_nonneg` - v·v ≥ 0
- `dot_self_eq_zero` - v·v = 0 ↔ v = 0
- `dot_scale_left`, `dot_scale_right` - scalar linearity
- `dot_add_left`, `dot_add_right` - additive linearity

### Perpendicular Operations (THE KEY GEOMETRIC PROOFS)
- `perp_orthogonal` - perp(v)·v = 0 (THE CRITICAL THEOREM for vortex forces)
- `perpCW_orthogonal` - perpCW(v)·v = 0
- `perp_neg_perpCW` - perp(v) = -perpCW(v)
- `lengthSq_perp` - |perp(v)|² = |v|² (rotation preserves length)
- `perp_perp` - perp(perp(v)) = -v (90° + 90° = 180°)
- `perp_perp_perp_perp` - four perp's = identity

### Length and Normalization
- `lengthSq_nonneg`, `length_nonneg` - non-negativity
- `lengthSq_eq_zero` - |v|² = 0 ↔ v = 0
- `lengthSq_zero_vec`, `length_zero_vec` - |0| = 0

### Linear Interpolation
- `lerp_zero` - lerp(0, a, b) = a
- `lerp_one` - lerp(1, a, b) = b
- `lerp_self` - lerp(t, a, a) = a

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

## Mat4.lean

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg` - addition group
- `mul_identity_left`, `mul_identity_right` - identity laws
- `mul_zero_left`, `mul_zero_right` - zero annihilation
- `mul_assoc` - THE CRITICAL THEOREM: matrix multiplication is associative
- `mul_add_left`, `mul_add_right` - distributivity
- `scale_mul_left`, `scale_mul_right` - scalar multiplication

### Transpose
- `transpose_involutive` - (Aᵀ)ᵀ = A
- `transpose_identity`, `transpose_zero` - special matrices
- `transpose_add`, `transpose_scale` - linearity
- `transpose_mul` - (AB)ᵀ = BᵀAᵀ (reverses order)

### Determinant
- `det_identity` - det(I) = 1
- `det_zero` - det(0) = 0
- `det_transpose` - det(Aᵀ) = det(A)
- `det_scale` - det(sA) = s⁴·det(A)
- `det_mul` - det(AB) = det(A)·det(B) (multiplicative)

### Transformations
- `makeTranslation_zero`, `makeScale_one` - identity cases
- `makeTranslation_mul` - T(a)·T(b) = T(a+b) (translations compose by adding)
- `makeScale_mul` - S(a)·S(b) = S(a*b) (scales compose by multiplying)
- `makeRotationX/Y/Z_zero` - R(0) = I (zero rotation is identity)
- `det_makeTranslation` - det = 1 (volume-preserving)
- `det_makeScale` - det = sx·sy·sz (volume scaling)
- `det_makeRotationX/Y/Z` - det = 1 (volume-preserving)

### Invertibility
- `identity_invertible`, `makeTranslation_invertible` - basic invertibility
- `makeScale_invertible`, `makeRotationX/Y/Z_invertible` - transform invertibility
- `mul_invertible` - product of invertibles is invertible

## Mat4Inverse.lean

### Cofactors and Adjugate
- `c00`..`c33` - all 16 cofactor functions
- `adjugate` - transpose of cofactor matrix
- `adjugate_identity` - adj(I) = I

### Adjugate Laws
- `mul_adjugate` - A × adj(A) = det(A) × I (KEY IDENTITY)
- `adjugate_mul` - adj(A) × A = det(A) × I

### Inverse
- `inverse` - A⁻¹ = adj(A) / det(A) for invertible A
- `mul_inverse` - A × A⁻¹ = I (right inverse)
- `inverse_mul` - A⁻¹ × A = I (left inverse)
- `inverse_identity` - I⁻¹ = I
- `inverse_mul_rev` - (A × B)⁻¹ = B⁻¹ × A⁻¹ (reverses order)

## Mat4Projection.lean

### Perspective Projection
- `makePerspective` - symmetric frustum from fov, aspect, near, far
- `makeFrustum` - asymmetric frustum from bounds

### Orthographic Projection
- `makeOrthographic` - orthographic from bounds
- `makeOrthographicSymmetric` - centered orthographic
- `makeOrthographic_invertible` - non-degenerate ortho is invertible
- `det_makeOrthographicSymmetric` - determinant is nonzero

### View Matrix
- `makeLookAt` - view matrix from eye, center, up vectors

## Quaternion.lean

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg` - addition group
- `mul_identity_left`, `mul_identity_right` - identity laws
- `mul_zero_left`, `mul_zero_right` - zero annihilation
- `mul_assoc` - THE KEY THEOREM: quaternion multiplication is associative
- `mul_not_comm` - multiplication is NOT commutative (unlike matrices)
- `scale_mul_left`, `scale_mul_right` - scalar multiplication

### Conjugate
- `conjugate_involutive` - (q*)* = q
- `conjugate_identity`, `conjugate_zero` - special cases
- `conjugate_mul` - (ab)* = b*a* (reverses order)
- `conjugate_add` - distributes over addition
- `mul_conjugate`, `conjugate_mul_self` - q × q* = ‖q‖² × I

### Length
- `lengthSq_nonneg`, `length_nonneg` - non-negativity
- `lengthSq_identity`, `length_identity` - identity has length 1
- `lengthSq_zero`, `length_zero` - zero has length 0
- `lengthSq_eq_zero` - ‖q‖² = 0 ↔ q = 0
- `length_conjugate` - ‖q*‖ = ‖q‖
- `lengthSq_mul`, `length_mul` - ‖ab‖ = ‖a‖ × ‖b‖ (multiplicative)

### Unit Quaternions
- `IsUnit` - predicate for unit length
- `identity_isUnit` - I is unit
- `mul_isUnit` - unit × unit = unit (closed under multiplication)
- `conjugate_isUnit` - unit* is unit
- `fromRotationX/Y/Z_isUnit` - axis rotations are unit
- `normalize_isUnit` - normalization produces unit quaternion

### Inverse
- `inverse` - q⁻¹ = q* / ‖q‖²
- `inverse_unit` - for unit q: q⁻¹ = q*
- `mul_inverse_unit`, `inverse_mul_unit` - q × q⁻¹ = I for unit q

### SLERP
- `lerp` - linear interpolation (for small angles)
- `lerp_zero`, `lerp_one` - lerp endpoints
- `slerp` - spherical linear interpolation (THE KEY FEATURE)

### Rotation Matrix Conversion
- `toMat4` - convert quaternion to 4×4 rotation matrix
- `toMat4_identity` - identity quaternion → identity matrix
- `det_toMat4_unit` - det = 1 for unit quaternions (rotation matrices)

## Integration.lean (Particle Physics Simulation)

### Integration Methods
- `eulerStep` - explicit Euler (simple but unstable)
- `semiImplicitEulerStep` - symplectic Euler (LATTICE rigid bodies)
- `verletStep` - Störmer-Verlet (LATTICE soft bodies)
- `verletStepDamped` - Verlet with damping factor
- `velocityVerletStep` - velocity Verlet (explicit velocity tracking)

### State Conversion
- `toVerletState` - convert particle state to Verlet state
- `fromVerletState` - extract ParticleState from VerletState
- `verletVelocity` - extract implicit velocity from Verlet state

### Zero Acceleration
- `euler_zero_accel` - zero acceleration preserves velocity
- `semiImplicit_zero_accel` - zero acceleration preserves velocity

### Zero Timestep
- `euler_zero_dt` - zero timestep is identity
- `semiImplicit_zero_dt` - zero timestep is identity
- `verlet_zero_dt` - zero timestep advances by implicit velocity

### Time-Reversibility (THE KEY THEOREM)
- `verlet_time_reversible` - Verlet is time-reversible (energy conservation)

### Euler Comparison
- `euler_semiImplicit_same_velocity` - both produce same velocity
- `euler_semiImplicit_position_diff` - position differs by a*dt²

### Verlet Equivalence
- `verlet_position_formula` - classic x(t+dt) = 2x(t) - x(t-dt) + a*dt²
- `verlet_conversion_velocity` - velocity preserved through conversion

### Damping Properties
- `verlet_damping_one` - damping=1 is undamped Verlet
- `verlet_damping_zero` - damping=0 eliminates velocity

### Velocity Verlet Properties
- `velocityVerlet_same_velocity` - same velocity as explicit Euler
- `velocityVerlet_position` - includes second-order correction
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
