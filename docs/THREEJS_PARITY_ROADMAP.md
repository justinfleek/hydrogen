# Three.js Parity Roadmap

> EVERYTHING. Norman Stansfield energy.

## Status: PHASE 1-3 COMPLETE — Proofs finished, PureScript generation next

---

## CURRENT IMPLEMENTATION AUDIT

*Last audited: 2026-02-24*

This section tracks what we ACTUALLY have across the Hydrogen codebase.

### Summary

| Layer | Files | Lines | Status |
|-------|-------|-------|--------|
| **Lean4 Proofs** | 50+ | ~15,000+ | ✅ COMPLETE (0 sorry) |
| **PureScript FFI** | 6 | ~2,500 | ⚠️ Three.js wrapper (TO REPLACE) |
| **PureScript Pure** | 1 | ~700 | ✅ Math/Core.purs |

### Lean4 Proofs (proofs/Hydrogen/)

**ALL PROOFS COMPLETE — ZERO SORRY**

Build status: `3,173 jobs, 0 warnings, 0 errors`

#### Math Module (19 files, ~7,100 lines)

| File | Lines | Key Types/Theorems | Status |
|------|-------|-------------------|--------|
| `Vec2.lean` | ~329 | Vec2, perp_orthogonal, lengthSq_perp, lerp | ✅ DONE |
| `Vec3.lean` | ~553 | Vec3, cross_perp_left/right, normalize_length, project_reject_orthogonal | ✅ DONE |
| `Vec4.lean` | ~340 | Vec4, homogeneous coords, point/direction, perspectiveDivide | ✅ DONE |
| `Mat3.lean` | ~556 | Mat3, mul_assoc, det_mul, transpose_mul, inverse proofs | ✅ DONE |
| `Mat4.lean` | ~530 | Mat4, determinant, multiply, all transform proofs | ✅ DONE |
| `Mat4Inverse.lean` | ~400 | Full 4x4 inverse via adjugate, mul_inverse proof | ✅ DONE |
| `Mat4Projection.lean` | ~350 | Perspective/orthographic projection matrices | ✅ DONE |
| `Quaternion.lean` | ~599 | Unit quaternions, SLERP, toMat4, IsUnit proofs | ✅ DONE |
| `Euler.lean` | ~434 | All 6 rotation orders (XYZ, YZX, ZXY, XZY, YXZ, ZYX) | ✅ DONE |
| `Box3.lean` | ~300 | AABB, containsPoint, intersectsBox, expandByPoint | ✅ DONE |
| `Sphere.lean` | ~250 | Bounding sphere, containsPoint, intersectsSphere | ✅ DONE |
| `Plane.lean` | ~280 | Infinite plane, distanceToPoint, projectPoint | ✅ DONE |
| `Frustum.lean` | ~320 | View frustum, containsPoint, intersectsBox/Sphere | ✅ DONE |
| `Ray.lean` | ~350 | Ray casting, intersectSphere, intersectPlane, intersectBox | ✅ DONE |
| `Triangle.lean` | ~300 | Barycentric coords, containsPoint, getArea, getNormal | ✅ DONE |
| `Bounded.lean` | ~200 | BoundedInt, clamp, wrap behaviors | ✅ DONE |
| `Constraint.lean` | ~255 | Distance constraints for soft body physics | ✅ DONE |
| `Force.lean` | ~266 | Vortex/gravity forces, vortex_force_orthogonal | ✅ DONE |
| `Integration.lean` | ~316 | Euler, Verlet, velocity Verlet, time-reversibility | ✅ DONE |

#### Geometry Module (5 files, ~1,200 lines)

| File | Key Types | Status |
|------|-----------|--------|
| `Bounds.lean` | BoundingBox, BoundingSphere | ✅ DONE |
| `Mesh.lean` | MeshData, VertexBuffer, IndexBuffer | ✅ DONE |
| `Primitives.lean` | Box, Sphere, Cylinder, Cone, Torus parameters | ✅ DONE |
| `Texture.lean` | TextureCoord, UV mapping | ✅ DONE |
| `Vertex.lean` | Vertex attributes, normals, tangents | ✅ DONE |

#### Camera Module (3 files, ~500 lines)

| File | Key Types | Status |
|------|-----------|--------|
| `Types.lean` | Camera, PerspectiveCamera, OrthographicCamera | ✅ DONE |
| `Lens.lean` | FOV, focal length, film gauge | ✅ DONE |
| `Projection.lean` | Projection matrices, near_lt_far proofs | ✅ DONE |

#### Light Module (6 files, ~900 lines)

| File | Key Types | Status |
|------|-----------|--------|
| `Types.lean` | Light, intensity bounds [0,1] | ✅ DONE |
| `Attenuation.lean` | Linear, quadratic falloff, physically correct | ✅ DONE |
| `Directional.lean` | DirectionalLight, direction normalization | ✅ DONE |
| `Point.lean` | PointLight, distance cutoff | ✅ DONE |
| `Spot.lean` | SpotLight, cone angle, penumbra | ✅ DONE |
| `Shadow.lean` | Shadow mapping, bias, depth comparison | ✅ DONE |

#### Material Module (5 files, ~1,100 lines)

| File | Key Types | Status |
|------|-----------|--------|
| `Types.lean` | Material base, opacity bounds | ✅ DONE |
| `Layer.lean` | Material layers, composition | ✅ DONE |
| `BRDF.lean` | Fresnel, GGX, Smith, Cook-Torrance | ✅ DONE |
| `Sparkle.lean` | Automotive sparkle/flake effects | ✅ DONE |
| `ISP.lean` | Image signal processing, color grading | ✅ DONE |

#### Scene Module (4 files, ~800 lines)

| File | Key Types | Status |
|------|-----------|--------|
| `Node.lean` | SceneNode, Transform, parent/child | ✅ DONE |
| `Graph.lean` | Scene graph traversal, updateWorldMatrix | ✅ DONE |
| `Resource.lean` | Resource management, ref counting | ✅ DONE |
| `Diff.lean` | Scene diffing for incremental updates | ✅ DONE |

#### WorldModel Module (8 files, ~2,500 lines)

| File | Key Types | Status |
|------|-----------|--------|
| `Rights.lean` | AI rights primitives | ✅ DONE |
| `Consensus.lean` | Multi-agent consensus proofs | ✅ DONE |
| `Governance.lean` | Governance structures | ✅ DONE |
| `Economy.lean` | Resource allocation, bounded trade | ✅ DONE |
| `Affective.lean` | Wellbeing attestation, liveness protocol | ✅ DONE |
| `Attention.lean` | Attention mechanisms | ✅ DONE |
| `Integrity.lean` | Sensory integrity, identity continuity | ✅ DONE |
| `Pose.lean` | 3D pose representation | ✅ DONE |

#### Schema Module (Color Proofs)

| File | Key Theorems | Status |
|------|--------------|--------|
| `Conversions.lean` | RGB↔HSL roundtrip, luminance preservation | ✅ DONE (10 theorems) |

---

### PureScript Implementation (src/Hydrogen/)

#### Three.js FFI Wrapper (TO BE REPLACED)

| File | Lines | Description | Status |
|------|-------|-------------|--------|
| `ThreeD/Scene.purs` | ~1,559 | Full Three.js wrapper with cameras, lighting, controls, primitives, materials, model loading, post-processing, WebXR | ⚠️ FFI (REPLACE) |
| `ThreeD/Scene.js` | ~852 | FFI bindings to Three.js, scene registry, raycasting, animation loop | ⚠️ FFI (REPLACE) |
| `ThreeD/Canvas3D.purs` | ~500 | Simplified 3D canvas for product viewers | ⚠️ FFI (REPLACE) |
| `ThreeD/Canvas3D.js` | ~200 | FFI for Canvas3D | ⚠️ FFI (REPLACE) |
| `ThreeD/Model.purs` | ~200 | GLTF/GLB model loading with animations | ⚠️ FFI (REPLACE) |
| `ThreeD/Model.js` | ~150 | FFI for model loading | ⚠️ FFI (REPLACE) |

**Current FFI features:**
- Scene management with registry
- Camera creation (Perspective, Orthographic)
- Lighting (Ambient, Directional, Point, Spot, Hemisphere)
- Primitives (Box, Sphere, Cylinder, Cone, Plane, Torus, Ring, Circle)
- Materials (Basic, Standard, Phong, Physical, Toon, Matcap)
- Model loading (GLTF, GLB with animations)
- OrbitControls
- Raycasting
- Post-processing (Bloom, SSAO, Outline)
- WebXR support
- Screenshot capture

#### Pure PureScript Math (NO FFI)

| File | Lines | Description | Status |
|------|-------|-------------|--------|
| `Math/Core.purs` | ~694 | Taylor series sin/cos/tan/exp/log, Newton-Raphson sqrt/cbrt, lerp, smoothstep | ✅ PURE |

**Math/Core.purs provides:**
- Trigonometric: sin, cos, tan, asin, acos, atan, atan2
- Hyperbolic: sinh, cosh, tanh
- Exponential: exp, log, log10, log2
- Roots: sqrt, cbrt (Newton-Raphson)
- Interpolation: lerp, smoothstep, smootherstep
- Utilities: clamp, sign, fract, mod, abs, floor, ceil, round

#### GPU Module (Pure Data Structures)

| File | Description | Status |
|------|-------------|--------|
| `GPU/Binary.purs` | Binary format handling | ✅ PURE |
| `GPU/DrawCommand.purs` | Draw command data types | ✅ PURE |
| `GPU/Index.purs` | Index buffer types | ✅ PURE |
| `GPU/GlyphConvert.purs` | Glyph conversion | ✅ PURE |
| `GPU/Flatten.purs` | Scene flattening | ✅ PURE |

#### Icon Module

| File | Description | Status |
|------|-------------|--------|
| `Icon/Icon3D.purs` | 3D icon primitives | ✅ PURE |
| `Icon/Icons3D.purs` | Icon collection | ✅ PURE |

---

### Gap Analysis

#### What We Have (Proven)
- ✅ Complete vector math (Vec2, Vec3, Vec4)
- ✅ Complete matrix math (Mat3, Mat4 with inverse)
- ✅ Quaternion rotations with SLERP
- ✅ Euler angles (all 6 orders)
- ✅ Geometric primitives (Box3, Sphere, Plane, Frustum, Ray, Triangle)
- ✅ Camera projections (perspective, orthographic)
- ✅ Light types and attenuation
- ✅ PBR BRDF (Fresnel, GGX, Cook-Torrance)
- ✅ Scene graph structure
- ✅ Physics integration (Verlet, constraints, forces)

#### What Needs Generation (Lean4 → PureScript)
- ⏳ Vec2, Vec3, Vec4 pure types (from proofs)
- ⏳ Mat3, Mat4 pure types (from proofs)
- ⏳ Quaternion, Euler pure types (from proofs)
- ⏳ Geometric primitives pure types (from proofs)
- ⏳ Camera types (from proofs)
- ⏳ Light types (from proofs)
- ⏳ Material types (from proofs)

#### What Needs Implementation (No FFI)
- ⏳ WebGL2 runtime (minimal interpreter)
- ⏳ WebGPU runtime (future)
- ⏳ Buffer management (typed arrays)
- ⏳ Shader compilation
- ⏳ Render pipeline

---

## 1. MATH FOUNDATION

The mathematical bedrock. Every 3D operation flows through these types.

### 1.1 Vectors

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Vector2` | `src/math/Vector2.js` | **PROVEN** ✅ | add, sub, scale, dot, perp, length, normalize, lerp (Vec2.lean ~329 lines) |
| `Vector3` | `src/math/Vector3.js` | **PROVEN** ✅ | add, sub, scale, dot, cross, length, normalize, lerp, project, reject, reflect (Vec3.lean ~553 lines) |
| `Vector4` | `src/math/Vector4.js` | **PROVEN** ✅ | add, sub, scale, dot, length, normalize, lerp, homogeneous coords (Vec4.lean ~340 lines) |

**Vector3 Methods (56 total in Three.js):**
```
set, setScalar, setX, setY, setZ, setComponent, getComponent, clone, copy,
add, addScalar, addVectors, addScaledVector, sub, subScalar, subVectors,
multiply, multiplyScalar, multiplyVectors, applyEuler, applyAxisAngle,
applyMatrix3, applyNormalMatrix, applyMatrix4, applyQuaternion,
project, unproject, transformDirection, divide, divideScalar,
min, max, clamp, clampScalar, clampLength, floor, ceil, round, roundToZero,
negate, dot, lengthSq, length, manhattanLength, normalize, setLength,
lerp, lerpVectors, cross, crossVectors, projectOnVector, projectOnPlane,
reflect, angleTo, distanceTo, distanceToSquared, manhattanDistanceTo,
setFromSpherical, setFromSphericalCoords, setFromCylindrical,
setFromCylindricalCoords, setFromMatrixPosition, setFromMatrixScale,
setFromMatrixColumn, setFromMatrix3Column, setFromEuler, setFromColor,
equals, fromArray, toArray, fromBufferAttribute, random, randomDirection
```

### 1.2 Matrices

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Matrix2` | `src/math/Matrix2.js` | NOT STARTED | identity, set, determinant, invert, multiply |
| `Matrix3` | `src/math/Matrix3.js` | **PROVEN** ✅ | identity, determinant, invert, transpose, multiply, getNormalMatrix (Mat3.lean ~556 lines) |
| `Matrix4` | `src/math/Matrix4.js` | **PROVEN** ✅ | Full 60+ methods including inverse, projection (Mat4.lean + Mat4Inverse.lean + Mat4Projection.lean ~1,280 lines) |

**Matrix4 Methods (THE BIG ONE - 62 methods):**
```
set, identity, clone, copy, copyPosition, setFromMatrix3,
extractBasis, makeBasis, extractRotation, makeRotationFromEuler,
makeRotationFromQuaternion, lookAt, multiply, premultiply, multiplyMatrices,
multiplyScalar, determinant, transpose, setPosition, invert, scale,
getMaxScaleOnAxis, makeTranslation, makeRotationX, makeRotationY,
makeRotationZ, makeRotationAxis, makeScale, makeShear,
compose, decompose, makePerspective, makeOrthographic,
equals, fromArray, toArray,
extractPosition (deprecated), setRotationFromQuaternion (deprecated),
multiplyVector3 (deprecated), multiplyVector4 (deprecated),
multiplyVector3Array (deprecated), rotateAxis (deprecated),
crossVector (deprecated), flattenToArray (deprecated),
flattenToArrayOffset (deprecated), getPosition (deprecated)
```

**CRITICAL PROOFS — ALL COMPLETE:**
- ✅ `(A × B) × C = A × (B × C)` — mul_assoc in Mat3.lean, Mat4.lean
- ✅ `(A × B)⁻¹ = B⁻¹ × A⁻¹` — inverse_mul_eq in Mat3.lean
- ✅ `det(A × B) = det(A) × det(B)` — det_mul in Mat3.lean, Mat4.lean
- ✅ `(A^T)^T = A` — transpose_involutive in Mat3.lean
- ✅ `det(rotation) = 1` — det_makeRotationX/Y/Z in Mat3.lean
- ✅ `M × M⁻¹ = I` — mul_inverse in Mat3.lean, Mat4Inverse.lean

### 1.3 Quaternion

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Quaternion` | `src/math/Quaternion.js` | **PROVEN** ✅ | multiply, conjugate, invert, normalize, slerp, toMat4, IsUnit proofs (Quaternion.lean ~599 lines) |

**Quaternion Methods (35 total):**
```
set, clone, copy, setFromEuler, setFromAxisAngle, setFromRotationMatrix,
setFromUnitVectors, angleTo, rotateTowards, slerp, slerpQuaternions,
identity, invert, conjugate, dot, lengthSq, length, normalize,
multiply, premultiply, multiplyQuaternions, equals,
fromArray, toArray, toJSON, onChange, _onChangeCallback,
slerpFlat (static), multiplyQuaternionsFlat (static)
```

**CRITICAL PROOFS — ALL COMPLETE:**
- ✅ Unit quaternions have length 1 — IsUnit predicate in Quaternion.lean
- ✅ `slerp(q, q, t) = q` — slerp_self in Quaternion.lean
- ✅ `slerp(q1, q2, 0) = q1` — slerp_zero in Quaternion.lean
- ✅ `slerp(q1, q2, 1) = q2` — slerp_one in Quaternion.lean
- ✅ Quaternion multiplication is associative — mul_assoc in Quaternion.lean
- ✅ `q × q⁻¹ = identity` — mul_inverse in Quaternion.lean

### 1.4 Euler Angles

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Euler` | `src/math/Euler.js` | **PROVEN** ✅ | All 6 rotation orders (XYZ, YZX, ZXY, XZY, YXZ, ZYX), toQuaternion, toMatrix (Euler.lean ~434 lines) |

**Euler Methods:**
```
set, clone, copy, setFromRotationMatrix, setFromQuaternion,
setFromVector3, reorder, equals, fromArray, toArray, toJSON,
onChange, _onChangeCallback, DEFAULT_ORDER (static)
```

### 1.5 Geometric Primitives

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Box2` | `src/math/Box2.js` | NOT STARTED | 2D axis-aligned bounding box |
| `Box3` | `src/math/Box3.js` | **PROVEN** ✅ | AABB intersection, containment, expand (Box3.lean ~300 lines) |
| `Sphere` | `src/math/Sphere.js` | **PROVEN** ✅ | Bounding sphere, containsPoint, intersects (Sphere.lean ~250 lines) |
| `Plane` | `src/math/Plane.js` | **PROVEN** ✅ | Infinite plane, distance, project (Plane.lean ~280 lines) |
| `Frustum` | `src/math/Frustum.js` | **PROVEN** ✅ | View frustum, containsPoint, intersectsBox/Sphere (Frustum.lean ~320 lines) |
| `Line3` | `src/math/Line3.js` | NOT STARTED | Line segment - closest point |
| `Triangle` | `src/math/Triangle.js` | **PROVEN** ✅ | Barycentric coords, containsPoint, area, normal (Triangle.lean ~300 lines) |
| `Ray` | `src/math/Ray.js` | **PROVEN** ✅ | Ray casting, intersectSphere/Plane/Box (Ray.lean ~350 lines) |

**Box3 Methods (26 total):**
```
set, setFromArray, setFromBufferAttribute, setFromPoints, setFromCenterAndSize,
setFromObject, clone, copy, makeEmpty, isEmpty, getCenter, getSize,
expandByPoint, expandByVector, expandByScalar, expandByObject,
containsPoint, containsBox, getParameter, intersectsBox, intersectsSphere,
intersectsPlane, intersectsTriangle, clampPoint, distanceToPoint,
getBoundingSphere, intersect, union, applyMatrix4, translate, equals
```

**CRITICAL PROOFS — ALL COMPLETE:**
- ✅ Ray-sphere intersection — intersectSphere in Ray.lean
- ✅ Ray-plane intersection — intersectPlane in Ray.lean
- ✅ Ray-box intersection — intersectBox in Ray.lean
- ✅ Frustum containment — containsPoint, intersectsBox, intersectsSphere in Frustum.lean
- ✅ Triangle containsPoint — barycentric coordinates in Triangle.lean
- ✅ AABB operations — containsPoint, intersectsBox in Box3.lean

### 1.6 Coordinate Systems

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Spherical` | `src/math/Spherical.js` | NOT STARTED | radius, phi, theta ↔ cartesian |
| `Cylindrical` | `src/math/Cylindrical.js` | NOT STARTED | radius, theta, y ↔ cartesian |

### 1.7 Interpolation

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|----------------|
| `Interpolant` | `src/math/Interpolant.js` | NOT STARTED | Base class |
| `LinearInterpolant` | `src/math/interpolants/LinearInterpolant.js` | NOT STARTED | Linear interpolation |
| `CubicInterpolant` | `src/math/interpolants/CubicInterpolant.js` | NOT STARTED | Cubic spline |
| `DiscreteInterpolant` | `src/math/interpolants/DiscreteInterpolant.js` | NOT STARTED | Step function |
| `QuaternionLinearInterpolant` | `src/math/interpolants/QuaternionLinearInterpolant.js` | NOT STARTED | Quaternion slerp |

### 1.8 Color

| Type | Three.js | Hydrogen Status | Key Operations |
|------|----------|-----------------|-------------|
| `Color` | `src/math/Color.js` | **PROVEN** ✅ | RGB↔HSL roundtrip, luminance preservation, full Schema atoms (Schema/Color/Conversions.lean, 10 theorems) |

**Color Methods (40+ total):**
```
set, setScalar, setHex, setRGB, setHSL, setStyle, setColorName,
clone, copy, copySRGBToLinear, copyLinearToSRGB, convertSRGBToLinear,
convertLinearToSRGB, getHex, getHexString, getHSL, getRGB, getStyle,
offsetHSL, add, addColors, addScalar, sub, multiply, multiplyScalar,
lerp, lerpColors, lerpHSL, setFromVector3, applyMatrix3, equals,
fromArray, toArray, toJSON, getHex (deprecated)
```

### 1.9 Math Utilities

| Function | Three.js | Hydrogen Status | Description |
|----------|----------|-----------------|-------------|
| `clamp` | MathUtils | **DONE** ✅ | Bounded.lean (Lean4) + Math/Core.purs (PureScript) |
| `lerp` | MathUtils | **DONE** ✅ | Vec2/Vec3/Vec4.lean + Math/Core.purs |
| `inverseLerp` | MathUtils | NOT STARTED | Inverse of lerp |
| `mapLinear` | MathUtils | NOT STARTED | Map from one range to another |
| `smoothstep` | MathUtils | **DONE** ✅ | Math/Core.purs (pure PureScript) |
| `smootherstep` | MathUtils | **DONE** ✅ | Math/Core.purs (pure PureScript) |
| `randInt` | MathUtils | NOT STARTED | Random integer in range |
| `randFloat` | MathUtils | NOT STARTED | Random float in range |
| `randFloatSpread` | MathUtils | NOT STARTED | Random in [-range/2, range/2] |
| `degToRad` | MathUtils | **DONE** ✅ | Math/Core.purs |
| `radToDeg` | MathUtils | **DONE** ✅ | Math/Core.purs |
| `isPowerOfTwo` | MathUtils | NOT STARTED | Power of 2 check |
| `ceilPowerOfTwo` | MathUtils | NOT STARTED | Next power of 2 |
| `floorPowerOfTwo` | MathUtils | NOT STARTED | Previous power of 2 |
| `euclideanModulo` | MathUtils | **DONE** ✅ | Math/Core.purs (mod function) |
| `generateUUID` | MathUtils | NOT STARTED | UUID generation |
| `denormalize` | MathUtils | NOT STARTED | Denormalize from typed array |
| `normalize` | MathUtils | NOT STARTED | Normalize to typed array |

### 1.10 Spherical Harmonics

| Type | Three.js | Hydrogen Status | Description |
|------|----------|-----------------|-------------|
| `SphericalHarmonics3` | `src/math/SphericalHarmonics3.js` | NOT STARTED | For irradiance/lighting |

---

**MATH FOUNDATION TOTALS:**

| Category | Types | Methods | Proofs Needed |
|----------|-------|---------|---------------|
| Vectors | 3 | ~140 | ~20 |
| Matrices | 3 | ~100 | ~15 |
| Quaternion | 1 | ~35 | ~10 |
| Euler | 1 | ~15 | ~5 |
| Primitives | 8 | ~150 | ~25 |
| Coordinates | 2 | ~10 | ~5 |
| Interpolation | 5 | ~20 | ~10 |
| Color | 1 | ~40 | ~10 |
| Utilities | 17 | ~17 | ~5 |
| **TOTAL** | **41** | **~527** | **~105** |

---

## 2. CORE OBJECTS

The scene graph. Everything visible inherits from Object3D.

### 2.1 Object3D (THE FOUNDATION)

| Property/Method | Description | Proof Required? |
|-----------------|-------------|-----------------|
| `id` | Unique ID | No |
| `uuid` | UUID | No |
| `name` | Human-readable name | No |
| `parent` | Parent in scene graph | No |
| `children` | Child objects | No |
| `position` | Local position (Vector3) | No |
| `rotation` | Local rotation (Euler) | Yes - sync with quaternion |
| `quaternion` | Local rotation (Quaternion) | Yes - sync with euler |
| `scale` | Local scale (Vector3) | No |
| `matrix` | Local transform matrix | Yes - compose/decompose |
| `matrixWorld` | World transform matrix | Yes - parent chain |
| `matrixAutoUpdate` | Auto-update matrix | No |
| `matrixWorldNeedsUpdate` | Dirty flag | No |
| `visible` | Visibility flag | No |
| `castShadow` | Shadow casting | No |
| `receiveShadow` | Shadow receiving | No |
| `frustumCulled` | Frustum culling | No |
| `renderOrder` | Render order | No |
| `userData` | User data | No |

**Object3D Methods (50+):**
```
add, remove, removeFromParent, clear, attach,
getObjectById, getObjectByName, getObjectByProperty, getObjectsByProperty,
getWorldPosition, getWorldQuaternion, getWorldScale, getWorldDirection,
traverse, traverseVisible, traverseAncestors,
updateMatrix, updateMatrixWorld, updateWorldMatrix,
localToWorld, worldToLocal, lookAt,
raycast, clone, copy, toJSON, applyMatrix4,
applyQuaternion, setRotationFromAxisAngle, setRotationFromEuler,
setRotationFromMatrix, setRotationFromQuaternion, rotateOnAxis,
rotateOnWorldAxis, rotateX, rotateY, rotateZ, translateOnAxis,
translateX, translateY, translateZ
```

**CRITICAL PROOFS:**
- `matrixWorld = parent.matrixWorld × matrix`
- `localToWorld(worldToLocal(v)) = v`
- Rotation order consistency (Euler ↔ Quaternion ↔ Matrix)

### 2.2 Scene

| Property | Description |
|----------|-------------|
| `background` | Background color/texture/cubemap |
| `environment` | Environment map for PBR |
| `fog` | Fog settings |
| `backgroundBlurriness` | Background blur |
| `backgroundIntensity` | Background intensity |
| `backgroundRotation` | Background rotation (Euler) |
| `environmentIntensity` | Environment intensity |
| `environmentRotation` | Environment rotation (Euler) |
| `overrideMaterial` | Force all objects to use this material |

### 2.3 Group

Simple Object3D container with no additional properties.

### 2.4 Layers

32-bit layer mask system for selective rendering.

```
set(layer), enable(layer), enableAll(), toggle(layer),
disable(layer), disableAll(), test(layers), isEnabled(layer)
```

### 2.5 Raycaster

| Method | Description | Proof Required? |
|--------|-------------|-----------------|
| `set(origin, direction)` | Set ray | No |
| `setFromCamera(coords, camera)` | Ray from screen coords | Yes - unproject math |
| `intersectObject(object, recursive)` | Find intersections | Yes - all intersection algorithms |
| `intersectObjects(objects, recursive)` | Batch intersection | No |

**Intersection Result:**
```typescript
{
  distance: number,      // Distance from ray origin
  point: Vector3,        // Intersection point (world)
  face: { a, b, c, normal, materialIndex },
  faceIndex: number,
  object: Object3D,
  uv: Vector2,           // UV coordinates
  uv1: Vector2,          // Second UV set
  normal: Vector3,       // Interpolated normal
  instanceId: number     // For InstancedMesh
}
```

### 2.6 Clock

| Method | Description |
|--------|-------------|
| `start()` | Start clock |
| `stop()` | Stop clock |
| `getElapsedTime()` | Total elapsed time |
| `getDelta()` | Time since last getDelta call |

### 2.7 EventDispatcher

| Method | Description |
|--------|-------------|
| `addEventListener(type, listener)` | Add listener |
| `hasEventListener(type, listener)` | Check listener |
| `removeEventListener(type, listener)` | Remove listener |
| `dispatchEvent(event)` | Dispatch event |

---

**CORE OBJECTS TOTALS:**

| Type | Methods | Proofs Needed |
|------|---------|---------------|
| Object3D | ~50 | ~10 |
| Scene | ~5 | ~2 |
| Group | ~0 | ~0 |
| Layers | ~8 | ~0 |
| Raycaster | ~4 | ~15 |
| Clock | ~4 | ~0 |
| EventDispatcher | ~4 | ~0 |
| **TOTAL** | **~75** | **~27** |

---

## 3. GEOMETRY

Vertex data. The shape of things.

### 3.1 BufferGeometry (Base Class)

**Attributes:**
| Attribute | Type | Description |
|-----------|------|-------------|
| `position` | Float32Array | Vertex positions (x,y,z per vertex) |
| `normal` | Float32Array | Vertex normals |
| `uv` | Float32Array | Texture coordinates |
| `uv1` | Float32Array | Second UV set (lightmaps) |
| `color` | Float32Array | Vertex colors |
| `tangent` | Float32Array | Tangent vectors (for normal mapping) |
| `index` | Uint16/32Array | Triangle indices |

**Methods (35+):**
```
setAttribute, getAttribute, deleteAttribute, hasAttribute, getIndex, setIndex,
setDrawRange, applyMatrix4, applyQuaternion, rotateX, rotateY, rotateZ,
translate, scale, center, normalize, computeBoundingBox, computeBoundingSphere,
computeTangents, computeVertexNormals, toNonIndexed, toJSON, clone, copy,
dispose, merge, groups, addGroup, clearGroups
```

**PROOFS NEEDED:**
- Normal vectors are unit length after `computeVertexNormals`
- Tangent vectors are perpendicular to normals
- Bounding box/sphere correctly contains all vertices

### 3.2 Primitive Geometries

| Geometry | Parameters | Vertices | Triangles |
|----------|------------|----------|-----------|
| `BoxGeometry` | width, height, depth, widthSegs, heightSegs, depthSegs | 24+ | 12+ |
| `PlaneGeometry` | width, height, widthSegs, heightSegs | 4+ | 2+ |
| `CircleGeometry` | radius, segments, thetaStart, thetaLength | segments+1 | segments |
| `RingGeometry` | innerRadius, outerRadius, thetaSegs, phiSegs, thetaStart, thetaLength | varies | varies |
| `SphereGeometry` | radius, widthSegs, heightSegs, phiStart, phiLength, thetaStart, thetaLength | varies | varies |
| `CylinderGeometry` | radiusTop, radiusBottom, height, radialSegs, heightSegs, openEnded, thetaStart, thetaLength | varies | varies |
| `ConeGeometry` | radius, height, radialSegs, heightSegs, openEnded, thetaStart, thetaLength | varies | varies |
| `CapsuleGeometry` | radius, length, capSegs, radialSegs | varies | varies |
| `TorusGeometry` | radius, tube, radialSegs, tubularSegs, arc | varies | varies |
| `TorusKnotGeometry` | radius, tube, tubularSegs, radialSegs, p, q | varies | varies |
| `DodecahedronGeometry` | radius, detail | 20×detail² | 36×detail² |
| `IcosahedronGeometry` | radius, detail | 12×detail² | 20×detail² |
| `OctahedronGeometry` | radius, detail | 6×detail² | 8×detail² |
| `TetrahedronGeometry` | radius, detail | 4×detail² | 4×detail² |
| `PolyhedronGeometry` | vertices, indices, radius, detail | varies | varies |
| `LatheGeometry` | points, segments, phiStart, phiLength | varies | varies |
| `ExtrudeGeometry` | shapes, options | varies | varies |
| `ShapeGeometry` | shapes, curveSegments | varies | varies |
| `TubeGeometry` | path, tubularSegs, radius, radialSegs, closed | varies | varies |
| `EdgesGeometry` | geometry, thresholdAngle | edges×2 | 0 (lines) |
| `WireframeGeometry` | geometry | edges×2 | 0 (lines) |

**PROOFS NEEDED:**
- All vertices of SphereGeometry are exactly `radius` from center
- BoxGeometry faces are perpendicular (dot product = 0)
- TorusKnotGeometry is topologically correct (p,q coprime check)
- All normals point outward (consistent winding)

### 3.3 Buffer Attributes

| Type | Bytes/Element | Range |
|------|---------------|-------|
| `Int8BufferAttribute` | 1 | -128 to 127 |
| `Uint8BufferAttribute` | 1 | 0 to 255 |
| `Uint8ClampedBufferAttribute` | 1 | 0 to 255 (clamped) |
| `Int16BufferAttribute` | 2 | -32768 to 32767 |
| `Uint16BufferAttribute` | 2 | 0 to 65535 |
| `Int32BufferAttribute` | 4 | -2³¹ to 2³¹-1 |
| `Uint32BufferAttribute` | 4 | 0 to 2³²-1 |
| `Float16BufferAttribute` | 2 | Half precision float |
| `Float32BufferAttribute` | 4 | Single precision float |

**Attribute Methods:**
```
setX, setY, setZ, setW, getX, getY, getZ, getW,
setXY, setXYZ, setXYZW, clone, copy, copyArray, copyAt,
set, onUpload, onUploadCallback, normalize, toJSON
```

### 3.4 Instanced Geometry

| Type | Description |
|------|-------------|
| `InstancedBufferGeometry` | Geometry with per-instance attributes |
| `InstancedBufferAttribute` | Per-instance data |
| `InstancedInterleavedBuffer` | Interleaved per-instance data |
| `InterleavedBuffer` | Multiple attributes sharing one buffer |
| `InterleavedBufferAttribute` | Attribute view into interleaved buffer |

---

**GEOMETRY TOTALS:**

| Category | Types | Methods | Proofs Needed |
|----------|-------|---------|---------------|
| BufferGeometry | 1 | ~35 | ~5 |
| Primitives | 21 | ~21 (constructors) | ~15 |
| Attributes | 9 | ~20 each | ~5 |
| Instancing | 5 | ~15 | ~3 |
| **TOTAL** | **36** | **~250** | **~28** |

---

## 4. MATERIALS

How things look. Shading models, textures, transparency.

### 4.1 Material (Base Class)

**Common Properties:**
| Property | Type | Description |
|----------|------|-------------|
| `alphaHash` | boolean | Alpha hashing |
| `alphaTest` | number | Alpha cutoff threshold |
| `alphaToCoverage` | boolean | MSAA alpha |
| `blendDst` | BlendingDstFactor | Destination blend factor |
| `blendDstAlpha` | BlendingDstFactor | Destination alpha blend |
| `blendEquation` | BlendingEquation | Blend equation |
| `blendEquationAlpha` | BlendingEquation | Alpha blend equation |
| `blending` | Blending | Blending mode |
| `blendSrc` | BlendingSrcFactor | Source blend factor |
| `blendSrcAlpha` | BlendingSrcFactor | Source alpha blend |
| `clipIntersection` | boolean | Clip intersection mode |
| `clippingPlanes` | Plane[] | Clipping planes |
| `clipShadows` | boolean | Clip shadows |
| `colorWrite` | boolean | Color write mask |
| `depthFunc` | DepthModes | Depth test function |
| `depthTest` | boolean | Enable depth test |
| `depthWrite` | boolean | Write to depth buffer |
| `forceSinglePass` | boolean | Force single pass |
| `opacity` | number | Opacity (0-1) |
| `polygonOffset` | boolean | Polygon offset |
| `polygonOffsetFactor` | number | Offset factor |
| `polygonOffsetUnits` | number | Offset units |
| `precision` | 'highp'\|'mediump'\|'lowp' | Shader precision |
| `premultipliedAlpha` | boolean | Premultiplied alpha |
| `side` | Side | FrontSide, BackSide, DoubleSide |
| `shadowSide` | Side | Shadow render side |
| `stencilFail` | StencilOp | Stencil fail op |
| `stencilFunc` | StencilFunc | Stencil function |
| `stencilFuncMask` | number | Stencil func mask |
| `stencilRef` | number | Stencil reference |
| `stencilWrite` | boolean | Write to stencil |
| `stencilWriteMask` | number | Stencil write mask |
| `stencilZFail` | StencilOp | Stencil zfail op |
| `stencilZPass` | StencilOp | Stencil zpass op |
| `toneMapped` | boolean | Apply tone mapping |
| `transparent` | boolean | Transparency enabled |
| `vertexColors` | boolean | Use vertex colors |
| `visible` | boolean | Visibility |

### 4.2 Standard Materials

| Material | Use Case | Lighting Model |
|----------|----------|----------------|
| `MeshBasicMaterial` | Unlit, solid colors | None |
| `MeshLambertMaterial` | Matte surfaces | Lambertian |
| `MeshPhongMaterial` | Shiny surfaces | Blinn-Phong |
| `MeshStandardMaterial` | PBR metallic-roughness | Cook-Torrance |
| `MeshPhysicalMaterial` | Advanced PBR | Cook-Torrance + clearcoat, sheen, etc. |
| `MeshToonMaterial` | Cel shading | Toon gradient |
| `MeshNormalMaterial` | Debug normals | None |
| `MeshMatcapMaterial` | Matcap/LitSphere | Matcap lookup |
| `MeshDepthMaterial` | Depth encoding | None |
| `MeshDistanceMaterial` | Point light shadows | None |

### 4.3 MeshStandardMaterial (PBR Reference)

| Property | Type | Description |
|----------|------|-------------|
| `color` | Color | Albedo color |
| `roughness` | number | 0 = mirror, 1 = diffuse |
| `metalness` | number | 0 = dielectric, 1 = metal |
| `map` | Texture | Albedo texture |
| `lightMap` | Texture | Baked lighting |
| `lightMapIntensity` | number | Light map intensity |
| `aoMap` | Texture | Ambient occlusion |
| `aoMapIntensity` | number | AO intensity |
| `emissive` | Color | Emissive color |
| `emissiveIntensity` | number | Emission strength |
| `emissiveMap` | Texture | Emission texture |
| `bumpMap` | Texture | Bump map |
| `bumpScale` | number | Bump intensity |
| `normalMap` | Texture | Normal map |
| `normalMapType` | NormalMapTypes | TangentSpace or ObjectSpace |
| `normalScale` | Vector2 | Normal intensity |
| `displacementMap` | Texture | Displacement map |
| `displacementScale` | number | Displacement amount |
| `displacementBias` | number | Displacement offset |
| `roughnessMap` | Texture | Roughness texture |
| `metalnessMap` | Texture | Metalness texture |
| `alphaMap` | Texture | Alpha texture |
| `envMap` | Texture | Environment map |
| `envMapIntensity` | number | Environment intensity |
| `wireframe` | boolean | Wireframe mode |
| `wireframeLinewidth` | number | Wire thickness |
| `flatShading` | boolean | Flat shading |

### 4.4 MeshPhysicalMaterial (Full PBR)

Extends MeshStandardMaterial with:

| Property | Type | Description |
|----------|------|-------------|
| `clearcoat` | number | Clearcoat layer |
| `clearcoatMap` | Texture | Clearcoat texture |
| `clearcoatRoughness` | number | Clearcoat roughness |
| `clearcoatRoughnessMap` | Texture | Clearcoat roughness texture |
| `clearcoatNormalMap` | Texture | Clearcoat normal map |
| `clearcoatNormalScale` | Vector2 | Clearcoat normal scale |
| `ior` | number | Index of refraction |
| `reflectivity` | number | Reflectivity (derived from ior) |
| `sheen` | number | Sheen intensity |
| `sheenColor` | Color | Sheen tint |
| `sheenColorMap` | Texture | Sheen color texture |
| `sheenRoughness` | number | Sheen roughness |
| `sheenRoughnessMap` | Texture | Sheen roughness texture |
| `transmission` | number | Transmission (glass) |
| `transmissionMap` | Texture | Transmission texture |
| `thickness` | number | Volume thickness |
| `thicknessMap` | Texture | Thickness texture |
| `attenuationColor` | Color | Volume absorption color |
| `attenuationDistance` | number | Absorption distance |
| `specularIntensity` | number | Specular intensity |
| `specularIntensityMap` | Texture | Specular intensity texture |
| `specularColor` | Color | Specular tint |
| `specularColorMap` | Texture | Specular color texture |
| `iridescence` | number | Iridescence intensity |
| `iridescenceMap` | Texture | Iridescence texture |
| `iridescenceIOR` | number | Thin-film IOR |
| `iridescenceThicknessRange` | [number, number] | Thin-film thickness range |
| `iridescenceThicknessMap` | Texture | Thickness texture |
| `anisotropy` | number | Anisotropy strength |
| `anisotropyRotation` | number | Anisotropy angle |
| `anisotropyMap` | Texture | Anisotropy texture |
| `dispersion` | number | Chromatic dispersion |

**PROOFS NEEDED:**
- Energy conservation: reflected + transmitted + absorbed = 1
- Fresnel equations correctness (Schlick approximation)
- GGX normal distribution function
- Smith geometry function

### 4.5 Other Material Types

| Material | Use Case |
|----------|----------|
| `LineBasicMaterial` | Simple lines |
| `LineDashedMaterial` | Dashed lines |
| `PointsMaterial` | Point clouds |
| `SpriteMaterial` | 2D sprites |
| `ShaderMaterial` | Custom shaders |
| `RawShaderMaterial` | No auto-uniforms |
| `ShadowMaterial` | Shadow-only |

### 4.6 Textures

| Type | Description |
|------|-------------|
| `Texture` | Base texture class |
| `CanvasTexture` | From canvas element |
| `VideoTexture` | From video element |
| `DataTexture` | From raw data |
| `Data3DTexture` | 3D texture |
| `DataArrayTexture` | 2D array texture |
| `CubeTexture` | Cubemap |
| `CompressedTexture` | GPU-compressed |
| `CompressedArrayTexture` | Compressed array |
| `CompressedCubeTexture` | Compressed cubemap |
| `DepthTexture` | Depth buffer |
| `FramebufferTexture` | Render target |

**Texture Properties:**
```
image, mapping, channel, wrapS, wrapT, magFilter, minFilter,
anisotropy, format, internalFormat, type, offset, repeat,
center, rotation, generateMipmaps, premultiplyAlpha, flipY,
unpackAlignment, colorSpace, needsUpdate
```

---

**MATERIALS TOTALS:**

| Category | Types | Properties | Proofs Needed |
|----------|-------|------------|---------------|
| Base Material | 1 | ~40 | ~5 |
| Standard Mats | 10 | ~200 | ~15 |
| Physical Mat | 1 | ~30 | ~10 |
| Other Mats | 7 | ~50 | ~2 |
| Textures | 12 | ~20 each | ~5 |
| **TOTAL** | **31** | **~560** | **~37** |

---

## 5. LIGHTS

Illumination. Without light, there is nothing to see.

### 5.1 Light (Base Class)

| Property | Type | Description |
|----------|------|-------------|
| `color` | Color | Light color |
| `intensity` | number | Light intensity |

### 5.2 Light Types

| Light | Properties | Shadow | Use Case |
|-------|------------|--------|----------|
| `AmbientLight` | color, intensity | No | Global fill light |
| `DirectionalLight` | color, intensity, position, target | Yes | Sun, distant light |
| `PointLight` | color, intensity, distance, decay | Yes | Bulbs, candles |
| `SpotLight` | color, intensity, distance, angle, penumbra, decay, target | Yes | Flashlights, stage lights |
| `HemisphereLight` | color, groundColor, intensity | No | Sky + ground ambient |
| `RectAreaLight` | color, intensity, width, height | No (special) | Area lights, soft boxes |
| `LightProbe` | sh (SphericalHarmonics3) | No | Baked irradiance |

### 5.3 Light Properties Detail

**DirectionalLight:**
```typescript
{
  color: Color,
  intensity: number,
  position: Vector3,      // Light direction = position.normalize()
  target: Object3D,       // Look-at target
  shadow: DirectionalLightShadow
}
```

**PointLight:**
```typescript
{
  color: Color,
  intensity: number,      // Candela when physicallyCorrect
  distance: number,       // Cutoff distance (0 = infinite)
  decay: number,          // Attenuation (2 = physically correct)
  shadow: PointLightShadow
}
```

**SpotLight:**
```typescript
{
  color: Color,
  intensity: number,      // Candela when physicallyCorrect
  distance: number,       // Cutoff distance
  angle: number,          // Cone angle (radians, max π/2)
  penumbra: number,       // Soft edge (0-1)
  decay: number,          // Attenuation
  target: Object3D,       // Look-at target
  shadow: SpotLightShadow
}
```

**PROOFS NEEDED:**
- Point light falloff: `intensity / (distance²)` for physically correct
- Spot light cone: `cos(angle)` threshold
- Hemisphere interpolation: `mix(groundColor, color, normal.y * 0.5 + 0.5)`

### 5.4 Shadows

**LightShadow (Base):**
| Property | Type | Description |
|----------|------|-------------|
| `camera` | Camera | Shadow camera |
| `bias` | number | Depth bias |
| `normalBias` | number | Normal offset bias |
| `radius` | number | Blur radius |
| `blurSamples` | number | PCF samples |
| `mapSize` | Vector2 | Shadow map resolution |
| `map` | RenderTarget | Shadow map |
| `matrix` | Matrix4 | World → shadow space |

**DirectionalLightShadow:**
- Uses OrthographicCamera
- `camera.left/right/top/bottom/near/far`

**PointLightShadow:**
- Uses PerspectiveCamera
- Renders to CubeMap (6 faces)

**SpotLightShadow:**
- Uses PerspectiveCamera
- `camera.fov` derived from `light.angle`

**Shadow Mapping Algorithm:**
1. Render scene from light's POV to depth texture
2. For each fragment, transform to light space
3. Compare fragment depth to shadow map
4. If fragment is further, it's in shadow

**PROOFS NEEDED:**
- Shadow matrix: `bias × projection × view × model`
- Depth comparison correctness
- Cascade shadow map split calculations (CSM)

### 5.5 Physically Correct Lighting

When `renderer.useLegacyLights = false`:

| Light | Unit | Formula |
|-------|------|---------|
| DirectionalLight | lux (lm/m²) | intensity directly |
| PointLight | candela (cd) | `intensity / (4π × distance²)` |
| SpotLight | candela (cd) | `intensity / (4π × distance²)` with cone |
| RectAreaLight | nits (cd/m²) | `intensity / area` |

---

**LIGHTS TOTALS:**

| Category | Types | Properties | Proofs Needed |
|----------|-------|------------|---------------|
| Light Base | 1 | ~2 | ~0 |
| Light Types | 7 | ~35 | ~10 |
| Shadows | 4 | ~20 | ~8 |
| **TOTAL** | **12** | **~57** | **~18** |

---

## 6. CAMERAS

The eye. How we see into the 3D world.

### 6.1 Camera (Base Class)

| Property | Type | Description |
|----------|------|-------------|
| `matrixWorldInverse` | Matrix4 | Inverse of world matrix (view matrix) |
| `projectionMatrix` | Matrix4 | Projection matrix |
| `projectionMatrixInverse` | Matrix4 | Inverse projection |

**Methods:**
```
getWorldDirection, updateMatrixWorld, updateWorldMatrix,
clone, copy, toJSON
```

### 6.2 PerspectiveCamera

The standard 3D camera with perspective projection.

| Property | Type | Description |
|----------|------|-------------|
| `fov` | number | Vertical field of view (degrees) |
| `aspect` | number | Width / height |
| `near` | number | Near clipping plane |
| `far` | number | Far clipping plane |
| `focus` | number | Focus distance (for stereo) |
| `filmGauge` | number | Film size (default 35mm) |
| `filmOffset` | number | Horizontal film offset |
| `zoom` | number | Zoom factor |
| `view` | Object | Sub-view for multi-window |

**Methods:**
```
setFocalLength, getFocalLength, getEffectiveFOV,
getFilmWidth, getFilmHeight, getViewBounds, setViewOffset,
clearViewOffset, updateProjectionMatrix, toJSON
```

**Projection Matrix (perspective):**
```
| 2n/(r-l)    0       (r+l)/(r-l)    0     |
|    0     2n/(t-b)   (t+b)/(t-b)    0     |
|    0        0      -(f+n)/(f-n)  -2fn/(f-n) |
|    0        0          -1          0     |
```

Where:
- `t = near × tan(fov/2)`
- `b = -t`
- `r = t × aspect`
- `l = -r`

**PROOFS NEEDED:**
- Perspective divide produces correct NDC coordinates
- Near/far planes map to [-1, 1] (or [0, 1] for WebGPU)
- Frustum planes correctly extracted from matrix

### 6.3 OrthographicCamera

No perspective distortion. Parallel projection.

| Property | Type | Description |
|----------|------|-------------|
| `left` | number | Left plane |
| `right` | number | Right plane |
| `top` | number | Top plane |
| `bottom` | number | Bottom plane |
| `near` | number | Near plane |
| `far` | number | Far plane |
| `zoom` | number | Zoom factor |
| `view` | Object | Sub-view |

**Projection Matrix (orthographic):**
```
| 2/(r-l)    0        0      -(r+l)/(r-l) |
|    0    2/(t-b)     0      -(t+b)/(t-b) |
|    0       0     -2/(f-n)  -(f+n)/(f-n) |
|    0       0        0           1       |
```

**PROOFS NEEDED:**
- Orthographic projection preserves parallel lines
- Size is independent of distance

### 6.4 ArrayCamera

Multiple cameras rendering to different viewports.

| Property | Type | Description |
|----------|------|-------------|
| `cameras` | PerspectiveCamera[] | Array of cameras |

### 6.5 CubeCamera

Six cameras for cubemap rendering.

| Property | Type | Description |
|----------|------|-------------|
| `renderTarget` | WebGLCubeRenderTarget | Output cubemap |

**Methods:**
```
update(renderer, scene)
```

### 6.6 StereoCamera

For VR/stereoscopic rendering.

| Property | Type | Description |
|----------|------|-------------|
| `aspect` | number | Aspect ratio |
| `eyeSep` | number | Eye separation |
| `cameraL` | PerspectiveCamera | Left eye |
| `cameraR` | PerspectiveCamera | Right eye |

**Methods:**
```
update(camera)
```

---

**CAMERAS TOTALS:**

| Type | Properties | Methods | Proofs Needed |
|------|------------|---------|---------------|
| Camera | ~3 | ~5 | ~0 |
| PerspectiveCamera | ~10 | ~10 | ~8 |
| OrthographicCamera | ~8 | ~5 | ~4 |
| ArrayCamera | ~1 | ~0 | ~0 |
| CubeCamera | ~1 | ~1 | ~0 |
| StereoCamera | ~4 | ~1 | ~2 |
| **TOTAL** | **~27** | **~22** | **~14** |

---

## 7. ANIMATION

Motion. Bringing the static to life.

### 7.1 Animation System Overview

```
AnimationClip ─────► AnimationMixer ─────► AnimationAction
     │                     │                      │
     ▼                     ▼                      ▼
KeyframeTracks        updates targets        playback control
```

### 7.2 AnimationClip

Container for animation data.

| Property | Type | Description |
|----------|------|-------------|
| `name` | string | Clip name |
| `uuid` | string | Unique ID |
| `duration` | number | Length in seconds |
| `tracks` | KeyframeTrack[] | Animation tracks |
| `blendMode` | AnimationBlendMode | NormalAnimationBlendMode or AdditiveAnimationBlendMode |

**Methods:**
```
resetDuration, trim, validate, optimize, clone, toJSON
```

**Static Methods:**
```
parse, toJSON, CreateFromMorphTargetSequence,
findByName, CreateClipsFromMorphTargetSequences
```

### 7.3 KeyframeTrack

Single animated property.

| Type | Interpolation | Use Case |
|------|---------------|----------|
| `VectorKeyframeTrack` | Linear | Position, scale |
| `QuaternionKeyframeTrack` | Spherical | Rotation |
| `NumberKeyframeTrack` | Linear | Opacity, intensity |
| `ColorKeyframeTrack` | Linear | Color properties |
| `BooleanKeyframeTrack` | Discrete | Visibility |
| `StringKeyframeTrack` | Discrete | Morph targets |

**Properties:**
| Property | Type | Description |
|----------|------|-------------|
| `name` | string | Property path (e.g., ".position") |
| `times` | Float32Array | Keyframe times |
| `values` | TypedArray | Keyframe values |
| `interpolation` | InterpolateDiscrete/Linear/Smooth | Interpolation mode |

**Methods:**
```
getInterpolation, setInterpolation, getValueSize,
shift, scale, trim, validate, optimize, clone, toJSON
```

**PROOFS NEEDED:**
- Quaternion slerp produces valid unit quaternions
- Cubic interpolation is C1 continuous
- Time scaling preserves relative keyframe positions

### 7.4 AnimationMixer

Playback controller for a target object.

| Property | Type | Description |
|----------|------|-------------|
| `time` | number | Global mixer time |
| `timeScale` | number | Playback speed |

**Methods:**
```
clipAction(clip, root), existingAction(clip, root),
stopAllAction, update(deltaTime), setTime(time),
getRoot, uncacheClip, uncacheRoot, uncacheAction
```

### 7.5 AnimationAction

Individual clip playback state.

| Property | Type | Description |
|----------|------|-------------|
| `blendMode` | AnimationBlendMode | Normal or Additive |
| `clampWhenFinished` | boolean | Hold last frame |
| `enabled` | boolean | Active state |
| `loop` | LoopMode | LoopOnce, LoopRepeat, LoopPingPong |
| `paused` | boolean | Pause state |
| `repetitions` | number | Loop count |
| `time` | number | Local time |
| `timeScale` | number | Local time scale |
| `weight` | number | Blend weight (0-1) |
| `zeroSlopeAtEnd` | boolean | Smooth end |
| `zeroSlopeAtStart` | boolean | Smooth start |

**Methods:**
```
play, stop, reset, isRunning, isScheduled,
startAt(time), setLoop(mode, repetitions),
setEffectiveWeight(weight), getEffectiveWeight,
fadeIn(duration), fadeOut(duration),
crossFadeFrom(action, duration, warp),
crossFadeTo(action, duration, warp),
stopFading, setEffectiveTimeScale(timeScale),
getEffectiveTimeScale, setDuration(duration),
syncWith(action), halt(duration), warp(startScale, endScale, duration),
stopWarping, getMixer, getClip, getRoot
```

**PROOFS NEEDED:**
- Blend weights sum to 1 (normalized)
- CrossFade produces smooth transitions
- Time warping is continuous

### 7.6 PropertyBinding

Binds animation tracks to object properties.

| Property | Type | Description |
|----------|------|-------------|
| `path` | string | Property path |
| `parsedPath` | Object | Parsed path components |
| `node` | Object3D | Target object |
| `rootNode` | Object3D | Root of hierarchy |

**Path Syntax:**
```
.position           // Direct property
.position[x]        // Component
.bones[2].position  // Indexed + nested
.morphTargetInfluences[smile] // Named index
```

### 7.7 AnimationObjectGroup

Shared animation state across multiple objects.

### 7.8 Skeleton & Bones

| Type | Description |
|------|-------------|
| `Bone` | Joint in skeleton hierarchy |
| `Skeleton` | Collection of bones with bind poses |
| `SkinnedMesh` | Mesh deformed by skeleton |

**Skeleton Properties:**
| Property | Type | Description |
|----------|------|-------------|
| `bones` | Bone[] | Bone array |
| `boneInverses` | Matrix4[] | Inverse bind matrices |
| `boneMatrices` | Float32Array | Flattened bone matrices |
| `boneTexture` | DataTexture | GPU bone data |

**PROOFS NEEDED:**
- Skinning: `vertex' = Σ(weight[i] × boneMatrix[i] × bindInverse[i] × vertex)`
- Weights sum to 1
- Bone hierarchy respects parent transforms

---

**ANIMATION TOTALS:**

| Category | Types | Methods | Proofs Needed |
|----------|-------|---------|---------------|
| Clips | 1 | ~10 | ~2 |
| Tracks | 6 | ~12 each | ~5 |
| Mixer | 1 | ~10 | ~2 |
| Action | 1 | ~25 | ~5 |
| Binding | 1 | ~10 | ~2 |
| Skeleton | 3 | ~15 | ~5 |
| **TOTAL** | **13** | **~140** | **~21** |

---

## 8. LOADERS

Getting data in. Asset pipelines.

### 8.1 Loader (Base Class)

| Property | Type | Description |
|----------|------|-------------|
| `crossOrigin` | string | CORS mode |
| `withCredentials` | boolean | Send cookies |
| `path` | string | Base path |
| `resourcePath` | string | Resource path |
| `manager` | LoadingManager | Loading manager |
| `requestHeader` | Object | HTTP headers |

**Methods:**
```
load(url, onLoad, onProgress, onError),
loadAsync(url, onProgress),
setCrossOrigin, setWithCredentials, setPath,
setResourcePath, setRequestHeader
```

### 8.2 Core Loaders

| Loader | Output | Format |
|--------|--------|--------|
| `FileLoader` | string/ArrayBuffer | Raw files |
| `ImageLoader` | HTMLImageElement | Images |
| `ImageBitmapLoader` | ImageBitmap | Images (offscreen) |
| `TextureLoader` | Texture | Image → Texture |
| `CubeTextureLoader` | CubeTexture | 6 images → Cubemap |
| `DataTextureLoader` | DataTexture | HDR/EXR |
| `CompressedTextureLoader` | CompressedTexture | DDS/KTX |
| `AudioLoader` | AudioBuffer | Audio files |
| `BufferGeometryLoader` | BufferGeometry | JSON geometry |
| `MaterialLoader` | Material | JSON material |
| `ObjectLoader` | Object3D | JSON scene |
| `AnimationLoader` | AnimationClip[] | JSON animations |

### 8.3 Format-Specific Loaders (Addons)

| Loader | Format | Notes |
|--------|--------|-------|
| `GLTFLoader` | glTF/GLB | **PRIMARY FORMAT** |
| `DRACOLoader` | Draco | Compressed geometry |
| `KTX2Loader` | KTX2 | GPU texture compression |
| `FBXLoader` | FBX | Autodesk format |
| `OBJLoader` | OBJ | Wavefront |
| `MTLLoader` | MTL | OBJ materials |
| `ColladaLoader` | DAE | COLLADA |
| `STLLoader` | STL | 3D printing |
| `PLYLoader` | PLY | Point clouds |
| `PCDLoader` | PCD | Point Cloud Data |
| `EXRLoader` | EXR | HDR images |
| `HDRLoader` | RGBE | HDR images |
| `SVGLoader` | SVG | Vector graphics |
| `FontLoader` | Typeface.js | Text fonts |
| `LDrawLoader` | LDraw | LEGO models |
| `3MFLoader` | 3MF | 3D printing |
| `AMFLoader` | AMF | Additive manufacturing |
| `BVHLoader` | BVH | Motion capture |
| `GCodeLoader` | G-code | CNC/3D printing |
| `MDDLoader` | MDD | Point cache |
| `NRRDLoader` | NRRD | Medical imaging |
| `PDBLoader` | PDB | Molecular data |
| `TDSLoader` | 3DS | 3D Studio |
| `TTFLoader` | TTF/OTF | TrueType fonts |
| `VOXLoader` | VOX | MagicaVoxel |
| `VRMLLoader` | VRML | Legacy 3D |
| `VTKLoader` | VTK | Scientific vis |
| `XYZLoader` | XYZ | Point clouds |

### 8.4 LoadingManager

Coordinates multiple loaders.

| Property | Type | Description |
|----------|------|-------------|
| `onStart` | Function | First item starts |
| `onLoad` | Function | All items complete |
| `onProgress` | Function | Item completes |
| `onError` | Function | Item fails |

**Methods:**
```
getHandler(file), addHandler(regex, loader),
removeHandler(regex), resolveURL(url),
setURLModifier(callback), itemStart(url),
itemEnd(url), itemError(url)
```

### 8.5 Cache

Global asset cache.

| Property/Method | Description |
|-----------------|-------------|
| `enabled` | Enable caching |
| `files` | Cached files |
| `add(key, file)` | Add to cache |
| `get(key)` | Get from cache |
| `remove(key)` | Remove from cache |
| `clear()` | Clear all |

---

**LOADERS TOTALS:**

| Category | Types | Methods |
|----------|-------|---------|
| Base Loader | 1 | ~10 |
| Core Loaders | 12 | ~12 |
| Format Loaders | 30+ | ~30+ |
| Manager/Cache | 2 | ~15 |
| **TOTAL** | **45+** | **~67+** |

---

## 9. RENDERERS

The final step. Pixels on screen.

### 9.1 WebGLRenderer

| Property | Type | Description |
|----------|------|-------------|
| `domElement` | HTMLCanvasElement | Canvas element |
| `debug` | Object | Debug info |
| `autoClear` | boolean | Auto clear before render |
| `autoClearColor` | boolean | Clear color buffer |
| `autoClearDepth` | boolean | Clear depth buffer |
| `autoClearStencil` | boolean | Clear stencil buffer |
| `sortObjects` | boolean | Sort transparent objects |
| `clippingPlanes` | Plane[] | Global clipping planes |
| `localClippingEnabled` | boolean | Per-object clipping |
| `outputColorSpace` | ColorSpace | Output color space |
| `toneMapping` | ToneMapping | Tone mapping mode |
| `toneMappingExposure` | number | Exposure value |
| `info` | Object | Render statistics |
| `shadowMap` | WebGLShadowMap | Shadow map renderer |
| `xr` | WebXRManager | XR (VR/AR) manager |
| `capabilities` | Object | WebGL capabilities |
| `extensions` | Object | Loaded extensions |
| `properties` | Object | Object properties cache |
| `state` | WebGLState | GL state manager |

**Methods:**
```
getContext, getContextAttributes, forceContextLoss,
forceContextRestore, getPixelRatio, setPixelRatio,
getSize, setSize, getDrawingBufferSize, setDrawingBufferSize,
getCurrentViewport, getViewport, setViewport,
getScissor, setScissor, getScissorTest, setScissorTest,
getClearColor, setClearColor, getClearAlpha, setClearAlpha,
clear(color, depth, stencil), clearColor, clearDepth, clearStencil,
clearTarget(target, color, depth, stencil),
dispose, renderBufferDirect, renderBufferImmediate,
render(scene, camera), compile(scene, camera, target),
compileAsync(scene, camera, target),
setAnimationLoop(callback), getAnimationLoop,
setOpaqueSort(method), setTransparentSort(method),
getRenderTarget, setRenderTarget(target, activeCubeFace, activeMipmapLevel),
readRenderTargetPixels(target, x, y, width, height, buffer, activeCubeFace),
readRenderTargetPixelsAsync(target, x, y, width, height, buffer, activeCubeFace),
copyFramebufferToTexture(texture, position, level),
copyTextureToTexture(srcTexture, dstTexture, srcRegion, dstPosition, level),
copyTextureToTexture3D(srcTexture, dstTexture, srcRegion, dstPosition, level),
initRenderTarget(target), initTexture(texture), resetState
```

### 9.2 WebGPURenderer

Next-generation renderer using WebGPU API.

Same interface as WebGLRenderer but with:
- Compute shaders
- Better multi-threading
- Modern GPU features
- TSL (Three Shading Language) nodes

### 9.3 Render Targets

| Type | Description |
|------|-------------|
| `WebGLRenderTarget` | Offscreen render target |
| `WebGLCubeRenderTarget` | Cubemap render target |
| `WebGLArrayRenderTarget` | 2D array render target |
| `WebGL3DRenderTarget` | 3D render target |

**RenderTarget Properties:**
| Property | Type | Description |
|----------|------|-------------|
| `width` | number | Width in pixels |
| `height` | number | Height in pixels |
| `depth` | number | Depth (for 3D) |
| `scissor` | Vector4 | Scissor rectangle |
| `scissorTest` | boolean | Enable scissor |
| `viewport` | Vector4 | Viewport |
| `texture` | Texture | Color attachment |
| `depthBuffer` | boolean | Has depth buffer |
| `stencilBuffer` | boolean | Has stencil buffer |
| `depthTexture` | DepthTexture | Depth attachment |
| `samples` | number | MSAA samples |

### 9.4 Render Pipeline

```
1. Frustum Culling
   └─ For each object: test against camera frustum
   
2. Sort Objects
   └─ Opaque: front-to-back (early Z)
   └─ Transparent: back-to-front (correct blending)
   
3. Shadow Pass (if shadows enabled)
   └─ For each shadow-casting light:
      └─ Render scene from light's POV to shadow map
      
4. Main Pass
   └─ For each visible object:
      ├─ Bind material/shader
      ├─ Upload uniforms (matrices, lights, textures)
      ├─ Bind geometry (VAO/VBO)
      └─ Draw call
      
5. Post-Processing (if enabled)
   └─ Render to screen quad with effect shaders
```

### 9.5 WebXRManager

| Method | Description |
|--------|-------------|
| `enabled` | Enable XR |
| `isPresenting` | Currently in XR |
| `getController(index)` | Get controller |
| `getControllerGrip(index)` | Get grip space |
| `getHand(index)` | Get hand tracking |
| `setFramebufferScaleFactor(value)` | Resolution scale |
| `setReferenceSpaceType(type)` | Reference space |
| `getReferenceSpace()` | Get reference space |
| `setSession(session)` | Set XR session |
| `getSession()` | Get XR session |
| `getCamera()` | Get XR camera |
| `setFoveation(value)` | Foveated rendering |
| `getFoveation()` | Get foveation |
| `getDepthSensing()` | Depth sensing |

---

**RENDERERS TOTALS:**

| Category | Types | Methods |
|----------|-------|---------|
| WebGLRenderer | 1 | ~50 |
| WebGPURenderer | 1 | ~50 |
| Render Targets | 4 | ~15 |
| XR Manager | 1 | ~15 |
| **TOTAL** | **7** | **~130** |

---

## 10. EXTRAS

Everything else. Controls, helpers, effects.

### 10.1 Controls (Addons)

| Control | Description |
|---------|-------------|
| `OrbitControls` | Orbit around target point |
| `MapControls` | Map-style pan/zoom |
| `TrackballControls` | Unconstrained rotation |
| `FlyControls` | Flight simulator style |
| `FirstPersonControls` | FPS-style |
| `PointerLockControls` | Pointer lock FPS |
| `DragControls` | Drag objects |
| `TransformControls` | Gizmo for translate/rotate/scale |
| `ArcballControls` | Arcball rotation |

### 10.2 Helpers

| Helper | Description |
|--------|-------------|
| `AxesHelper` | RGB XYZ axes |
| `BoxHelper` | Wireframe box around object |
| `Box3Helper` | Wireframe Box3 |
| `CameraHelper` | Visualize camera frustum |
| `DirectionalLightHelper` | Visualize directional light |
| `GridHelper` | Ground grid |
| `PolarGridHelper` | Polar coordinate grid |
| `HemisphereLightHelper` | Visualize hemisphere light |
| `PlaneHelper` | Visualize plane |
| `PointLightHelper` | Visualize point light |
| `SkeletonHelper` | Visualize bone hierarchy |
| `SpotLightHelper` | Visualize spot light cone |
| `ArrowHelper` | 3D arrow |

### 10.3 Post-Processing (Addons)

**EffectComposer Pipeline:**
```
Scene Render → Pass 1 → Pass 2 → ... → Screen
```

| Pass | Effect |
|------|--------|
| `RenderPass` | Render scene to texture |
| `ShaderPass` | Custom shader |
| `BloomPass` | Glow/bloom |
| `UnrealBloomPass` | Unreal-style bloom |
| `SSAOPass` | Screen-space ambient occlusion |
| `SAOPass` | Scalable ambient occlusion |
| `SSRPass` | Screen-space reflections |
| `BokehPass` | Depth of field |
| `OutlinePass` | Object outlines |
| `FXAAPass` | Anti-aliasing |
| `SMAAPass` | Subpixel morphological AA |
| `TAARenderPass` | Temporal AA |
| `FilmPass` | Film grain/scanlines |
| `GlitchPass` | Glitch effect |
| `HalftonePass` | Halftone dots |
| `DotScreenPass` | Dot screen |
| `AfterimagePass` | Motion blur/trails |
| `GTAOPass` | Ground truth AO |
| `LUTPass` | Color LUT |
| `MaskPass` | Stencil masking |
| `ClearPass` | Clear buffers |

### 10.4 Curves (Addons)

| Curve | Description |
|-------|-------------|
| `CatmullRomCurve3` | Smooth spline through points |
| `CubicBezierCurve` | 2D cubic bezier |
| `CubicBezierCurve3` | 3D cubic bezier |
| `QuadraticBezierCurve` | 2D quadratic bezier |
| `QuadraticBezierCurve3` | 3D quadratic bezier |
| `LineCurve` | 2D line segment |
| `LineCurve3` | 3D line segment |
| `ArcCurve` | 2D arc |
| `EllipseCurve` | 2D ellipse |
| `SplineCurve` | 2D spline |
| `CurvePath` | Composite curve |
| `Path` | 2D path (for shapes) |
| `Shape` | 2D shape (with holes) |

### 10.5 Math Utilities (Addons)

| Utility | Description |
|---------|-------------|
| `OBB` | Oriented bounding box |
| `Capsule` | Capsule primitive |
| `ConvexHull` | Convex hull algorithm |
| `Octree` | Spatial partitioning |
| `SimplexNoise` | Simplex noise |
| `ImprovedNoise` | Perlin noise |
| `Lut` | Color lookup table |
| `MeshSurfaceSampler` | Sample points on mesh |

### 10.6 Exporters (Addons)

| Exporter | Format |
|----------|--------|
| `GLTFExporter` | glTF/GLB |
| `OBJExporter` | OBJ |
| `STLExporter` | STL |
| `PLYExporter` | PLY |
| `ColladaExporter` | COLLADA |
| `USDZExporter` | USDZ (Apple AR) |
| `DRACOExporter` | Draco compressed |
| `EXRExporter` | EXR HDR |

### 10.7 Modifiers (Addons)

| Modifier | Description |
|----------|-------------|
| `SimplifyModifier` | Reduce polygon count |
| `TessellateModifier` | Subdivide triangles |
| `EdgeSplitModifier` | Split hard edges |

### 10.8 Special Objects (Addons)

| Object | Description |
|--------|-------------|
| `Reflector` | Planar reflection |
| `Refractor` | Planar refraction |
| `Water` | Water surface |
| `Sky` | Procedural sky |
| `Lensflare` | Lens flare effect |
| `MarchingCubes` | Isosurface extraction |
| `GPUComputationRenderer` | GPGPU |

---

**EXTRAS TOTALS:**

| Category | Types |
|----------|-------|
| Controls | 9 |
| Helpers | 13 |
| Post-Processing | 21 |
| Curves | 13 |
| Math Utils | 8 |
| Exporters | 8 |
| Modifiers | 3 |
| Special Objects | 7 |
| **TOTAL** | **82** |

---

## PROOF REQUIREMENTS

What needs formal verification. The mathematical bedrock.

### Critical Path (Must Have)

These proofs are **non-negotiable** for billion-agent operation:

#### Tier 1: Core Math ✅ ALL COMPLETE

| Module | Theorem | Status |
|--------|---------|--------|
| Vec3 | `cross_perp_left/right` | ✅ DONE — Cross product perpendicularity |
| Vec3 | `normalize_length = 1` | ✅ DONE — Unit vectors |
| Vec3 | `dot_self_eq_zero` | ✅ DONE — Zero vector characterization |
| Mat4 | `(A×B)×C = A×(B×C)` | ✅ DONE — mul_assoc in Mat4.lean |
| Mat4 | `(A×B)⁻¹ = B⁻¹×A⁻¹` | ✅ DONE — inverse_mul_eq in Mat4Inverse.lean |
| Mat4 | `det(A×B) = det(A)×det(B)` | ✅ DONE — det_mul in Mat4.lean |
| Quat | `slerp(q,q,t) = q` | ✅ DONE — slerp_self in Quaternion.lean |
| Quat | `q×q⁻¹ = identity` | ✅ DONE — mul_inverse in Quaternion.lean |
| Quat | Unit quaternion IsUnit | ✅ DONE — IsUnit predicate in Quaternion.lean |

#### Tier 2: Geometric Primitives ✅ ALL COMPLETE

| Module | Theorem | Status |
|--------|---------|--------|
| Ray | Ray-sphere intersection | ✅ DONE — intersectSphere in Ray.lean |
| Ray | Ray-plane intersection | ✅ DONE — intersectPlane in Ray.lean |
| Ray | Ray-box intersection | ✅ DONE — intersectBox in Ray.lean |
| Box3 | AABB containment | ✅ DONE — containsPoint in Box3.lean |
| Box3 | AABB-AABB intersection | ✅ DONE — intersectsBox in Box3.lean |
| Frustum | Point containment | ✅ DONE — containsPoint in Frustum.lean |
| Frustum | Box/Sphere intersection | ✅ DONE — intersectsBox, intersectsSphere in Frustum.lean |

#### Tier 3: Transformations ✅ ALL COMPLETE

| Module | Theorem | Status |
|--------|---------|--------|
| Mat4 | Translation, rotation, scale composition | ✅ DONE — makeTranslation, makeRotation, makeScale in Mat4.lean |
| Mat4 | Perspective projection | ✅ DONE — makePerspective in Mat4Projection.lean |
| Mat4 | Orthographic projection | ✅ DONE — makeOrthographic in Mat4Projection.lean |
| Scene | Scene graph multiplication | ✅ DONE — updateWorldMatrix in Scene/Graph.lean |
| Scene | Node parent-child relationships | ✅ DONE — Scene/Node.lean |

#### Tier 4: Rendering Math ✅ ALL COMPLETE

| Module | Theorem | Status |
|--------|---------|--------|
| BRDF | Fresnel (Schlick) | ✅ DONE — fresnel_schlick in Material/BRDF.lean |
| BRDF | GGX distribution | ✅ DONE — ggx_distribution in Material/BRDF.lean |
| BRDF | Smith geometry | ✅ DONE — smith_geometry in Material/BRDF.lean |
| BRDF | Cook-Torrance | ✅ DONE — cook_torrance in Material/BRDF.lean |
| Light | Attenuation | ✅ DONE — Light/Attenuation.lean |
| Shadow | Shadow mapping | ✅ DONE — Light/Shadow.lean |

### Implementation Order

```
PHASE 1: Foundation ✅ COMPLETE
├─ Bounded.lean ✅ DONE
├─ Vec2.lean ✅ DONE
├─ Vec3.lean ✅ DONE  
├─ Vec4.lean ✅ DONE
└─ Math/Core.purs ✅ DONE (pure PureScript)

PHASE 2: Matrices & Rotations ✅ COMPLETE
├─ Mat3.lean ✅ DONE (with inverse)
├─ Mat4.lean ✅ DONE
├─ Mat4Inverse.lean ✅ DONE
├─ Mat4Projection.lean ✅ DONE
├─ Quaternion.lean ✅ DONE (with SLERP)
└─ Euler.lean ✅ DONE (all 6 orders)

PHASE 3: Geometric Primitives ✅ COMPLETE
├─ Ray.lean ✅ DONE
├─ Box3.lean ✅ DONE
├─ Sphere.lean ✅ DONE
├─ Plane.lean ✅ DONE
├─ Frustum.lean ✅ DONE
└─ Triangle.lean ✅ DONE

PHASE 4: Camera/Light/Material ✅ COMPLETE
├─ Camera/ ✅ DONE (Types, Lens, Projection)
├─ Light/ ✅ DONE (6 files: Types, Attenuation, Directional, Point, Spot, Shadow)
└─ Material/ ✅ DONE (5 files: Types, Layer, BRDF, Sparkle, ISP)

PHASE 5: Scene Graph ✅ COMPLETE
├─ Scene/Node.lean ✅ DONE
├─ Scene/Graph.lean ✅ DONE
├─ Scene/Resource.lean ✅ DONE
└─ Scene/Diff.lean ✅ DONE

PHASE 6: PureScript Generation ⏳ NEXT
├─ Generate Vec2/Vec3/Vec4 from Lean proofs
├─ Generate Mat3/Mat4 from Lean proofs
├─ Generate Quaternion/Euler from Lean proofs
├─ Generate primitives from Lean proofs
└─ Build pure WebGL2 runtime (no Three.js FFI)
```

---

## GRAND TOTALS

| Category | Types | Methods | Proofs Needed | Proofs Done |
|----------|-------|---------|---------------|-------------|
| 1. Math Foundation | 41 | ~527 | ~105 | **~95** ✅ |
| 2. Core Objects | 7 | ~75 | ~27 | ~5 |
| 3. Geometry | 36 | ~250 | ~28 | **~28** ✅ |
| 4. Materials | 31 | ~560 | ~37 | **~37** ✅ |
| 5. Lights | 12 | ~57 | ~18 | **~18** ✅ |
| 6. Cameras | 6 | ~49 | ~14 | **~14** ✅ |
| 7. Animation | 13 | ~140 | ~21 | ~0 |
| 8. Loaders | 45+ | ~67+ | ~0 | ~0 |
| 9. Renderers | 7 | ~130 | ~0 | ~0 |
| 10. Extras | 82 | varies | ~10 | ~0 |
| **TOTAL** | **~280** | **~1,900+** | **~260** | **~197** ✅ |

**Proof Progress: ~76% complete**

Remaining work is primarily in:
- Animation (skeletal, keyframes)
- Core Objects (Object3D scene graph methods)
- Some Math utilities (random, power-of-two)

---

## WHAT "DONE" MEANS

For each type to be considered complete:

1. **Lean4 Proof File**
   - All operations defined
   - All invariants proven
   - No `sorry`, no `axiom`, no escape hatches

2. **PureScript Generation**
   - Generated code from Lean definitions
   - Type signatures match Lean
   - Comments reference proven theorems

3. **Test Coverage**
   - Property-based tests
   - Edge cases (zero vectors, identity matrices, etc.)
   - Numerical stability tests

4. **Documentation**
   - Mathematical background
   - Usage examples
   - Invariant guarantees

---

## THE GOAL

```
┌─────────────────────────────────────────────────────────────────────────┐
│                                                                         │
│   Three.js is ~150,000 lines of JavaScript with zero formal proofs.    │
│                                                                         │
│   Hydrogen will be ~50,000 lines of PureScript backed by ~20,000       │
│   lines of Lean4 proofs.                                                │
│                                                                         │
│   Every cross product. Every matrix multiply. Every ray intersection.   │
│   PROVEN CORRECT.                                                       │
│                                                                         │
│   When a billion agents use this code simultaneously, there will be     │
│   ZERO runtime checks because the math is correct BY CONSTRUCTION.      │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

---

*"I like these calm little moments before the storm."*
— Stansfield

---

## Document History

| Date | Status | Notes |
|------|--------|-------|
| 2026-02-24 | **AUDIT COMPLETE** | Added comprehensive implementation audit, updated all status markers |
| 2026-02-24 | PROOFS COMPLETE | All Lean4 proofs finished (0 sorry, 3173 jobs) |
| 2026-02-21 | DRAFT | Initial roadmap |

---

Document Status: **AUDIT COMPLETE — PROOFS DONE, PURESCRIPT GENERATION NEXT**
Last Updated: 2026-02-24

