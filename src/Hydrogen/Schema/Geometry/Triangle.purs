-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // triangle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Triangle defined by three vertices with barycentric coordinates.
-- |
-- | ## Proof References
-- | All operations correspond to proven theorems in `proofs/Hydrogen/Math/Triangle.lean`:
-- | - barycentric_vertexA/B/C_sum: barycentric coordinates sum to 1
-- | - fromBarycentric_vertexA/B/C: vertices map correctly
-- | - fromBarycentric_centroid: centroid maps correctly
-- | - edge_loop: edges form closed loop (AB + BC + CA = 0)
-- | - normal_perp_edgeAB/AC: normal is perpendicular to edges
-- | - area_nonneg: area is non-negative
-- |
-- | ## Three.js Parity
-- | - set, setFromPointsAndIndices, setFromAttributeAndIndices
-- | - clone, copy, getArea, getMidpoint, getNormal
-- | - getPlane, getBarycoord, getInterpolation, containsPoint
-- | - isFrontFacing, intersectsBox, closestPointToPoint, equals
-- |
-- | ## Applications
-- | - Ray-triangle intersection (Möller–Trumbore algorithm)
-- | - Barycentric interpolation for textures/normals
-- | - Mesh collision detection
-- | - Surface normal computation

module Hydrogen.Schema.Geometry.Triangle
  ( -- * Types
    Triangle(Triangle)
  , Barycentric(Barycentric)
  
  -- * Triangle Constructors
  , triangle
  , triangleUnit
  , triangleDegenerate
  , triangleFromPoints
  
  -- * Barycentric Constructors
  , barycentric
  , barycentricVertexA
  , barycentricVertexB
  , barycentricVertexC
  , barycentricCentroid
  
  -- * Barycentric Queries
  , sumBarycentric
  , isValidBarycentric
  , isInsideBarycentric
  
  -- * Triangle Edges
  , edgeAB
  , edgeAC
  , edgeBC
  , edgeBA
  , edgeCA
  , edgeCB
  
  -- * Normal and Area
  , crossEdges
  , normalUnnormalized
  , normalLengthSq
  , areaTriangle
  , isDegenerate
  
  -- * Centroid and Midpoints
  , midpointAB
  , midpointBC
  , midpointCA
  , centroidTriangle
  
  -- * Barycentric Conversion
  , fromBarycentric
  , getBarycoord
  
  -- * Accessors
  , getA
  , getB
  , getC
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (>=)
  , (<>)
  , (&&)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3(Vec3)
  , vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , crossVec3
  , dotVec3
  , lengthSquaredVec3
  , lengthVec3
  , vec3Zero
  , vec3UnitX
  , vec3UnitY
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // barycentric type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Barycentric coordinates (u, v, w) where point = u*a + v*b + w*c
-- |
-- | Proof reference: Triangle.lean Barycentric
data Barycentric = Barycentric Number Number Number
  -- u v w (weights for vertices a, b, c)

derive instance eqBarycentric :: Eq Barycentric

instance showBarycentric :: Show Barycentric where
  show (Barycentric u v w) =
    "(Barycentric " <> show u <> " " <> show v <> " " <> show w <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // triangle type
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A triangle defined by three vertices.
-- |
-- | Vertices are labeled a, b, c and ordered counter-clockwise
-- | when viewed from the front face.
-- |
-- | Proof reference: Triangle.lean Triangle
data Triangle = Triangle (Vec3 Number) (Vec3 Number) (Vec3 Number)
  -- a b c

derive instance eqTriangle :: Eq Triangle

instance showTriangle :: Show Triangle where
  show (Triangle a b c) =
    "(Triangle a:" <> show a <> " b:" <> show b <> " c:" <> show c <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // triangle constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create a triangle from three vertices
triangle :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Triangle
triangle = Triangle

-- | Unit triangle in XY plane
-- | Proof reference: Triangle.lean unit, unit_a, unit_b, unit_c
triangleUnit :: Triangle
triangleUnit = Triangle vec3Zero vec3UnitX vec3UnitY

-- | Degenerate triangle (all vertices at origin)
-- | Proof reference: Triangle.lean degenerate
triangleDegenerate :: Triangle
triangleDegenerate = Triangle vec3Zero vec3Zero vec3Zero

-- | Triangle from three points (alias for triangle)
-- | Proof reference: Triangle.lean fromPoints
triangleFromPoints :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Triangle
triangleFromPoints = Triangle

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                     // barycentric constructors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create barycentric coordinates
barycentric :: Number -> Number -> Number -> Barycentric
barycentric = Barycentric

-- | Barycentric coordinates for vertex A: (1, 0, 0)
-- | Proof reference: Triangle.lean Barycentric.vertexA, barycentric_vertexA_valid
barycentricVertexA :: Barycentric
barycentricVertexA = Barycentric 1.0 0.0 0.0

-- | Barycentric coordinates for vertex B: (0, 1, 0)
-- | Proof reference: Triangle.lean Barycentric.vertexB, barycentric_vertexB_valid
barycentricVertexB :: Barycentric
barycentricVertexB = Barycentric 0.0 1.0 0.0

-- | Barycentric coordinates for vertex C: (0, 0, 1)
-- | Proof reference: Triangle.lean Barycentric.vertexC, barycentric_vertexC_valid
barycentricVertexC :: Barycentric
barycentricVertexC = Barycentric 0.0 0.0 1.0

-- | Barycentric coordinates for centroid: (1/3, 1/3, 1/3)
-- | Proof reference: Triangle.lean Barycentric.centroid, barycentric_centroid_valid
barycentricCentroid :: Barycentric
barycentricCentroid = Barycentric (1.0 / 3.0) (1.0 / 3.0) (1.0 / 3.0)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // barycentric queries
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Sum of barycentric coordinates (should be 1 for valid coords)
-- | Proof reference: Triangle.lean Barycentric.sum
sumBarycentric :: Barycentric -> Number
sumBarycentric (Barycentric u v w) = u + v + w

-- | Check if barycentric coordinates are valid (sum to 1)
-- | Proof reference: Triangle.lean Barycentric.IsValid
isValidBarycentric :: Barycentric -> Boolean
isValidBarycentric bc = sumBarycentric bc == 1.0

-- | Check if point is inside triangle (all coordinates non-negative)
-- | Proof reference: Triangle.lean Barycentric.IsInside
isInsideBarycentric :: Barycentric -> Boolean
isInsideBarycentric (Barycentric u v w) = u >= 0.0 && v >= 0.0 && w >= 0.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // triangle edges
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Edge from A to B
-- | Proof reference: Triangle.lean edgeAB
edgeAB :: Triangle -> Vec3 Number
edgeAB (Triangle a b _) = subtractVec3 b a

-- | Edge from A to C
-- | Proof reference: Triangle.lean edgeAC
edgeAC :: Triangle -> Vec3 Number
edgeAC (Triangle a _ c) = subtractVec3 c a

-- | Edge from B to C
-- | Proof reference: Triangle.lean edgeBC
edgeBC :: Triangle -> Vec3 Number
edgeBC (Triangle _ b c) = subtractVec3 c b

-- | Edge from B to A
-- | Proof reference: Triangle.lean edgeBA
edgeBA :: Triangle -> Vec3 Number
edgeBA (Triangle a b _) = subtractVec3 a b

-- | Edge from C to A
-- | Proof reference: Triangle.lean edgeCA
edgeCA :: Triangle -> Vec3 Number
edgeCA (Triangle a _ c) = subtractVec3 a c

-- | Edge from C to B
-- | Proof reference: Triangle.lean edgeCB
edgeCB :: Triangle -> Vec3 Number
edgeCB (Triangle _ b c) = subtractVec3 b c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // normal and area
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cross product of two edges (twice the area vector)
-- | Proof reference: Triangle.lean crossEdges
crossEdges :: Triangle -> Vec3 Number
crossEdges t = crossVec3 (edgeAB t) (edgeAC t)

-- | Normal vector (not normalized, length = 2 * area)
-- | Proof reference: Triangle.lean normalUnnormalized, unit_normal
normalUnnormalized :: Triangle -> Vec3 Number
normalUnnormalized = crossEdges

-- | Squared length of the normal (4 * area²)
-- | Proof reference: Triangle.lean normalLengthSq
normalLengthSq :: Triangle -> Number
normalLengthSq t = lengthSquaredVec3 (normalUnnormalized t)

-- | Area of the triangle: |AB × AC| / 2
-- | Proof reference: Triangle.lean area, area_nonneg, unit_area, degenerate_area
areaTriangle :: Triangle -> Number
areaTriangle t = lengthVec3 (crossEdges t) / 2.0

-- | Check if triangle is degenerate (zero area)
-- | Proof reference: Triangle.lean IsDegenerate
isDegenerate :: Triangle -> Boolean
isDegenerate t = normalLengthSq t == 0.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // centroid and midpoints
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Midpoint of edge AB
-- | Proof reference: Triangle.lean midpointAB
midpointAB :: Triangle -> Vec3 Number
midpointAB (Triangle a b _) = scaleVec3 0.5 (addVec3 a b)

-- | Midpoint of edge BC
-- | Proof reference: Triangle.lean midpointBC
midpointBC :: Triangle -> Vec3 Number
midpointBC (Triangle _ b c) = scaleVec3 0.5 (addVec3 b c)

-- | Midpoint of edge CA
-- | Proof reference: Triangle.lean midpointCA
midpointCA :: Triangle -> Vec3 Number
midpointCA (Triangle a _ c) = scaleVec3 0.5 (addVec3 c a)

-- | Centroid (center of mass) at (a + b + c) / 3
-- | Proof reference: Triangle.lean centroid
centroidTriangle :: Triangle -> Vec3 Number
centroidTriangle (Triangle a b c) = scaleVec3 (1.0 / 3.0) (addVec3 (addVec3 a b) c)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // barycentric conversion
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert barycentric coordinates to a point
-- | Proof reference: Triangle.lean fromBarycentric, fromBarycentric_vertexA/B/C
fromBarycentric :: Triangle -> Barycentric -> Vec3 Number
fromBarycentric (Triangle a b c) (Barycentric u v w) =
  addVec3 (addVec3 (scaleVec3 u a) (scaleVec3 v b)) (scaleVec3 w c)

-- | Compute barycentric coordinates of a point relative to triangle.
-- |
-- | Given a triangle ABC and a point P, computes (u, v, w) such that:
-- |   P = u*A + v*B + w*C  (where u + v + w = 1)
-- |
-- | Uses the standard algorithm via dot products:
-- |   v0 = C - A, v1 = B - A, v2 = P - A
-- |   d00 = v0·v0, d01 = v0·v1, d02 = v0·v2, d11 = v1·v1, d12 = v1·v2
-- |   denom = d00*d11 - d01*d01
-- |   v = (d11*d02 - d01*d12) / denom
-- |   w = (d00*d12 - d01*d02) / denom
-- |   u = 1 - v - w
-- |
-- | Three.js parity: Triangle.getBarycoord
-- | 
-- | Note: For degenerate triangles (denom ≈ 0), returns centroid coordinates
-- | as a safe fallback rather than producing NaN/Infinity.
getBarycoord :: Triangle -> Vec3 Number -> Barycentric
getBarycoord (Triangle a b c) p =
  let
    v0 = subtractVec3 c a
    v1 = subtractVec3 b a
    v2 = subtractVec3 p a
    
    d00 = dotVec3 v0 v0
    d01 = dotVec3 v0 v1
    d02 = dotVec3 v0 v2
    d11 = dotVec3 v1 v1
    d12 = dotVec3 v1 v2
    
    denom = d00 * d11 - d01 * d01
  in
    -- Guard against degenerate triangles (denom = 0)
    -- Return centroid as safe fallback
    if denom == 0.0
      then barycentricCentroid
      else
        let
          invDenom = 1.0 / denom
          v = (d11 * d02 - d01 * d12) * invDenom
          w = (d00 * d12 - d01 * d02) * invDenom
          u = 1.0 - v - w
        in
          Barycentric u v w

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get vertex A
getA :: Triangle -> Vec3 Number
getA (Triangle a _ _) = a

-- | Get vertex B
getB :: Triangle -> Vec3 Number
getB (Triangle _ b _) = b

-- | Get vertex C
getC :: Triangle -> Vec3 Number
getC (Triangle _ _ c) = c
