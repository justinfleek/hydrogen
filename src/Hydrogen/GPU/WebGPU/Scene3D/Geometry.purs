-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- Hydrogen.GPU.WebGPU.Scene3D.Geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Procedural mesh generation. Pure functions that produce vertex data.
--
-- MATHEMATICAL FOUNDATIONS:
-- Vertex/index count formulas are proven correct in:
--   proofs/Hydrogen/Geometry/Primitives.lean
--
-- INVARIANTS:
-- - All normals are unit length
-- - All indices form valid triangles (counterclockwise winding)
-- - UV coordinates are in [0, 1] range
-- - Vertex counts match Lean proofs exactly
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Geometry
  ( -- Mesh data type
    MeshData
  , emptyMeshData
    -- Main generator
  , generateMesh
    -- Basic generators
  , generatePlane
  , generateBox
  , generateSphere
  , generateCylinder
  , generateCone
  , generateCircle
  , generateRing
  , generateTorus
  , generateCapsule
    -- Platonic solids
  , generateIcosahedron
  , generateOctahedron
  , generateTetrahedron
  , generateDodecahedron
    -- Procedural
  , generateLathe
  , generateTorusKnot
    -- Utilities
  , combineMeshData
    -- Vertex/Index counts (matching Lean proofs)
  , planeVertexCount
  , planeIndexCount
  , boxVertexCount
  , boxIndexCount
  , sphereVertexCount
  , sphereIndexCount
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.GPU.Scene3D.Mesh
  ( BoxMeshParams
  , CapsuleMeshParams
  , CircleMeshParams
  , ConeMeshParams
  , CylinderMeshParams
  , DodecahedronMeshParams
  , IcosahedronMeshParams
  , LatheMeshParams
  , Mesh3D(..)
  , OctahedronMeshParams
  , PlaneMeshParams
  , Point2DProfile
  , RingMeshParams
  , SphereMeshParams
  , TetrahedronMeshParams
  , TorusKnotMeshParams
  , TorusMeshParams
  )
import Hydrogen.Math.Core (cos, sin, sqrt)
import Hydrogen.Schema.Dimension.Physical.SI (Meter, meter, unwrapMeter)
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2, vec2)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, addVec3, scaleVec3, getX3, getY3, getZ3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MESH DATA TYPE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generated mesh data. Pure vertex/index arrays ready for GPU upload.
-- |
-- | INVARIANTS (matching Lean proofs):
-- | - Array.length positions == vertex count from proof
-- | - Array.length indices == index count from proof
-- | - Array.length indices `mod` 3 == 0 (always triangles)
-- | - All normals have length ≈ 1.0
type MeshData =
  { positions :: Array (Vec3 Number)
  , normals :: Array (Vec3 Number)
  , uvs :: Array (Vec2 Number)
  , indices :: Array Int
  , tangents :: Maybe (Array (Vec4 Number))
  }

-- | Empty mesh data.
emptyMeshData :: MeshData
emptyMeshData =
  { positions: []
  , normals: []
  , uvs: []
  , indices: []
  , tangents: Nothing
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MAIN GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate mesh data from any Mesh3D type.
generateMesh :: Mesh3D -> MeshData
generateMesh = case _ of
  BoxMesh3D params -> generateBox params
  SphereMesh3D params -> generateSphere params
  CylinderMesh3D params -> generateCylinder params
  ConeMesh3D params -> generateCone params
  PlaneMesh3D params -> generatePlane params
  TorusMesh3D params -> generateTorus params
  RingMesh3D params -> generateRing params
  CircleMesh3D params -> generateCircle params
  CapsuleMesh3D params -> generateCapsule params
  -- Platonic solids
  IcosahedronMesh3D params -> generateIcosahedron params
  OctahedronMesh3D params -> generateOctahedron params
  TetrahedronMesh3D params -> generateTetrahedron params
  DodecahedronMesh3D params -> generateDodecahedron params
  -- Procedural
  TorusKnotMesh3D params -> generateTorusKnot params
  LatheMesh3D params -> generateLathe params
  -- Not yet implemented
  ExtrudeMesh3D _ -> emptyMeshData
  BufferGeometry3D _ -> emptyMeshData

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- VERTEX/INDEX COUNTS (matching Lean proofs)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Plane vertex count.
-- | From Primitives.lean: vertexCount = (widthSegments + 1) * (heightSegments + 1)
planeVertexCount :: Int -> Int -> Int
planeVertexCount widthSegs heightSegs = (widthSegs + 1) * (heightSegs + 1)

-- | Plane index count.
-- | From Primitives.lean: indexCount = widthSegments * heightSegments * 6
planeIndexCount :: Int -> Int -> Int
planeIndexCount widthSegs heightSegs = widthSegs * heightSegs * 6

-- | Box vertex count.
-- | From Primitives.lean: 24 for unit box (4 vertices per face × 6 faces)
boxVertexCount :: Int -> Int -> Int -> Int
boxVertexCount widthSegs heightSegs depthSegs =
  2 * (widthSegs + 1) * (heightSegs + 1) +
  2 * (depthSegs + 1) * (heightSegs + 1) +
  2 * (widthSegs + 1) * (depthSegs + 1)

-- | Box index count.
-- | From Primitives.lean: 36 for unit box
boxIndexCount :: Int -> Int -> Int -> Int
boxIndexCount widthSegs heightSegs depthSegs =
  2 * widthSegs * heightSegs * 6 +
  2 * depthSegs * heightSegs * 6 +
  2 * widthSegs * depthSegs * 6

-- | Sphere vertex count.
-- | From Primitives.lean: (widthSegments + 1) * (heightSegments + 1)
sphereVertexCount :: Int -> Int -> Int
sphereVertexCount widthSegs heightSegs = (widthSegs + 1) * (heightSegs + 1)

-- | Sphere index count.
-- | From Primitives.lean: widthSegments * heightSegments * 6
sphereIndexCount :: Int -> Int -> Int
sphereIndexCount widthSegs heightSegs = widthSegs * heightSegs * 6

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PLANE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a plane (XY plane, facing +Z).
generatePlane :: PlaneMeshParams -> MeshData
generatePlane params =
  let
    w = unwrapMeter params.width
    h = unwrapMeter params.height
    wSegs = params.widthSegments
    hSegs = params.heightSegments
    
    halfW = w / 2.0
    halfH = h / 2.0
    
    -- Generate grid of vertices
    vertices = do
      iy <- Array.range 0 hSegs
      ix <- Array.range 0 wSegs
      let
        u = toNumber ix / toNumber wSegs
        v = toNumber iy / toNumber hSegs
        x = u * w - halfW
        y = v * h - halfH
      pure { pos: vec3 x y 0.0, uv: vec2 u v }
    
    positions = map _.pos vertices
    uvs = map _.uv vertices
    normals = map (\_ -> vec3 0.0 0.0 1.0) positions
    indices = generateGridIndices wSegs hSegs (wSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BOX GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a box (axis-aligned, centered at origin).
generateBox :: BoxMeshParams -> MeshData
generateBox params =
  let
    w = unwrapMeter params.width
    h = unwrapMeter params.height
    d = unwrapMeter params.depth
    wSegs = params.widthSegments
    hSegs = params.heightSegments
    dSegs = params.depthSegments
    
    halfW = w / 2.0
    halfH = h / 2.0
    halfD = d / 2.0
    
    -- Generate each face, then combine
    frontFace = generateBoxFace 
      { width: w, height: h, depth: halfD
      , widthSegs: wSegs, heightSegs: hSegs
      , normal: vec3 0.0 0.0 1.0
      , u: vec3 1.0 0.0 0.0
      , v: vec3 0.0 1.0 0.0
      }
    
    backFace = generateBoxFace
      { width: w, height: h, depth: (-halfD)
      , widthSegs: wSegs, heightSegs: hSegs
      , normal: vec3 0.0 0.0 (-1.0)
      , u: vec3 (-1.0) 0.0 0.0
      , v: vec3 0.0 1.0 0.0
      }
    
    topFace = generateBoxFace
      { width: w, height: d, depth: halfH
      , widthSegs: wSegs, heightSegs: dSegs
      , normal: vec3 0.0 1.0 0.0
      , u: vec3 1.0 0.0 0.0
      , v: vec3 0.0 0.0 (-1.0)
      }
    
    bottomFace = generateBoxFace
      { width: w, height: d, depth: (-halfH)
      , widthSegs: wSegs, heightSegs: dSegs
      , normal: vec3 0.0 (-1.0) 0.0
      , u: vec3 1.0 0.0 0.0
      , v: vec3 0.0 0.0 1.0
      }
    
    rightFace = generateBoxFace
      { width: d, height: h, depth: halfW
      , widthSegs: dSegs, heightSegs: hSegs
      , normal: vec3 1.0 0.0 0.0
      , u: vec3 0.0 0.0 (-1.0)
      , v: vec3 0.0 1.0 0.0
      }
    
    leftFace = generateBoxFace
      { width: d, height: h, depth: (-halfW)
      , widthSegs: dSegs, heightSegs: hSegs
      , normal: vec3 (-1.0) 0.0 0.0
      , u: vec3 0.0 0.0 1.0
      , v: vec3 0.0 1.0 0.0
      }
  in
    combineMeshData [frontFace, backFace, topFace, bottomFace, rightFace, leftFace]

-- | Generate a single box face.
generateBoxFace 
  :: { width :: Number, height :: Number, depth :: Number
     , widthSegs :: Int, heightSegs :: Int
     , normal :: Vec3 Number
     , u :: Vec3 Number
     , v :: Vec3 Number
     }
  -> MeshData
generateBoxFace params =
  let
    halfW = params.width / 2.0
    halfH = params.height / 2.0
    
    vertices = do
      iy <- Array.range 0 params.heightSegs
      ix <- Array.range 0 params.widthSegs
      let
        uvx = toNumber ix / toNumber params.widthSegs
        uvy = toNumber iy / toNumber params.heightSegs
        localX = uvx * params.width - halfW
        localY = uvy * params.height - halfH
        pos = addVec3 (addVec3 (scaleVec3 localX params.u) (scaleVec3 localY params.v))
                      (scaleVec3 params.depth params.normal)
      pure { pos, uv: vec2 uvx uvy }
    
    positions = map _.pos vertices
    uvs = map _.uv vertices
    normals = map (\_ -> params.normal) positions
    indices = generateGridIndices params.widthSegs params.heightSegs (params.widthSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SPHERE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a UV sphere with optional phi/theta limits.
-- |
-- | Phi (horizontal): 0-360° for full sphere, partial for wedges
-- | Theta (vertical): 0-180° for full sphere, partial for bands/caps
generateSphere :: SphereMeshParams -> MeshData
generateSphere params =
  let
    radius = unwrapMeter params.radius
    wSegs = params.widthSegments
    hSegs = params.heightSegments
    
    -- Convert angle params to radians
    phiStart = unwrapDegrees params.phiStart * degToRad
    phiLength = unwrapDegrees params.phiLength * degToRad
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    -- Generate vertices using spherical coordinates
    vertices = do
      iy <- Array.range 0 hSegs
      ix <- Array.range 0 wSegs
      let
        u = toNumber ix / toNumber wSegs
        v = toNumber iy / toNumber hSegs
        
        -- Spherical angles with phi/theta limits
        phi = phiStart + u * phiLength
        theta = thetaStart + v * thetaLength
        
        sinTheta = sin theta
        cosTheta = cos theta
        sinPhi = sin phi
        cosPhi = cos phi
        
        x = radius * sinTheta * cosPhi
        y = radius * cosTheta
        z = radius * sinTheta * sinPhi
        
        -- Normal = position / radius (unit sphere direction)
        nx = sinTheta * cosPhi
        ny = cosTheta
        nz = sinTheta * sinPhi
      
      pure { pos: vec3 x y z, normal: vec3 nx ny nz, uv: vec2 u (1.0 - v) }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices wSegs hSegs (wSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CYLINDER GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a cylinder (along Y axis) with optional arc.
-- |
-- | Theta controls the arc: 360° for full cylinder, less for partial arcs.
generateCylinder :: CylinderMeshParams -> MeshData
generateCylinder params =
  let
    radiusTop = unwrapMeter params.radiusTop
    radiusBottom = unwrapMeter params.radiusBottom
    height = unwrapMeter params.height
    radSegs = params.radialSegments
    hSegs = params.heightSegments
    
    -- Convert angle params to radians
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    halfH = height / 2.0
    
    -- Generate body vertices
    bodyVerts = do
      iy <- Array.range 0 hSegs
      ix <- Array.range 0 radSegs
      let
        u = toNumber ix / toNumber radSegs
        v = toNumber iy / toNumber hSegs
        r = radiusBottom + (radiusTop - radiusBottom) * v
        theta = thetaStart + u * thetaLength
        x = r * cos theta
        z = r * sin theta
        y = v * height - halfH
        
        slope = (radiusBottom - radiusTop) / height
        nx = cos theta
        ny = slope
        nz = sin theta
        len = sqrt (nx * nx + ny * ny + nz * nz)
      
      pure { pos: vec3 x y z
           , normal: vec3 (nx / len) (ny / len) (nz / len)
           , uv: vec2 u v
           }
    
    bodyPositions = map _.pos bodyVerts
    bodyNormals = map _.normal bodyVerts
    bodyUvs = map _.uv bodyVerts
    bodyIndices = generateGridIndices radSegs hSegs (radSegs + 1)
    
    bodyMesh = { positions: bodyPositions, normals: bodyNormals, uvs: bodyUvs
               , indices: bodyIndices, tangents: Nothing }
    
    -- Only generate caps for full cylinders (thetaLength ≈ 360°)
    isFullCylinder = thetaLength >= 2.0 * pi - 0.001
    
    topCap = if params.openEnded || not isFullCylinder then emptyMeshData
             else generateCircleCap radiusTop halfH radSegs true
    
    bottomCap = if params.openEnded || not isFullCylinder then emptyMeshData
                else generateCircleCap radiusBottom (-halfH) radSegs false
  in
    combineMeshData [bodyMesh, topCap, bottomCap]

-- | Generate a circle cap for cylinder/cone.
generateCircleCap :: Number -> Number -> Int -> Boolean -> MeshData
generateCircleCap radius y segments isTop =
  let
    centerPos = vec3 0.0 y 0.0
    centerNormal = if isTop then vec3 0.0 1.0 0.0 else vec3 0.0 (-1.0) 0.0
    centerUv = vec2 0.5 0.5
    
    edgeVerts = do
      i <- Array.range 0 segments
      let
        theta = (toNumber i / toNumber segments) * 2.0 * pi
        x = radius * cos theta
        z = radius * sin theta
        uvU = 0.5 + 0.5 * cos theta
        uvV = 0.5 + 0.5 * sin theta
      pure { pos: vec3 x y z, normal: centerNormal, uv: vec2 uvU uvV }
    
    positions = [centerPos] <> map _.pos edgeVerts
    normals = [centerNormal] <> map _.normal edgeVerts
    uvs = [centerUv] <> map _.uv edgeVerts
    
    indices = do
      i <- Array.range 0 (segments - 1)
      let
        a = 0
        b = i + 1
        c = i + 2
      if isTop then [a, b, c] else [a, c, b]
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CONE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a cone.
-- |
-- | A cone is a cylinder with radiusTop = 0. The apex is at the top,
-- | the base circle is at the bottom.
generateCone :: ConeMeshParams -> MeshData
generateCone params =
  generateCylinder
    { radiusTop: meter 0.0           -- Apex at top
    , radiusBottom: params.radius    -- Base circle at bottom
    , height: params.height
    , radialSegments: params.radialSegments
    , heightSegments: params.heightSegments
    , openEnded: params.openEnded
    , thetaStart: params.thetaStart
    , thetaLength: params.thetaLength
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CIRCLE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a circle (flat disk on XZ plane).
generateCircle :: CircleMeshParams -> MeshData
generateCircle params =
  let
    radius = unwrapMeter params.radius
    segments = params.segments
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    centerPos = vec3 0.0 0.0 0.0
    centerNormal = vec3 0.0 1.0 0.0
    centerUv = vec2 0.5 0.5
    
    edgeVerts = do
      i <- Array.range 0 segments
      let
        theta = thetaStart + (toNumber i / toNumber segments) * thetaLength
        x = radius * cos theta
        z = radius * sin theta
        uvU = 0.5 + 0.5 * cos theta
        uvV = 0.5 + 0.5 * sin theta
      pure { pos: vec3 x 0.0 z, uv: vec2 uvU uvV }
    
    positions = [centerPos] <> map _.pos edgeVerts
    normals = map (\_ -> centerNormal) positions
    uvs = [centerUv] <> map _.uv edgeVerts
    
    indices = do
      i <- Array.range 0 (segments - 1)
      [0, i + 1, i + 2]
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RING GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a ring (annulus on XZ plane).
generateRing :: RingMeshParams -> MeshData
generateRing params =
  let
    innerR = unwrapMeter params.innerRadius
    outerR = unwrapMeter params.outerRadius
    thetaSegs = params.thetaSegments
    phiSegs = params.phiSegments
    thetaStart = unwrapDegrees params.thetaStart * degToRad
    thetaLength = unwrapDegrees params.thetaLength * degToRad
    
    vertices = do
      ip <- Array.range 0 phiSegs
      it <- Array.range 0 thetaSegs
      let
        u = toNumber it / toNumber thetaSegs
        v = toNumber ip / toNumber phiSegs
        theta = thetaStart + u * thetaLength
        r = innerR + v * (outerR - innerR)
        x = r * cos theta
        z = r * sin theta
      pure { pos: vec3 x 0.0 z, uv: vec2 u v }
    
    positions = map _.pos vertices
    normals = map (\_ -> vec3 0.0 1.0 0.0) positions
    uvs = map _.uv vertices
    indices = generateGridIndices thetaSegs phiSegs (thetaSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- TORUS GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a torus.
generateTorus :: TorusMeshParams -> MeshData
generateTorus params =
  let
    radius = unwrapMeter params.radius
    tube = unwrapMeter params.tube
    radSegs = params.radialSegments
    tubSegs = params.tubularSegments
    arc = unwrapDegrees params.arc * degToRad
    
    vertices = do
      j <- Array.range 0 radSegs
      i <- Array.range 0 tubSegs
      let
        u = toNumber i / toNumber tubSegs * arc
        v = toNumber j / toNumber radSegs * 2.0 * pi
        
        x = (radius + tube * cos v) * cos u
        y = tube * sin v
        z = (radius + tube * cos v) * sin u
        
        cx = radius * cos u
        cz = radius * sin u
        
        nx = x - cx
        ny = y
        nz = z - cz
        len = sqrt (nx * nx + ny * ny + nz * nz)
      
      pure { pos: vec3 x y z
           , normal: vec3 (nx / len) (ny / len) (nz / len)
           , uv: vec2 (toNumber i / toNumber tubSegs) (toNumber j / toNumber radSegs)
           }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices tubSegs radSegs (tubSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CAPSULE GENERATOR
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a capsule (cylinder with hemispherical caps).
generateCapsule :: CapsuleMeshParams -> MeshData
generateCapsule params =
  let
    radius = unwrapMeter params.radius
    len = unwrapMeter params.length
    capSegs = params.capSegments
    radSegs = params.radialSegments
    
    halfLen = len / 2.0
    
    topHemi = generateHemisphere radius halfLen capSegs radSegs true
    bottomHemi = generateHemisphere radius (-halfLen) capSegs radSegs false
    
    body = generateCylinder
      { radiusTop: params.radius
      , radiusBottom: params.radius
      , height: params.length
      , radialSegments: radSegs
      , heightSegments: 1
      , openEnded: true
      , thetaStart: degrees 0.0
      , thetaLength: degrees 360.0
      }
  in
    combineMeshData [topHemi, body, bottomHemi]

-- | Generate a hemisphere for capsule caps.
generateHemisphere :: Number -> Number -> Int -> Int -> Boolean -> MeshData
generateHemisphere radius yOffset capSegs radSegs isTop =
  let
    vertices = do
      iy <- Array.range 0 capSegs
      ix <- Array.range 0 radSegs
      let
        u = toNumber ix / toNumber radSegs
        v = toNumber iy / toNumber capSegs
        
        theta = if isTop then v * (pi / 2.0) else (pi / 2.0) + v * (pi / 2.0)
        phi = u * 2.0 * pi
        
        sinTheta = sin theta
        cosTheta = cos theta
        sinPhi = sin phi
        cosPhi = cos phi
        
        x = radius * sinTheta * cosPhi
        y = radius * cosTheta + yOffset
        z = radius * sinTheta * sinPhi
        
        nx = sinTheta * cosPhi
        ny = cosTheta
        nz = sinTheta * sinPhi
      
      pure { pos: vec3 x y z, normal: vec3 nx ny nz, uv: vec2 u v }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices radSegs capSegs (radSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PLATONIC SOLIDS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate an icosahedron (20-faced regular polyhedron).
-- |
-- | The icosahedron is defined by 12 vertices and 20 triangular faces.
-- | Detail level controls subdivision: 0 = 20 triangles, n = 20 × 4^n triangles.
-- |
-- | Golden ratio: φ = (1 + √5) / 2 ≈ 1.618
-- | Vertices lie at (0, ±1, ±φ) and cyclic permutations.
generateIcosahedron :: IcosahedronMeshParams -> MeshData
generateIcosahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- Golden ratio
    phi = (1.0 + sqrt 5.0) / 2.0
    
    -- Normalize to unit sphere, then scale
    len = sqrt (1.0 + phi * phi)
    a = 1.0 / len
    b = phi / len
    
    -- 12 vertices of icosahedron (normalized, then scaled)
    basePositions =
      [ vec3 (-a) b 0.0, vec3 a b 0.0, vec3 (-a) (-b) 0.0, vec3 a (-b) 0.0
      , vec3 0.0 (-a) b, vec3 0.0 a b, vec3 0.0 (-a) (-b), vec3 0.0 a (-b)
      , vec3 b 0.0 (-a), vec3 b 0.0 a, vec3 (-b) 0.0 (-a), vec3 (-b) 0.0 a
      ]
    
    -- 20 triangular faces (CCW winding, outward normals)
    baseFaces =
      [ [0, 11, 5], [0, 5, 1], [0, 1, 7], [0, 7, 10], [0, 10, 11]
      , [1, 5, 9], [5, 11, 4], [11, 10, 2], [10, 7, 6], [7, 1, 8]
      , [3, 9, 4], [3, 4, 2], [3, 2, 6], [3, 6, 8], [3, 8, 9]
      , [4, 9, 5], [2, 4, 11], [6, 2, 10], [8, 6, 7], [9, 8, 1]
      ]
    
    -- Subdivide if detail > 0
    subdivided = subdividePolyhedron basePositions baseFaces detail
    
    -- Scale to radius and compute normals
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    
    -- For a sphere-like polyhedron, normal = normalized position
    computedNormals = map normalizeVec3 subdivided.positions
    
    -- Simple UV mapping: spherical projection
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- | Generate an octahedron (8-faced regular polyhedron).
-- |
-- | The octahedron has 6 vertices at (±1, 0, 0), (0, ±1, 0), (0, 0, ±1)
-- | and 8 triangular faces.
generateOctahedron :: OctahedronMeshParams -> MeshData
generateOctahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- 6 vertices of octahedron (unit)
    basePositions =
      [ vec3 1.0 0.0 0.0, vec3 (-1.0) 0.0 0.0
      , vec3 0.0 1.0 0.0, vec3 0.0 (-1.0) 0.0
      , vec3 0.0 0.0 1.0, vec3 0.0 0.0 (-1.0)
      ]
    
    -- 8 triangular faces (CCW winding)
    baseFaces =
      [ [0, 2, 4], [0, 4, 3], [0, 3, 5], [0, 5, 2]
      , [1, 2, 5], [1, 5, 3], [1, 3, 4], [1, 4, 2]
      ]
    
    subdivided = subdividePolyhedron basePositions baseFaces detail
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    computedNormals = map normalizeVec3 subdivided.positions
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- | Generate a tetrahedron (4-faced regular polyhedron).
-- |
-- | The simplest Platonic solid with 4 vertices and 4 triangular faces.
generateTetrahedron :: TetrahedronMeshParams -> MeshData
generateTetrahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- 4 vertices of tetrahedron (inscribed in unit sphere)
    -- Using coordinates that place centroid at origin
    a = 1.0 / sqrt 3.0
    b = sqrt (2.0 / 3.0)
    c = sqrt (2.0 / 9.0)
    d = sqrt (8.0 / 9.0)
    
    basePositions =
      [ vec3 0.0 1.0 0.0
      , vec3 d (-a) 0.0
      , vec3 (-c) (-a) b
      , vec3 (-c) (-a) (-b)
      ]
    
    -- 4 triangular faces (CCW winding)
    baseFaces =
      [ [0, 1, 2], [0, 2, 3], [0, 3, 1], [1, 3, 2]
      ]
    
    subdivided = subdividePolyhedron basePositions baseFaces detail
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    computedNormals = map normalizeVec3 subdivided.positions
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- | Generate a dodecahedron (12-faced regular polyhedron).
-- |
-- | The dodecahedron has 20 vertices and 12 pentagonal faces.
-- | We triangulate each pentagon into 5 triangles (60 total).
generateDodecahedron :: DodecahedronMeshParams -> MeshData
generateDodecahedron params =
  let
    radius = unwrapMeter params.radius
    detail = params.detail
    
    -- Golden ratio
    phi = (1.0 + sqrt 5.0) / 2.0
    invPhi = 1.0 / phi
    
    -- 20 vertices of dodecahedron (normalized)
    -- Cube vertices: (±1, ±1, ±1)
    -- Rectangle vertices: (0, ±φ, ±1/φ), (±1/φ, 0, ±φ), (±φ, ±1/φ, 0)
    basePositions =
      [ -- Cube vertices (8)
        vec3 1.0 1.0 1.0, vec3 1.0 1.0 (-1.0), vec3 1.0 (-1.0) 1.0, vec3 1.0 (-1.0) (-1.0)
      , vec3 (-1.0) 1.0 1.0, vec3 (-1.0) 1.0 (-1.0), vec3 (-1.0) (-1.0) 1.0, vec3 (-1.0) (-1.0) (-1.0)
        -- Rectangle vertices (12)
      , vec3 0.0 phi invPhi, vec3 0.0 phi (-invPhi), vec3 0.0 (-phi) invPhi, vec3 0.0 (-phi) (-invPhi)
      , vec3 invPhi 0.0 phi, vec3 (-invPhi) 0.0 phi, vec3 invPhi 0.0 (-phi), vec3 (-invPhi) 0.0 (-phi)
      , vec3 phi invPhi 0.0, vec3 phi (-invPhi) 0.0, vec3 (-phi) invPhi 0.0, vec3 (-phi) (-invPhi) 0.0
      ]
    
    -- Normalize all positions to unit sphere
    normalizedPositions = map normalizeVec3 basePositions
    
    -- 12 pentagonal faces, each triangulated into 5 triangles (fan from center)
    -- We create a center vertex for each pentagon
    baseFaces =
      [ [0, 16, 1, 9, 8], [0, 8, 4, 13, 12], [0, 12, 2, 17, 16]
      , [1, 16, 17, 3, 14], [1, 14, 15, 5, 9], [2, 12, 13, 6, 10]
      , [2, 10, 11, 3, 17], [3, 11, 7, 15, 14], [4, 8, 9, 5, 18]
      , [4, 18, 19, 6, 13], [5, 15, 7, 19, 18], [6, 19, 7, 11, 10]
      ]
    
    -- Triangulate pentagons and apply subdivision
    triangulated = triangulatePentagons normalizedPositions baseFaces
    subdivided = subdividePolyhedron triangulated.positions triangulated.faces detail
    scaledPositions = map (scaleVec3 radius) subdivided.positions
    computedNormals = map normalizeVec3 subdivided.positions
    computedUvs = map sphericalUV subdivided.positions
  in
    { positions: scaledPositions
    , normals: computedNormals
    , uvs: computedUvs
    , indices: subdivided.indices
    , tangents: Nothing
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PROCEDURAL GENERATORS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate a torus knot.
-- |
-- | A torus knot winds around a torus p times through the hole
-- | and q times around the tube. The (2,3) knot is the trefoil.
generateTorusKnot :: TorusKnotMeshParams -> MeshData
generateTorusKnot params =
  let
    radius = unwrapMeter params.radius
    tube = unwrapMeter params.tube
    tubSegs = params.tubularSegments
    radSegs = params.radialSegments
    p = toNumber params.p
    q = toNumber params.q
    
    -- Parametric torus knot curve
    -- P(t) = ((2 + cos(q*t)) * cos(p*t), (2 + cos(q*t)) * sin(p*t), sin(q*t))
    -- We trace this curve and build a tube around it
    
    vertices = do
      i <- Array.range 0 tubSegs
      j <- Array.range 0 radSegs
      let
        u = toNumber i / toNumber tubSegs * 2.0 * pi
        v = toNumber j / toNumber radSegs * 2.0 * pi
        
        -- Point on torus knot curve
        cu = cos (p * u)
        su = sin (p * u)
        cqu = cos (q * u)
        squ = sin (q * u)
        
        -- Scale factor for knot size
        r = radius * (2.0 + cqu) / 3.0
        
        -- Center of tube at this point
        cx = r * cu
        cy = r * su
        cz = radius * squ / 3.0
        
        -- Tangent vector (derivative)
        dx = (-p * r * su) + ((-q * radius * squ / 3.0) * cu)
        dy = (p * r * cu) + ((-q * radius * squ / 3.0) * su)
        dz = q * radius * cqu / 3.0
        
        -- Normalize tangent
        tlen = sqrt (dx * dx + dy * dy + dz * dz)
        tx = dx / tlen
        ty = dy / tlen
        tz = dz / tlen
        
        -- Build orthonormal frame using cross products
        -- Binormal: cross(tangent, (0, 1, 0)) if tangent not parallel to Y
        bx = ty
        by = (-tx)
        bz = 0.0
        blen = sqrt (bx * bx + by * by + bz * bz)
        bnx = if blen > 0.001 then bx / blen else 1.0
        bny = if blen > 0.001 then by / blen else 0.0
        bnz = if blen > 0.001 then bz / blen else 0.0
        
        -- Normal: cross(binormal, tangent)
        nx = bny * tz - bnz * ty
        ny = bnz * tx - bnx * tz
        nz = bnx * ty - bny * tx
        
        -- Point on tube surface
        cv = cos v
        sv = sin v
        x = cx + tube * (cv * nx + sv * bnx)
        y = cy + tube * (cv * ny + sv * bny)
        z = cz + tube * (cv * nz + sv * bnz)
        
        -- Surface normal at this point
        snx = cv * nx + sv * bnx
        sny = cv * ny + sv * bny
        snz = cv * nz + sv * bnz
        
        uvU = toNumber i / toNumber tubSegs
        uvV = toNumber j / toNumber radSegs
      
      pure { pos: vec3 x y z, normal: vec3 snx sny snz, uv: vec2 uvU uvV }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices tubSegs radSegs (radSegs + 1)
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- | Generate a lathe (surface of revolution).
-- |
-- | Takes a 2D profile in XY plane and rotates it around the Y axis.
generateLathe :: LatheMeshParams -> MeshData
generateLathe params =
  let
    points = params.points
    segments = params.segments
    phiStart = unwrapDegrees params.phiStart * degToRad
    phiLength = unwrapDegrees params.phiLength * degToRad
    
    numPoints = Array.length points
    
    vertices = do
      i <- Array.range 0 segments
      j <- Array.range 0 (numPoints - 1)
      let
        phi = phiStart + (toNumber i / toNumber segments) * phiLength
        
        -- Get profile point
        point = case Array.index points j of
          Nothing -> { x: meter 0.0, y: meter 0.0 }
          Just p -> p
        
        r = unwrapMeter point.x
        y = unwrapMeter point.y
        
        x = r * cos phi
        z = r * sin phi
        
        -- Normal: perpendicular to profile, rotated
        -- Approximate using finite differences
        nextIdx = min (j + 1) (numPoints - 1)
        prevIdx = max (j - 1) 0
        
        nextPoint = case Array.index points nextIdx of
          Nothing -> point
          Just p -> p
        prevPoint = case Array.index points prevIdx of
          Nothing -> point
          Just p -> p
        
        dx = unwrapMeter nextPoint.x - unwrapMeter prevPoint.x
        dy = unwrapMeter nextPoint.y - unwrapMeter prevPoint.y
        
        -- Profile tangent is (dx, dy), normal is (-dy, dx) in profile plane
        pnx = (-dy)
        pny = dx
        pnLen = sqrt (pnx * pnx + pny * pny)
        normalizedPnx = if pnLen > 0.001 then pnx / pnLen else 1.0
        normalizedPny = if pnLen > 0.001 then pny / pnLen else 0.0
        
        -- Rotate normal around Y axis
        nx = normalizedPnx * cos phi
        ny = normalizedPny
        nz = normalizedPnx * sin phi
        
        uvU = toNumber i / toNumber segments
        uvV = toNumber j / toNumber (numPoints - 1)
      
      pure { pos: vec3 x y z, normal: vec3 nx ny nz, uv: vec2 uvU uvV }
    
    positions = map _.pos vertices
    normals = map _.normal vertices
    uvs = map _.uv vertices
    indices = generateGridIndices segments (numPoints - 1) numPoints
  in
    { positions, normals, uvs, indices, tangents: Nothing }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- POLYHEDRON HELPERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Subdivide a polyhedron by splitting each triangle into 4.
-- |
-- | Each subdivision level multiplies triangle count by 4.
-- | Vertices are projected back to unit sphere.
subdividePolyhedron 
  :: Array (Vec3 Number) 
  -> Array (Array Int) 
  -> Int 
  -> { positions :: Array (Vec3 Number), indices :: Array Int }
subdividePolyhedron positions faces detail =
  if detail <= 0 then
    { positions
    , indices: Array.concatMap identity faces
    }
  else
    let
      subdivided = subdivideFaces positions faces
    in
      subdividePolyhedron subdivided.positions subdivided.faces (detail - 1)

-- | Single level of face subdivision.
subdivideFaces 
  :: Array (Vec3 Number) 
  -> Array (Array Int) 
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
subdivideFaces positions faces =
  -- For each triangle, create 4 new triangles
  -- by adding midpoint vertices on each edge
  foldl subdivideSingleFace { positions, faces: [] } faces

-- | Subdivide a single triangular face.
subdivideSingleFace
  :: { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
  -> Array Int
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
subdivideSingleFace acc face =
  case face of
    [i0, i1, i2] ->
      let
        p0 = getVec3At acc.positions i0
        p1 = getVec3At acc.positions i1
        p2 = getVec3At acc.positions i2
        
        -- Midpoints (normalized to unit sphere)
        m01 = normalizeVec3 (midpoint p0 p1)
        m12 = normalizeVec3 (midpoint p1 p2)
        m20 = normalizeVec3 (midpoint p2 p0)
        
        -- Add new vertices
        baseIdx = Array.length acc.positions
        newPositions = acc.positions <> [m01, m12, m20]
        i01 = baseIdx
        i12 = baseIdx + 1
        i20 = baseIdx + 2
        
        -- 4 new triangles
        newFaces = acc.faces <> 
          [ [i0, i01, i20]
          , [i01, i1, i12]
          , [i20, i12, i2]
          , [i01, i12, i20]
          ]
      in
        { positions: newPositions, faces: newFaces }
    _ -> acc  -- Not a triangle, skip

-- | Triangulate pentagonal faces into triangles using fan method.
triangulatePentagons
  :: Array (Vec3 Number)
  -> Array (Array Int)
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
triangulatePentagons positions pentagons =
  foldl triangulateSinglePentagon { positions, faces: [] } pentagons

-- | Triangulate a single pentagon by adding center vertex.
triangulateSinglePentagon
  :: { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
  -> Array Int
  -> { positions :: Array (Vec3 Number), faces :: Array (Array Int) }
triangulateSinglePentagon acc pentagon =
  case pentagon of
    [i0, i1, i2, i3, i4] ->
      let
        p0 = getVec3At acc.positions i0
        p1 = getVec3At acc.positions i1
        p2 = getVec3At acc.positions i2
        p3 = getVec3At acc.positions i3
        p4 = getVec3At acc.positions i4
        
        -- Center of pentagon (average of vertices, then normalized)
        cx = (getX3 p0 + getX3 p1 + getX3 p2 + getX3 p3 + getX3 p4) / 5.0
        cy = (getY3 p0 + getY3 p1 + getY3 p2 + getY3 p3 + getY3 p4) / 5.0
        cz = (getZ3 p0 + getZ3 p1 + getZ3 p2 + getZ3 p3 + getZ3 p4) / 5.0
        center = normalizeVec3 (vec3 cx cy cz)
        
        centerIdx = Array.length acc.positions
        newPositions = acc.positions <> [center]
        
        -- 5 triangles from center to each edge
        newFaces = acc.faces <>
          [ [centerIdx, i0, i1]
          , [centerIdx, i1, i2]
          , [centerIdx, i2, i3]
          , [centerIdx, i3, i4]
          , [centerIdx, i4, i0]
          ]
      in
        { positions: newPositions, faces: newFaces }
    _ -> acc  -- Not a pentagon, skip

-- | Get Vec3 at index, or zero vector.
getVec3At :: Array (Vec3 Number) -> Int -> Vec3 Number
getVec3At arr i = case Array.index arr i of
  Just v -> v
  Nothing -> vec3 0.0 0.0 0.0

-- | Compute midpoint of two vectors.
midpoint :: Vec3 Number -> Vec3 Number -> Vec3 Number
midpoint a b = vec3 
  ((getX3 a + getX3 b) / 2.0)
  ((getY3 a + getY3 b) / 2.0)
  ((getZ3 a + getZ3 b) / 2.0)

-- | Normalize a Vec3 to unit length.
normalizeVec3 :: Vec3 Number -> Vec3 Number
normalizeVec3 v =
  let
    x = getX3 v
    y = getY3 v
    z = getZ3 v
    len = sqrt (x * x + y * y + z * z)
  in
    if len > 0.0001 then vec3 (x / len) (y / len) (z / len)
    else vec3 0.0 1.0 0.0  -- Default up vector

-- | Spherical UV mapping from normalized position.
sphericalUV :: Vec3 Number -> Vec2 Number
sphericalUV v =
  let
    x = getX3 v
    y = getY3 v
    z = getZ3 v
    
    -- U: atan2(z, x) mapped to [0, 1]
    -- V: asin(y) mapped to [0, 1]
    u = 0.5 + atan2 z x / (2.0 * pi)
    vVal = 0.5 + asin (clamp (-1.0) 1.0 y) / pi
  in
    vec2 u vVal

-- | Clamp a value to a range.
clamp :: Number -> Number -> Number -> Number
clamp lo hi x = if x < lo then lo else if x > hi then hi else x

-- | Arc tangent of y/x, handling quadrants.
atan2 :: Number -> Number -> Number
atan2 y x =
  let
    rawAtan = if x > 0.0 then atan (y / x)
              else if x < 0.0 && y >= 0.0 then atan (y / x) + pi
              else if x < 0.0 && y < 0.0 then atan (y / x) - pi
              else if x == 0.0 && y > 0.0 then pi / 2.0
              else if x == 0.0 && y < 0.0 then (-pi) / 2.0
              else 0.0  -- x == 0 && y == 0
  in
    rawAtan

-- | Arc sine function (Taylor series approximation).
asin :: Number -> Number
asin x =
  -- Polynomial approximation for asin in [-1, 1]
  -- asin(x) ≈ x + x³/6 + 3x⁵/40 + 15x⁷/336 for |x| < 1
  let
    x2 = x * x
    x3 = x2 * x
    x5 = x3 * x2
    x7 = x5 * x2
  in
    x + x3 / 6.0 + 3.0 * x5 / 40.0 + 15.0 * x7 / 336.0

-- | Arc tangent function (approximation).
atan :: Number -> Number
atan x =
  -- For |x| <= 1: atan(x) ≈ x - x³/3 + x⁵/5 - x⁷/7
  -- For |x| > 1: atan(x) = π/2 - atan(1/x) if x > 0
  if x > 1.0 then pi / 2.0 - atanSmall (1.0 / x)
  else if x < (-1.0) then (-pi) / 2.0 - atanSmall (1.0 / x)
  else atanSmall x
  where
    atanSmall :: Number -> Number
    atanSmall t =
      let
        t2 = t * t
        t3 = t2 * t
        t5 = t3 * t2
        t7 = t5 * t2
      in
        t - t3 / 3.0 + t5 / 5.0 - t7 / 7.0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate grid indices for a subdivided quad.
generateGridIndices :: Int -> Int -> Int -> Array Int
generateGridIndices widthSegs heightSegs stride = do
  iy <- Array.range 0 (heightSegs - 1)
  ix <- Array.range 0 (widthSegs - 1)
  let
    a = iy * stride + ix
    b = iy * stride + ix + 1
    c = (iy + 1) * stride + ix + 1
    d = (iy + 1) * stride + ix
  [a, b, d, b, c, d]

-- | Combine multiple mesh data into one.
combineMeshData :: Array MeshData -> MeshData
combineMeshData = foldl combineTwoMeshes emptyMeshData

-- | Combine two mesh data, offsetting indices of the second.
combineTwoMeshes :: MeshData -> MeshData -> MeshData
combineTwoMeshes a b =
  let
    offset = Array.length a.positions
    offsetIndices = map (_ + offset) b.indices
  in
    { positions: a.positions <> b.positions
    , normals: a.normals <> b.normals
    , uvs: a.uvs <> b.uvs
    , indices: a.indices <> offsetIndices
    , tangents: Nothing
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- CONSTANTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pi :: Number
pi = 3.141592653589793

degToRad :: Number
degToRad = pi / 180.0
