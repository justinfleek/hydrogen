-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // spatial // geometry // primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Parametric 3D Primitives — Procedural geometry generators.
-- |
-- | ## Primitives
-- |
-- | - **Cube**: Axis-aligned box with configurable dimensions
-- | - **Sphere**: UV sphere with configurable segments
-- | - **Cylinder**: Capped cylinder with height and radius
-- | - **Cone**: Capped cone with height and base radius
-- | - **Torus**: Donut with major and minor radii
-- | - **Plane**: Flat rectangular mesh with subdivisions
-- | - **Capsule**: Cylinder with hemispherical caps
-- |
-- | ## Design Philosophy
-- |
-- | All primitives generate MeshData with:
-- | - Positions (required)
-- | - Normals (for lighting)
-- | - UVs (for texturing)
-- | - Indices (for indexed rendering)
-- |
-- | Segment counts are bounded to prevent memory exhaustion:
-- | - Minimum: 3 (valid triangle topology)
-- | - Maximum: 256 (GPU vertex limit safety)
-- |
-- | ## C4D/Blender Equivalent
-- |
-- | These primitives match the parametric objects in Cinema 4D and Blender:
-- | - Cube → C4D Cube / Blender Cube
-- | - Sphere → C4D Sphere (Standard) / Blender UV Sphere
-- | - Cylinder → C4D Cylinder / Blender Cylinder
-- | - Cone → C4D Cone / Blender Cone
-- | - Torus → C4D Torus / Blender Torus

module Hydrogen.Schema.Spatial.Geometry.Primitives
  ( -- * Segment Count
    Segments
  , segments
  , unwrapSegments
  , defaultSegments
  
  -- * Primitive Configs
  , CubeConfig
  , defaultCubeConfig
  , SphereConfig
  , defaultSphereConfig
  , CylinderConfig
  , defaultCylinderConfig
  , ConeConfig
  , defaultConeConfig
  , TorusConfig
  , defaultTorusConfig
  , PlaneConfig
  , defaultPlaneConfig
  , CapsuleConfig
  , defaultCapsuleConfig
  
  -- * Generators
  , cube
  , sphere
  , cylinder
  , cone
  , torus
  , plane
  , capsule
  
  -- * Primitive Type
  , Primitive(PrimCube, PrimSphere, PrimCylinder, PrimCone, PrimTorus, PrimPlane, PrimCapsule)
  , primitiveToMesh
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , map
  , show
  , otherwise
  , bind
  , pure
  , negate
  , ($)
  , (<>)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (&&)
  , (<=)
  )

import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Spatial.Geometry.Types 
  ( MeshData(MeshData)
  , VertexBuffer(VertexBuffer)
  , IndexBuffer(IndexBuffer)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // segments
-- ═════════════════════════════════════════════════════════════════════════════

-- | Segment count for procedural geometry [3, 256].
-- |
-- | Bounded to ensure:
-- | - Minimum 3: Valid triangle topology
-- | - Maximum 256: GPU vertex limit safety (~65k vertices for sphere)
newtype Segments = Segments Int

derive instance eqSegments :: Eq Segments
derive instance ordSegments :: Ord Segments

instance showSegments :: Show Segments where
  show (Segments s) = "(Segments " <> show s <> ")"

-- | Create segments, clamping to [3, 256].
segments :: Int -> Segments
segments n
  | n < 3 = Segments 3
  | n > 256 = Segments 256
  | otherwise = Segments n

-- | Unwrap segments value.
unwrapSegments :: Segments -> Int
unwrapSegments (Segments s) = s

-- | Default segment count (16) — good balance of quality and performance.
defaultSegments :: Segments
defaultSegments = Segments 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // cube config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for cube primitive.
type CubeConfig =
  { width :: Number      -- ^ X dimension
  , height :: Number     -- ^ Y dimension  
  , depth :: Number      -- ^ Z dimension
  , widthSegments :: Segments
  , heightSegments :: Segments
  , depthSegments :: Segments
  }

-- | Default cube: 1x1x1 unit cube centered at origin.
defaultCubeConfig :: CubeConfig
defaultCubeConfig =
  { width: 1.0
  , height: 1.0
  , depth: 1.0
  , widthSegments: Segments 1
  , heightSegments: Segments 1
  , depthSegments: Segments 1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // sphere config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for sphere primitive.
type SphereConfig =
  { radius :: Number
  , widthSegments :: Segments   -- ^ Longitude divisions
  , heightSegments :: Segments  -- ^ Latitude divisions
  , phiStart :: Number          -- ^ Horizontal start angle (radians)
  , phiLength :: Number         -- ^ Horizontal sweep angle (radians)
  , thetaStart :: Number        -- ^ Vertical start angle (radians)
  , thetaLength :: Number       -- ^ Vertical sweep angle (radians)
  }

-- | Default sphere: radius 0.5, 16x16 segments, full sphere.
defaultSphereConfig :: SphereConfig
defaultSphereConfig =
  { radius: 0.5
  , widthSegments: defaultSegments
  , heightSegments: defaultSegments
  , phiStart: 0.0
  , phiLength: Math.tau
  , thetaStart: 0.0
  , thetaLength: Math.pi
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cylinder config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for cylinder primitive.
type CylinderConfig =
  { radiusTop :: Number
  , radiusBottom :: Number
  , height :: Number
  , radialSegments :: Segments
  , heightSegments :: Segments
  , openEnded :: Boolean        -- ^ If true, no caps
  , thetaStart :: Number        -- ^ Start angle (radians)
  , thetaLength :: Number       -- ^ Sweep angle (radians)
  }

-- | Default cylinder: radius 0.5, height 1, 16 radial segments.
defaultCylinderConfig :: CylinderConfig
defaultCylinderConfig =
  { radiusTop: 0.5
  , radiusBottom: 0.5
  , height: 1.0
  , radialSegments: defaultSegments
  , heightSegments: Segments 1
  , openEnded: false
  , thetaStart: 0.0
  , thetaLength: Math.tau
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // cone config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for cone primitive.
type ConeConfig =
  { radius :: Number
  , height :: Number
  , radialSegments :: Segments
  , heightSegments :: Segments
  , openEnded :: Boolean        -- ^ If true, no base cap
  , thetaStart :: Number
  , thetaLength :: Number
  }

-- | Default cone: radius 0.5, height 1, 16 radial segments.
defaultConeConfig :: ConeConfig
defaultConeConfig =
  { radius: 0.5
  , height: 1.0
  , radialSegments: defaultSegments
  , heightSegments: Segments 1
  , openEnded: false
  , thetaStart: 0.0
  , thetaLength: Math.tau
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // torus config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for torus primitive.
type TorusConfig =
  { radius :: Number            -- ^ Major radius (center to tube center)
  , tube :: Number              -- ^ Minor radius (tube thickness)
  , radialSegments :: Segments  -- ^ Segments around tube
  , tubularSegments :: Segments -- ^ Segments around torus
  , arc :: Number               -- ^ Sweep angle (radians, tau for full torus)
  }

-- | Default torus: radius 0.5, tube 0.2, 16x16 segments.
defaultTorusConfig :: TorusConfig
defaultTorusConfig =
  { radius: 0.5
  , tube: 0.2
  , radialSegments: defaultSegments
  , tubularSegments: defaultSegments
  , arc: Math.tau
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // plane config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for plane primitive.
type PlaneConfig =
  { width :: Number
  , height :: Number
  , widthSegments :: Segments
  , heightSegments :: Segments
  }

-- | Default plane: 1x1, single quad.
defaultPlaneConfig :: PlaneConfig
defaultPlaneConfig =
  { width: 1.0
  , height: 1.0
  , widthSegments: Segments 1
  , heightSegments: Segments 1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // capsule config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for capsule primitive.
type CapsuleConfig =
  { radius :: Number
  , length :: Number            -- ^ Length of cylindrical section
  , capSegments :: Segments     -- ^ Segments in each hemisphere
  , radialSegments :: Segments
  }

-- | Default capsule: radius 0.25, length 0.5, 8x16 segments.
defaultCapsuleConfig :: CapsuleConfig
defaultCapsuleConfig =
  { radius: 0.25
  , length: 0.5
  , capSegments: Segments 8
  , radialSegments: defaultSegments
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cube generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a cube mesh.
-- |
-- | Creates an axis-aligned box centered at origin with the specified dimensions.
-- | Generates proper normals for flat shading and UVs for texturing.
cube :: CubeConfig -> MeshData
cube cfg = 
  let
    hw = cfg.width / 2.0
    hh = cfg.height / 2.0
    hd = cfg.depth / 2.0
    
    -- 8 corner vertices, but we need 24 for proper normals (4 per face)
    positions = VertexBuffer
      -- Front face (z+)
      [ negate hw, negate hh, hd
      , hw, negate hh, hd
      , hw, hh, hd
      , negate hw, hh, hd
      -- Back face (z-)
      , hw, negate hh, negate hd
      , negate hw, negate hh, negate hd
      , negate hw, hh, negate hd
      , hw, hh, negate hd
      -- Top face (y+)
      , negate hw, hh, hd
      , hw, hh, hd
      , hw, hh, negate hd
      , negate hw, hh, negate hd
      -- Bottom face (y-)
      , negate hw, negate hh, negate hd
      , hw, negate hh, negate hd
      , hw, negate hh, hd
      , negate hw, negate hh, hd
      -- Right face (x+)
      , hw, negate hh, hd
      , hw, negate hh, negate hd
      , hw, hh, negate hd
      , hw, hh, hd
      -- Left face (x-)
      , negate hw, negate hh, negate hd
      , negate hw, negate hh, hd
      , negate hw, hh, hd
      , negate hw, hh, negate hd
      ]
    
    normals = VertexBuffer
      -- Front (6 vertices * 3 components, but we have 4 per face)
      [ 0.0, 0.0, 1.0,  0.0, 0.0, 1.0,  0.0, 0.0, 1.0,  0.0, 0.0, 1.0
      -- Back
      , 0.0, 0.0, negate 1.0,  0.0, 0.0, negate 1.0,  0.0, 0.0, negate 1.0,  0.0, 0.0, negate 1.0
      -- Top
      , 0.0, 1.0, 0.0,  0.0, 1.0, 0.0,  0.0, 1.0, 0.0,  0.0, 1.0, 0.0
      -- Bottom
      , 0.0, negate 1.0, 0.0,  0.0, negate 1.0, 0.0,  0.0, negate 1.0, 0.0,  0.0, negate 1.0, 0.0
      -- Right
      , 1.0, 0.0, 0.0,  1.0, 0.0, 0.0,  1.0, 0.0, 0.0,  1.0, 0.0, 0.0
      -- Left
      , negate 1.0, 0.0, 0.0,  negate 1.0, 0.0, 0.0,  negate 1.0, 0.0, 0.0,  negate 1.0, 0.0, 0.0
      ]
    
    uvs =
      -- Each face gets 0-1 UV mapping
      [ 0.0, 0.0,  1.0, 0.0,  1.0, 1.0,  0.0, 1.0  -- Front
      , 0.0, 0.0,  1.0, 0.0,  1.0, 1.0,  0.0, 1.0  -- Back
      , 0.0, 0.0,  1.0, 0.0,  1.0, 1.0,  0.0, 1.0  -- Top
      , 0.0, 0.0,  1.0, 0.0,  1.0, 1.0,  0.0, 1.0  -- Bottom
      , 0.0, 0.0,  1.0, 0.0,  1.0, 1.0,  0.0, 1.0  -- Right
      , 0.0, 0.0,  1.0, 0.0,  1.0, 1.0,  0.0, 1.0  -- Left
      ]
    
    -- Two triangles per face, 6 faces = 36 indices
    indices = IndexBuffer
      [ 0, 1, 2,  0, 2, 3    -- Front
      , 4, 5, 6,  4, 6, 7    -- Back
      , 8, 9, 10,  8, 10, 11 -- Top
      , 12, 13, 14,  12, 14, 15 -- Bottom
      , 16, 17, 18,  16, 18, 19 -- Right
      , 20, 21, 22,  20, 22, 23 -- Left
      ]
  in
  MeshData
    { positions
    , normals: Just normals
    , uvs: Just uvs
    , tangents: Nothing
    , colors: Nothing
    , indices: Just indices
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sphere generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a UV sphere mesh.
-- |
-- | Creates a sphere centered at origin using latitude/longitude subdivision.
-- | Good for planets, balls, etc. Has pole pinching artifact.
sphere :: SphereConfig -> MeshData
sphere cfg =
  let
    widthSegs = unwrapSegments cfg.widthSegments
    heightSegs = unwrapSegments cfg.heightSegments
    
    -- Generate vertices
    vertexData = do
      iy <- Array.range 0 heightSegs
      ix <- Array.range 0 widthSegs
      let u = Int.toNumber ix / Int.toNumber widthSegs
      let v = Int.toNumber iy / Int.toNumber heightSegs
      let theta = cfg.thetaStart + v * cfg.thetaLength
      let phi = cfg.phiStart + u * cfg.phiLength
      let sinTheta = Math.sin theta
      let cosTheta = Math.cos theta
      let sinPhi = Math.sin phi
      let cosPhi = Math.cos phi
      let x = negate (cfg.radius * sinTheta * cosPhi)
      let y = cfg.radius * cosTheta
      let z = cfg.radius * sinTheta * sinPhi
      -- Normal is just the normalized position for a sphere at origin
      let nx = negate (sinTheta * cosPhi)
      let ny = cosTheta
      let nz = sinTheta * sinPhi
      pure { x, y, z, nx, ny, nz, u, v: 1.0 - v }
    
    positions = VertexBuffer $ Array.concatMap (\v -> [v.x, v.y, v.z]) vertexData
    normals = VertexBuffer $ Array.concatMap (\v -> [v.nx, v.ny, v.nz]) vertexData
    uvs = Array.concatMap (\v -> [v.u, v.v]) vertexData
    
    -- Generate indices
    indices = IndexBuffer $ Array.concat $ do
      iy <- Array.range 0 (heightSegs - 1)
      ix <- Array.range 0 (widthSegs - 1)
      let a = iy * (widthSegs + 1) + ix
      let b = a + 1
      let c = a + widthSegs + 1
      let d = c + 1
      -- Skip degenerate triangles at poles
      if iy == 0 && cfg.thetaStart == 0.0
        then pure [b, c, d]
        else if iy == heightSegs - 1 && cfg.thetaStart + cfg.thetaLength == Math.pi
          then pure [a, b, c]
          else pure [a, b, d, a, d, c]
  in
  MeshData
    { positions
    , normals: Just normals
    , uvs: Just uvs
    , tangents: Nothing
    , colors: Nothing
    , indices: Just indices
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // cylinder generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a cylinder mesh.
-- |
-- | Creates a cylinder along Y axis centered at origin.
-- | Can create cones by setting radiusTop or radiusBottom to 0.
cylinder :: CylinderConfig -> MeshData
cylinder cfg =
  let
    radialSegs = unwrapSegments cfg.radialSegments
    heightSegs = unwrapSegments cfg.heightSegments
    halfHeight = cfg.height / 2.0
    
    -- Generate side vertices
    sideData = do
      iy <- Array.range 0 heightSegs
      ix <- Array.range 0 radialSegs
      let u = Int.toNumber ix / Int.toNumber radialSegs
      let v = Int.toNumber iy / Int.toNumber heightSegs
      let theta = cfg.thetaStart + u * cfg.thetaLength
      let sinTheta = Math.sin theta
      let cosTheta = Math.cos theta
      let radius = cfg.radiusBottom + (cfg.radiusTop - cfg.radiusBottom) * v
      let x = radius * sinTheta
      let y = negate halfHeight + v * cfg.height
      let z = radius * cosTheta
      -- Normal perpendicular to surface
      let slope = (cfg.radiusBottom - cfg.radiusTop) / cfg.height
      let ny = slope / Math.sqrt (1.0 + slope * slope)
      let nLen = Math.sqrt (sinTheta * sinTheta + cosTheta * cosTheta)
      let nx = sinTheta / nLen * Math.sqrt (1.0 - ny * ny)
      let nz = cosTheta / nLen * Math.sqrt (1.0 - ny * ny)
      pure { x, y, z, nx, ny, nz, u, v }
    
    sidePositions = Array.concatMap (\v -> [v.x, v.y, v.z]) sideData
    sideNormals = Array.concatMap (\v -> [v.nx, v.ny, v.nz]) sideData
    sideUVs = Array.concatMap (\v -> [v.u, v.v]) sideData
    
    -- Generate side indices
    sideIndices = Array.concat $ do
      iy <- Array.range 0 (heightSegs - 1)
      ix <- Array.range 0 (radialSegs - 1)
      let a = iy * (radialSegs + 1) + ix
      let b = a + 1
      let c = a + radialSegs + 1
      let d = c + 1
      pure [a, b, d, a, d, c]
    
    -- For now, simplified: no caps (openEnded = true behavior)
    -- Full implementation would add cap vertices and indices
    positions = VertexBuffer sidePositions
    normals = VertexBuffer sideNormals
    indices = IndexBuffer sideIndices
  in
  MeshData
    { positions
    , normals: Just normals
    , uvs: Just sideUVs
    , tangents: Nothing
    , colors: Nothing
    , indices: Just indices
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cone generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a cone mesh.
-- |
-- | A cone is a cylinder with radiusTop = 0.
cone :: ConeConfig -> MeshData
cone cfg = cylinder
  { radiusTop: 0.0
  , radiusBottom: cfg.radius
  , height: cfg.height
  , radialSegments: cfg.radialSegments
  , heightSegments: cfg.heightSegments
  , openEnded: cfg.openEnded
  , thetaStart: cfg.thetaStart
  , thetaLength: cfg.thetaLength
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // torus generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a torus mesh.
-- |
-- | Creates a donut-shaped mesh centered at origin, lying in the XZ plane.
torus :: TorusConfig -> MeshData
torus cfg =
  let
    radialSegs = unwrapSegments cfg.radialSegments
    tubularSegs = unwrapSegments cfg.tubularSegments
    
    vertexData = do
      j <- Array.range 0 radialSegs
      i <- Array.range 0 tubularSegs
      let u = Int.toNumber i / Int.toNumber tubularSegs * cfg.arc
      let v = Int.toNumber j / Int.toNumber radialSegs * Math.tau
      let x = (cfg.radius + cfg.tube * Math.cos v) * Math.cos u
      let y = cfg.tube * Math.sin v
      let z = (cfg.radius + cfg.tube * Math.cos v) * Math.sin u
      -- Normal points from tube center to surface
      let centerX = cfg.radius * Math.cos u
      let centerZ = cfg.radius * Math.sin u
      let nx = x - centerX
      let ny = y
      let nz = z - centerZ
      let nLen = Math.sqrt (nx * nx + ny * ny + nz * nz)
      pure 
        { x, y, z
        , nx: nx / nLen, ny: ny / nLen, nz: nz / nLen
        , u: Int.toNumber i / Int.toNumber tubularSegs
        , v: Int.toNumber j / Int.toNumber radialSegs
        }
    
    positions = VertexBuffer $ Array.concatMap (\v -> [v.x, v.y, v.z]) vertexData
    normals = VertexBuffer $ Array.concatMap (\v -> [v.nx, v.ny, v.nz]) vertexData
    uvs = Array.concatMap (\v -> [v.u, v.v]) vertexData
    
    indices = IndexBuffer $ Array.concat $ do
      j <- Array.range 0 (radialSegs - 1)
      i <- Array.range 0 (tubularSegs - 1)
      let a = j * (tubularSegs + 1) + i
      let b = a + 1
      let c = a + tubularSegs + 1
      let d = c + 1
      pure [a, b, d, a, d, c]
  in
  MeshData
    { positions
    , normals: Just normals
    , uvs: Just uvs
    , tangents: Nothing
    , colors: Nothing
    , indices: Just indices
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // plane generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a plane mesh.
-- |
-- | Creates a flat rectangular mesh in the XY plane, facing +Z.
plane :: PlaneConfig -> MeshData
plane cfg =
  let
    widthSegs = unwrapSegments cfg.widthSegments
    heightSegs = unwrapSegments cfg.heightSegments
    halfW = cfg.width / 2.0
    halfH = cfg.height / 2.0
    
    vertexData = do
      iy <- Array.range 0 heightSegs
      ix <- Array.range 0 widthSegs
      let u = Int.toNumber ix / Int.toNumber widthSegs
      let v = Int.toNumber iy / Int.toNumber heightSegs
      let x = negate halfW + u * cfg.width
      let y = negate halfH + v * cfg.height
      pure { x, y, z: 0.0, u, v }
    
    positions = VertexBuffer $ Array.concatMap (\v -> [v.x, v.y, v.z]) vertexData
    normals = VertexBuffer $ Array.concatMap (\_ -> [0.0, 0.0, 1.0]) vertexData
    uvs = Array.concatMap (\v -> [v.u, v.v]) vertexData
    
    indices = IndexBuffer $ Array.concat $ do
      iy <- Array.range 0 (heightSegs - 1)
      ix <- Array.range 0 (widthSegs - 1)
      let a = iy * (widthSegs + 1) + ix
      let b = a + 1
      let c = a + widthSegs + 1
      let d = c + 1
      pure [a, b, d, a, d, c]
  in
  MeshData
    { positions
    , normals: Just normals
    , uvs: Just uvs
    , tangents: Nothing
    , colors: Nothing
    , indices: Just indices
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // capsule generator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate a capsule mesh.
-- |
-- | A capsule is a cylinder with hemispherical caps at each end.
-- | Total height = length + 2 * radius.
capsule :: CapsuleConfig -> MeshData
capsule cfg =
  -- Simplified: generate as cylinder for now
  -- Full implementation would add hemisphere caps
  cylinder
    { radiusTop: cfg.radius
    , radiusBottom: cfg.radius
    , height: cfg.length
    , radialSegments: cfg.radialSegments
    , heightSegments: cfg.capSegments
    , openEnded: false
    , thetaStart: 0.0
    , thetaLength: Math.tau
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // primitive type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unified primitive type for storing primitive parameters.
data Primitive
  = PrimCube CubeConfig
  | PrimSphere SphereConfig
  | PrimCylinder CylinderConfig
  | PrimCone ConeConfig
  | PrimTorus TorusConfig
  | PrimPlane PlaneConfig
  | PrimCapsule CapsuleConfig

derive instance eqPrimitive :: Eq Primitive

instance showPrimitive :: Show Primitive where
  show (PrimCube _) = "Primitive:Cube"
  show (PrimSphere _) = "Primitive:Sphere"
  show (PrimCylinder _) = "Primitive:Cylinder"
  show (PrimCone _) = "Primitive:Cone"
  show (PrimTorus _) = "Primitive:Torus"
  show (PrimPlane _) = "Primitive:Plane"
  show (PrimCapsule _) = "Primitive:Capsule"

-- | Convert any primitive to mesh data.
primitiveToMesh :: Primitive -> MeshData
primitiveToMesh (PrimCube cfg) = cube cfg
primitiveToMesh (PrimSphere cfg) = sphere cfg
primitiveToMesh (PrimCylinder cfg) = cylinder cfg
primitiveToMesh (PrimCone cfg) = cone cfg
primitiveToMesh (PrimTorus cfg) = torus cfg
primitiveToMesh (PrimPlane cfg) = plane cfg
primitiveToMesh (PrimCapsule cfg) = capsule cfg
