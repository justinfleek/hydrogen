-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // spatial // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Geometry — 3D mesh data, parametric primitives, and deformers.
-- |
-- | ## Submodules
-- |
-- | - **Types**: Raw mesh data structures (vertices, indices, skinning)
-- | - **Primitives**: Parametric shape generators (cube, sphere, cylinder, etc.)
-- | - **Deformers**: Non-destructive mesh transformations (bend, twist, taper, etc.)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Spatial.Geometry as Geo
-- |
-- | -- Create a sphere primitive
-- | sphereMesh = Geo.sphere Geo.defaultSphereConfig
-- |
-- | -- Apply twist deformation
-- | twisted = Geo.twist Geo.defaultTwistConfig sphereMesh
-- |
-- | -- Chain multiple deformers
-- | deformed = Geo.applyDeformers
-- |   [ Geo.DefTwist Geo.defaultTwistConfig
-- |   , Geo.DefTaper Geo.defaultTaperConfig
-- |   ] sphereMesh
-- | ```
-- |
-- | ## C4D / Blender Equivalents
-- |
-- | | Hydrogen | Cinema 4D | Blender |
-- | |----------|-----------|---------|
-- | | cube | Cube | Cube |
-- | | sphere | Sphere | UV Sphere |
-- | | cylinder | Cylinder | Cylinder |
-- | | cone | Cone | Cone |
-- | | torus | Torus | Torus |
-- | | plane | Plane | Plane |
-- | | capsule | Capsule | Cylinder + Hemisphere |
-- | | bend | Bend Deformer | Simple Deform (Bend) |
-- | | twist | Twist Deformer | Simple Deform (Twist) |
-- | | taper | Taper Deformer | Simple Deform (Taper) |
-- | | bulge | Bulge Deformer | Simple Deform (Stretch) |
-- | | noise | Displacer | Displace Modifier |
-- | | spherify | Spherify Deformer | To Sphere |

module Hydrogen.Schema.Spatial.Geometry
  ( -- * Re-exports from Types
    module Hydrogen.Schema.Spatial.Geometry.Types
  
  -- * Re-exports from Primitives
  , module Hydrogen.Schema.Spatial.Geometry.Primitives
  
  -- * Re-exports from Deformers
  , module Hydrogen.Schema.Spatial.Geometry.Deformers
  ) where

import Hydrogen.Schema.Spatial.Geometry.Types
  ( VertexBuffer(VertexBuffer)
  , IndexBuffer(IndexBuffer)
  , MeshData(MeshData)
  , BoneIndex
  , boneIndex
  , BoneWeight
  , boneWeight
  , SkinWeight
  , Bone(Bone)
  , Skeleton(Skeleton)
  , SkinnedMesh(SkinnedMesh)
  , InstanceData
  , InstancedMesh(InstancedMesh)
  , PointCloudData
  , PointCloud(PointCloud)
  , LineVertex
  , Line3D(Line3D)
  , LineStyle(LineSolid, LineDashed, LineDotted)
  , Sprite3D(Sprite3D)
  , SpriteAlignment(AlignCamera, AlignCameraY, AlignWorld)
  , Geometry(GeoMesh, GeoSkinned, GeoInstanced, GeoPoints, GeoLine, GeoSprite)
  , meshData
  , skinnedMesh
  , instancedMesh
  , pointCloud
  , line3D
  , sprite3D
  , vertexCount
  , triangleCount
  , hasNormals
  , hasUVs
  )

import Hydrogen.Schema.Spatial.Geometry.Primitives
  ( Segments
  , segments
  , unwrapSegments
  , defaultSegments
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
  , cube
  , sphere
  , cylinder
  , cone
  , torus
  , plane
  , capsule
  , Primitive(PrimCube, PrimSphere, PrimCylinder, PrimCone, PrimTorus, PrimPlane, PrimCapsule)
  , primitiveToMesh
  )

import Hydrogen.Schema.Spatial.Geometry.Deformers
  ( BendConfig
  , defaultBendConfig
  , TwistConfig
  , defaultTwistConfig
  , TaperConfig
  , defaultTaperConfig
  , BulgeConfig
  , defaultBulgeConfig
  , NoiseConfig
  , defaultNoiseConfig
  , SpherifyConfig
  , defaultSpherifyConfig
  , DeformAxis(AxisX, AxisY, AxisZ)
  , bend
  , twist
  , taper
  , bulge
  , noise
  , spherify
  , Deformer(DefBend, DefTwist, DefTaper, DefBulge, DefNoise, DefSpherify)
  , applyDeformer
  , applyDeformers
  , recalculateNormals
  )
