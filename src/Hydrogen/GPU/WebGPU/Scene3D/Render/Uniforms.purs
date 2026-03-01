-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // gpu // webgpu // scene3d // render // uniforms
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Uniform Data — GPU uniform buffer structures.
--
-- Provides types and computation for:
-- - Frame uniforms (camera matrices, time)
-- - Light uniforms (re-exported from Light submodule)
-- - Object uniforms (model/normal matrices)
-- - Material uniforms (PBR parameters)
--
-- All types match their corresponding WGSL struct layouts.
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render.Uniforms
  ( -- Frame uniforms
    FrameUniforms
  , computeFrameUniforms
    -- Light uniforms (re-exported)
  , module Light
    -- Object uniforms
  , ObjectUniforms
  , computeObjectUniforms
    -- Material uniforms
  , MaterialUniforms
  , computeMaterialUniforms
    -- Transform utilities
  , computeEulerRotation
  , identityTransform
    -- Serialization (for Batching module)
  , frameUniformsToBindGroup
  , objectUniformsToBindGroup
  , materialUniformsToBindGroup
  ) where

import Prelude
  ( (/)
  , (<>)
  )

import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.Scene3D.Camera
  ( Camera3D
      ( PerspectiveCamera3D
      , OrthographicCamera3D
      )
  )
import Hydrogen.GPU.Scene3D.Material
  ( Material3D
      ( BasicMaterial3D
      , StandardMaterial3D
      , PhysicalMaterial3D
      )
  )
import Hydrogen.GPU.Scene3D.Mesh (MeshParams)
import Hydrogen.GPU.Scene3D.Position (Position3D, Direction3D(Direction3D), positionToMeters)
import Hydrogen.GPU.WebGPU.Scene3D.Render.Commands (BindGroupData)
import Hydrogen.GPU.WebGPU.Scene3D.Render.Uniforms.Light
  ( LightUniforms
  , LightData
  , computeLightUniforms
  , lightUniformsToBindGroup
  , lightDataToArray
  ) as Light
import Hydrogen.Schema.Color.RGB (RGBA, rgbaToRecord)
import Hydrogen.Schema.Dimension.Matrix.Mat4
  ( Mat4
  , mat4Identity
  , makePerspective
  , makeOrthographic
  , makeLookAt
  , makeTranslation4
  , makeRotationX4
  , makeRotationY4
  , makeRotationZ4
  , makeScale4
  , mulMat4
  , transposeMat4
  , invertMat4
  , toArray16
  )
import Hydrogen.Schema.Dimension.Physical.SI (unwrapMeter)
import Hydrogen.Schema.Dimension.Rotation.Quaternion (Quaternion, toMat4Quaternion)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, getX3, getY3, getZ3)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4, vec4, getX4, getY4, getZ4, getW4)
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRAME UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frame-level uniforms (updated once per frame).
-- | Matches WGSL FrameUniforms struct.
type FrameUniforms =
  { viewMatrix :: Mat4
  , projectionMatrix :: Mat4
  , viewProjectionMatrix :: Mat4
  , cameraPosition :: Vec3 Number
  , time :: Number
  }

-- | Compute frame uniforms from camera.
computeFrameUniforms :: Camera3D -> FrameUniforms
computeFrameUniforms camera =
  let
    viewMatrix = computeViewMatrix camera
    projectionMatrix = computeProjectionMatrix camera
    viewProjectionMatrix = mulMat4 projectionMatrix viewMatrix
    cameraPosition = getCameraPosition camera
  in
    { viewMatrix
    , projectionMatrix
    , viewProjectionMatrix
    , cameraPosition
    , time: 0.0  -- Set by runtime
    }

-- | Compute view matrix from camera.
computeViewMatrix :: Camera3D -> Mat4
computeViewMatrix = case _ of
  PerspectiveCamera3D params ->
    let
      pos = unwrapPosition3D params.position
      target = unwrapPosition3D params.target
      up = unwrapDirection3D params.up
    in
      makeLookAt pos target up
  
  OrthographicCamera3D params ->
    let
      pos = unwrapPosition3D params.position
      target = unwrapPosition3D params.target
      up = unwrapDirection3D params.up
    in
      makeLookAt pos target up

-- | Compute projection matrix from camera.
computeProjectionMatrix :: Camera3D -> Mat4
computeProjectionMatrix = case _ of
  PerspectiveCamera3D params ->
    let
      fov = unwrapDegrees params.fov
      aspect = params.aspect
      near = unwrapMeter params.near
      far = unwrapMeter params.far
    in
      makePerspective fov aspect near far
  
  OrthographicCamera3D params ->
    let
      left = unwrapMeter params.left
      right = unwrapMeter params.right
      top = unwrapMeter params.top
      bottom = unwrapMeter params.bottom
      near = unwrapMeter params.near
      far = unwrapMeter params.far
    in
      makeOrthographic left right bottom top near far

-- | Get camera world position.
getCameraPosition :: Camera3D -> Vec3 Number
getCameraPosition = case _ of
  PerspectiveCamera3D params -> unwrapPosition3D params.position
  OrthographicCamera3D params -> unwrapPosition3D params.position

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- OBJECT UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Per-object uniforms (matches WGSL ObjectUniforms struct).
type ObjectUniforms =
  { modelMatrix :: Mat4
  , normalMatrix :: Mat4  -- transpose(inverse(modelMatrix)) for correct normals
  }

-- | Compute object uniforms from mesh parameters.
computeObjectUniforms :: forall msg. MeshParams msg -> ObjectUniforms
computeObjectUniforms mesh =
  let
    modelMatrix = computeModelMatrix mesh
    normalMatrix = computeNormalMatrix modelMatrix
  in
    { modelMatrix
    , normalMatrix
    }

-- | Compute model matrix from mesh transform.
-- | Model = Translation x Rotation x Scale
computeModelMatrix :: forall msg. MeshParams msg -> Mat4
computeModelMatrix mesh =
  let
    pos = unwrapPosition3D mesh.position
    
    -- Extract rotation quaternion for matrix conversion
    rot :: Quaternion
    rot = mesh.rotation
    
    scl :: Vec3 Number
    scl = mesh.scale
    
    translateMat = makeTranslation4 (vecX pos) (vecY pos) (vecZ pos)
    rotateMat = toMat4Quaternion rot
    scaleMat = makeScale4 (vecX scl) (vecY scl) (vecZ scl)
  in
    -- T x R x S (standard TRS order)
    mulMat4 translateMat (mulMat4 rotateMat scaleMat)

-- | Compute normal matrix (transpose of inverse of model matrix).
-- | Required for correct normal transformation with non-uniform scaling.
-- | Falls back to transpose if matrix is singular (shouldn't happen for valid transforms).
computeNormalMatrix :: Mat4 -> Mat4
computeNormalMatrix modelMatrix =
  case invertMat4 modelMatrix of
    Just inverted -> transposeMat4 inverted
    Nothing -> transposeMat4 modelMatrix  -- Fallback for singular matrices

-- | Compute rotation matrix from Euler angles (XYZ order).
-- | 
-- | For most cases, use Quaternion rotation via computeModelMatrix.
-- | This function is provided for interop with systems that use Euler angles.
computeEulerRotation :: Number -> Number -> Number -> Mat4
computeEulerRotation rx ry rz =
  let
    rotX = makeRotationX4 rx
    rotY = makeRotationY4 ry
    rotZ = makeRotationZ4 rz
  in
    -- XYZ order: apply Z, then Y, then X (right-to-left multiplication)
    mulMat4 rotX (mulMat4 rotY rotZ)

-- | Identity matrix for transforms.
-- | 
-- | Use when no transformation is needed.
identityTransform :: Mat4
identityTransform = mat4Identity

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MATERIAL UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Material uniforms (matches WGSL MaterialUniforms struct).
type MaterialUniforms =
  { baseColor :: Vec4 Number
  , emissive :: Vec3 Number
  , metallic :: Number
  , roughness :: Number
  , emissiveIntensity :: Number
  }

-- | Compute material uniforms from Material3D.
computeMaterialUniforms :: Material3D -> MaterialUniforms
computeMaterialUniforms = case _ of
  BasicMaterial3D params ->
    { baseColor: rgbaToVec4 params.color
    , emissive: vec3 0.0 0.0 0.0
    , metallic: 0.0
    , roughness: 1.0
    , emissiveIntensity: 0.0
    }
  
  StandardMaterial3D params ->
    { baseColor: rgbaToVec4 params.color
    , emissive: rgbaToVec3 params.emissive
    , metallic: params.metalness
    , roughness: params.roughness
    , emissiveIntensity: params.emissiveIntensity
    }
  
  PhysicalMaterial3D params ->
    { baseColor: rgbaToVec4 params.color
    , emissive: rgbaToVec3 params.emissive
    , metallic: params.metalness
    , roughness: params.roughness
    , emissiveIntensity: params.emissiveIntensity
    }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP SERIALIZATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

frameUniformsToBindGroup :: FrameUniforms -> BindGroupData
frameUniformsToBindGroup u =
  { uniforms: mat4ToArray u.viewProjectionMatrix 
      <> vec3ToArray u.cameraPosition 
      <> [u.time]
  , textures: []
  , samplers: []
  }

materialUniformsToBindGroup :: MaterialUniforms -> BindGroupData
materialUniformsToBindGroup u =
  { uniforms: vec4ToArray u.baseColor
      <> vec3ToArray u.emissive
      <> [u.metallic, u.roughness, u.emissiveIntensity]
  , textures: []
  , samplers: []
  }

objectUniformsToBindGroup :: ObjectUniforms -> BindGroupData
objectUniformsToBindGroup u =
  { uniforms: mat4ToArray u.modelMatrix <> mat4ToArray u.normalMatrix
  , textures: []
  , samplers: []
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

rgbaToVec3 :: RGBA -> Vec3 Number
rgbaToVec3 color =
  let c = rgbaToRecord color
  in vec3 (toNumber c.r / 255.0) (toNumber c.g / 255.0) (toNumber c.b / 255.0)

rgbaToVec4 :: RGBA -> Vec4 Number
rgbaToVec4 color =
  let c = rgbaToRecord color
  in vec4 
    (toNumber c.r / 255.0) 
    (toNumber c.g / 255.0) 
    (toNumber c.b / 255.0) 
    (toNumber c.a / 255.0)

vec3ToArray :: Vec3 Number -> Array Number
vec3ToArray v = [vecX v, vecY v, vecZ v]

vec4ToArray :: Vec4 Number -> Array Number
vec4ToArray v = [vecX4 v, vecY4 v, vecZ4 v, vecW4 v]

mat4ToArray :: Mat4 -> Array Number
mat4ToArray = toArray16

-- Vec3 accessors
vecX :: Vec3 Number -> Number
vecX = getX3

vecY :: Vec3 Number -> Number
vecY = getY3

vecZ :: Vec3 Number -> Number
vecZ = getZ3

-- Vec4 accessors
vecX4 :: Vec4 Number -> Number
vecX4 = getX4

vecY4 :: Vec4 Number -> Number
vecY4 = getY4

vecZ4 :: Vec4 Number -> Number
vecZ4 = getZ4

vecW4 :: Vec4 Number -> Number
vecW4 = getW4

-- Position/Direction unwrap helpers
unwrapPosition3D :: Position3D -> Vec3 Number
unwrapPosition3D pos =
  let m = positionToMeters pos
  in vec3 m.x m.y m.z

unwrapDirection3D :: Direction3D -> Vec3 Number
unwrapDirection3D (Direction3D v) = v
