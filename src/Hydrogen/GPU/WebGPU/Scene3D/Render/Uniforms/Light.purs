-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--             // hydrogen // gpu // webgpu // scene3d // render // uniforms // light
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Light Uniforms — GPU uniform buffer structures for lighting.
--
-- Provides types and computation for:
-- - Light uniforms (ambient color, light array)
-- - Individual light data (position, type, color, intensity, etc.)
--
-- All types match their corresponding WGSL struct layouts.
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render.Uniforms.Light
  ( -- Light uniforms
    LightUniforms
  , LightData
  , computeLightUniforms
    -- Serialization
  , lightUniformsToBindGroup
  , lightDataToArray
  ) where

import Prelude
  ( map
  , (*)
  , (+)
  , (/)
  , (<>)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)

import Hydrogen.GPU.Scene3D.Light
  ( Light3D
      ( AmbientLight3D
      , DirectionalLight3D
      , PointLight3D
      , SpotLight3D
      , HemisphereLight3D
      )
  )
import Hydrogen.GPU.Scene3D.Position (Position3D, Direction3D(Direction3D), positionToMeters)
import Hydrogen.GPU.WebGPU.Scene3D.Render.Commands (BindGroupData)
import Hydrogen.Schema.Color.RGB (RGBA, rgbaToRecord)
import Hydrogen.Schema.Dimension.Physical.SI (unwrapMeter)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, getX3, getY3, getZ3, subtractVec3, normalizeVec3)
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- LIGHT UNIFORMS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Light uniforms (matches WGSL LightUniforms struct).
type LightUniforms =
  { ambientColor :: Vec3 Number
  , numLights :: Int
  , lights :: Array LightData
  }

-- | Single light data (matches WGSL Light struct).
type LightData =
  { position :: Vec3 Number
  , lightType :: Int  -- 0 = directional, 1 = point, 2 = spot
  , color :: Vec3 Number
  , intensity :: Number
  , direction :: Vec3 Number
  , range :: Number
  , innerConeAngle :: Number
  , outerConeAngle :: Number
  }

-- | Compute light uniforms from light array.
computeLightUniforms :: Array Light3D -> LightUniforms
computeLightUniforms lights =
  let
    ambientColor = extractAmbientColor lights
    nonAmbientLights = Array.filter (\l -> not (isAmbientLight l)) lights
    lightData = map lightToData nonAmbientLights
  in
    { ambientColor
    , numLights: Array.length lightData
    , lights: lightData
    }

-- | Check if light is ambient.
isAmbientLight :: Light3D -> Boolean
isAmbientLight = case _ of
  AmbientLight3D _ -> true
  HemisphereLight3D _ -> true
  _ -> false

-- | Extract combined ambient color from lights.
extractAmbientColor :: Array Light3D -> Vec3 Number
extractAmbientColor lights =
  foldl addAmbient (vec3 0.0 0.0 0.0) lights
  where
    addAmbient acc light = case light of
      AmbientLight3D params ->
        let c = rgbaToVec3 params.color
            i = params.intensity
        in vec3 
          (vecX acc + vecX c * i)
          (vecY acc + vecY c * i)
          (vecZ acc + vecZ c * i)
      HemisphereLight3D params ->
        let sky = rgbaToVec3 params.skyColor
            ground = rgbaToVec3 params.groundColor
            i = params.intensity
            avg = vec3 
              ((vecX sky + vecX ground) / 2.0 * i)
              ((vecY sky + vecY ground) / 2.0 * i)
              ((vecZ sky + vecZ ground) / 2.0 * i)
        in vec3 
          (vecX acc + vecX avg)
          (vecY acc + vecY avg)
          (vecZ acc + vecZ avg)
      _ -> acc

-- | Convert Light3D to LightData.
lightToData :: Light3D -> LightData
lightToData = case _ of
  DirectionalLight3D params ->
    { position: vec3 0.0 0.0 0.0
    , lightType: 0
    , color: rgbaToVec3 params.color
    , intensity: params.intensity
    , direction: unwrapDirection3D params.direction
    , range: 0.0
    , innerConeAngle: 0.0
    , outerConeAngle: 0.0
    }
  
  PointLight3D params ->
    { position: unwrapPosition3D params.position
    , lightType: 1
    , color: rgbaToVec3 params.color
    , intensity: params.intensity
    , direction: vec3 0.0 0.0 0.0
    , range: unwrapMeter params.distance
    , innerConeAngle: 0.0
    , outerConeAngle: 0.0
    }
  
  SpotLight3D params ->
    let
      posVec = unwrapPosition3D params.position
      targetVec = unwrapPosition3D params.target
      -- Direction from position toward target (normalized)
      dirVec = normalizeVec3 (subtractVec3 targetVec posVec)
    in
      { position: posVec
      , lightType: 2
      , color: rgbaToVec3 params.color
      , intensity: params.intensity
      , direction: dirVec
      , range: unwrapMeter params.distance
      , innerConeAngle: unwrapDegrees params.angle * 0.8  -- Inner cone slightly smaller
      , outerConeAngle: unwrapDegrees params.angle
      }
  
  -- Ambient lights don't produce LightData (handled separately)
  AmbientLight3D _ -> emptyLightData
  HemisphereLight3D _ -> emptyLightData

emptyLightData :: LightData
emptyLightData =
  { position: vec3 0.0 0.0 0.0
  , lightType: 0
  , color: vec3 0.0 0.0 0.0
  , intensity: 0.0
  , direction: vec3 0.0 0.0 0.0
  , range: 0.0
  , innerConeAngle: 0.0
  , outerConeAngle: 0.0
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP SERIALIZATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

lightUniformsToBindGroup :: LightUniforms -> BindGroupData
lightUniformsToBindGroup u =
  { uniforms: vec3ToArray u.ambientColor 
      <> [toNumber u.numLights]
      <> Array.concatMap lightDataToArray u.lights
  , textures: []
  , samplers: []
  }

lightDataToArray :: LightData -> Array Number
lightDataToArray l =
  vec3ToArray l.position
    <> [toNumber l.lightType]
    <> vec3ToArray l.color
    <> [l.intensity]
    <> vec3ToArray l.direction
    <> [l.range, l.innerConeAngle, l.outerConeAngle]

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

rgbaToVec3 :: RGBA -> Vec3 Number
rgbaToVec3 color =
  let c = rgbaToRecord color
  in vec3 (toNumber c.r / 255.0) (toNumber c.g / 255.0) (toNumber c.b / 255.0)

vec3ToArray :: Vec3 Number -> Array Number
vec3ToArray v = [vecX v, vecY v, vecZ v]

-- Vec3 accessors
vecX :: Vec3 Number -> Number
vecX = getX3

vecY :: Vec3 Number -> Number
vecY = getY3

vecZ :: Vec3 Number -> Number
vecZ = getZ3

-- Boolean negation
not :: Boolean -> Boolean
not true = false
not false = true

-- Position/Direction unwrap helpers
unwrapPosition3D :: Position3D -> Vec3 Number
unwrapPosition3D pos =
  let m = positionToMeters pos
  in vec3 m.x m.y m.z

unwrapDirection3D :: Direction3D -> Vec3 Number
unwrapDirection3D (Direction3D v) = v
