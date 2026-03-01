-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // webgpu // shader // pbr
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Physically Based Rendering (PBR) WGSL shaders.
--
-- Implements Cook-Torrance BRDF with metallic-roughness workflow:
-- - GGX/Trowbridge-Reitz normal distribution function
-- - Smith-Schlick geometry function (height-correlated)
-- - Fresnel-Schlick approximation
-- - Energy conservation
--
-- PROOF REFERENCE: proofs/Hydrogen/Material/BRDF.lean
-- - fresnel_schlick
-- - ggx_distribution  
-- - smith_geometry
-- - cook_torrance
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.PBR
  ( pbrVertexShader
  , pbrFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PBR SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PBR vertex shader — same as basic, but passes tangent for normal mapping.
pbrVertexShader :: WGSLSource
pbrVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) normal: vec3<f32>,
  @location(2) uv: vec2<f32>,
  @location(3) tangent: vec4<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) worldPosition: vec3<f32>,
  @location(1) worldNormal: vec3<f32>,
  @location(2) uv: vec2<f32>,
  @location(3) worldTangent: vec3<f32>,
  @location(4) worldBitangent: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.worldPosition = worldPos.xyz;
  output.worldNormal = normalize(object.normalMatrix * input.normal);
  output.uv = input.uv;
  
  // Tangent space for normal mapping
  output.worldTangent = normalize(object.normalMatrix * input.tangent.xyz);
  output.worldBitangent = cross(output.worldNormal, output.worldTangent) * input.tangent.w;
  
  return output;
}
"""

-- | PBR fragment shader — Cook-Torrance BRDF with metallic-roughness workflow.
-- | 
-- | Implements:
-- | - GGX/Trowbridge-Reitz normal distribution function
-- | - Smith-Schlick geometry function (height-correlated)
-- | - Fresnel-Schlick approximation
-- | - Energy conservation
-- |
-- | PROOF REFERENCE: proofs/Hydrogen/Material/BRDF.lean
pbrFragmentShader :: WGSLSource
pbrFragmentShader = WGSLSource
  """
const PI: f32 = 3.14159265359;

struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct MaterialUniforms {
  baseColor: vec4<f32>,
  emissive: vec3<f32>,
  metallic: f32,
  roughness: f32,
  emissiveIntensity: f32,
  _padding: vec2<f32>,
}

struct Light {
  position: vec3<f32>,
  lightType: u32,
  color: vec3<f32>,
  intensity: f32,
  direction: vec3<f32>,
  range: f32,
  innerConeAngle: f32,
  outerConeAngle: f32,
  _padding: vec2<f32>,
}

struct LightUniforms {
  ambientColor: vec3<f32>,
  numLights: u32,
  lights: array<Light, 16>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(1) @binding(0) var<uniform> material: MaterialUniforms;
@group(3) @binding(0) var<uniform> lighting: LightUniforms;

struct FragmentInput {
  @location(0) worldPosition: vec3<f32>,
  @location(1) worldNormal: vec3<f32>,
  @location(2) uv: vec2<f32>,
  @location(3) worldTangent: vec3<f32>,
  @location(4) worldBitangent: vec3<f32>,
}

// GGX/Trowbridge-Reitz normal distribution function
// D(h) = α² / (π * ((n·h)² * (α² - 1) + 1)²)
fn distributionGGX(NdotH: f32, roughness: f32) -> f32 {
  let a = roughness * roughness;
  let a2 = a * a;
  let denom = NdotH * NdotH * (a2 - 1.0) + 1.0;
  return a2 / (PI * denom * denom);
}

// Smith-Schlick geometry function (single direction)
// G1(v) = n·v / (n·v * (1 - k) + k)
// where k = α/2 for direct lighting
fn geometrySchlickGGX(NdotV: f32, roughness: f32) -> f32 {
  let r = roughness + 1.0;
  let k = (r * r) / 8.0;
  return NdotV / (NdotV * (1.0 - k) + k);
}

// Smith geometry function (combined)
// G(l, v, h) = G1(l) * G1(v)
fn geometrySmith(NdotV: f32, NdotL: f32, roughness: f32) -> f32 {
  let ggx1 = geometrySchlickGGX(NdotV, roughness);
  let ggx2 = geometrySchlickGGX(NdotL, roughness);
  return ggx1 * ggx2;
}

// Fresnel-Schlick approximation
// F(h, v) = F0 + (1 - F0) * (1 - h·v)⁵
fn fresnelSchlick(cosTheta: f32, F0: vec3<f32>) -> vec3<f32> {
  return F0 + (1.0 - F0) * pow(clamp(1.0 - cosTheta, 0.0, 1.0), 5.0);
}

// Calculate light attenuation based on distance
fn lightAttenuation(distance: f32, range: f32) -> f32 {
  if (range <= 0.0) {
    return 1.0; // Directional light
  }
  let attenuation = clamp(1.0 - pow(distance / range, 4.0), 0.0, 1.0);
  return attenuation * attenuation / (distance * distance + 1.0);
}

// Main PBR calculation
fn calculatePBR(
  N: vec3<f32>,
  V: vec3<f32>,
  L: vec3<f32>,
  baseColor: vec3<f32>,
  metallic: f32,
  roughness: f32,
  lightColor: vec3<f32>,
  lightIntensity: f32,
) -> vec3<f32> {
  let H = normalize(V + L);
  
  let NdotV = max(dot(N, V), 0.001);
  let NdotL = max(dot(N, L), 0.0);
  let NdotH = max(dot(N, H), 0.0);
  let HdotV = max(dot(H, V), 0.0);
  
  // Dialectric F0 = 0.04, metal F0 = baseColor
  let F0 = mix(vec3<f32>(0.04), baseColor, metallic);
  
  // Cook-Torrance BRDF
  let D = distributionGGX(NdotH, roughness);
  let G = geometrySmith(NdotV, NdotL, roughness);
  let F = fresnelSchlick(HdotV, F0);
  
  // Specular contribution
  let numerator = D * G * F;
  let denominator = 4.0 * NdotV * NdotL + 0.0001;
  let specular = numerator / denominator;
  
  // Energy conservation: diffuse + specular must not exceed 1
  let kS = F;
  let kD = (vec3<f32>(1.0) - kS) * (1.0 - metallic);
  
  // Lambertian diffuse
  let diffuse = kD * baseColor / PI;
  
  // Final radiance
  let radiance = lightColor * lightIntensity;
  return (diffuse + specular) * radiance * NdotL;
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  let N = normalize(input.worldNormal);
  let V = normalize(frame.cameraPosition - input.worldPosition);
  
  let baseColor = material.baseColor.rgb;
  let metallic = material.metallic;
  let roughness = max(material.roughness, 0.04); // Avoid division by zero
  
  // Start with ambient
  var Lo = lighting.ambientColor * baseColor;
  
  // Accumulate light contributions
  for (var i: u32 = 0u; i < lighting.numLights; i = i + 1u) {
    let light = lighting.lights[i];
    
    var L: vec3<f32>;
    var attenuation: f32 = 1.0;
    
    // Light type: 0 = directional, 1 = point, 2 = spot
    if (light.lightType == 0u) {
      // Directional light
      L = normalize(-light.direction);
    } else {
      // Point or spot light
      let lightVec = light.position - input.worldPosition;
      let distance = length(lightVec);
      L = lightVec / distance;
      attenuation = lightAttenuation(distance, light.range);
      
      // Spot light cone attenuation
      if (light.lightType == 2u) {
        let theta = dot(L, normalize(-light.direction));
        let epsilon = light.innerConeAngle - light.outerConeAngle;
        let spotAttenuation = clamp((theta - light.outerConeAngle) / epsilon, 0.0, 1.0);
        attenuation = attenuation * spotAttenuation;
      }
    }
    
    Lo = Lo + calculatePBR(N, V, L, baseColor, metallic, roughness, light.color, light.intensity * attenuation);
  }
  
  // Add emissive
  Lo = Lo + material.emissive * material.emissiveIntensity;
  
  return vec4<f32>(Lo, material.baseColor.a);
}
"""
