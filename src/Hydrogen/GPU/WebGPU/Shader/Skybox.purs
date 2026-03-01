-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // webgpu // shader // skybox
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Skybox WGSL shaders.
--
-- Renders environment cubemaps at infinite distance.
-- Vertex shader removes translation from view matrix so skybox stays at camera.
-- Depth is set to far plane (z = w) for correct depth testing.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.Skybox
  ( skyboxVertexShader
  , skyboxFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SKYBOX SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Skybox vertex shader — renders at infinite distance.
skyboxVertexShader :: WGSLSource
skyboxVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) localPosition: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  
  // Remove translation from view matrix (skybox stays at camera)
  var viewNoTranslation = frame.viewProjection;
  viewNoTranslation[3] = vec4<f32>(0.0, 0.0, 0.0, 1.0);
  
  let clipPos = viewNoTranslation * vec4<f32>(input.position, 1.0);
  
  // Set z = w so depth is always at far plane
  output.clipPosition = vec4<f32>(clipPos.xy, clipPos.w, clipPos.w);
  output.localPosition = input.position;
  
  return output;
}
"""

-- | Skybox fragment shader — samples cubemap.
skyboxFragmentShader :: WGSLSource
skyboxFragmentShader = WGSLSource
  """
@group(1) @binding(0) var skyboxTexture: texture_cube<f32>;
@group(1) @binding(1) var skyboxSampler: sampler;

struct FragmentInput {
  @location(0) localPosition: vec3<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  let color = textureSample(skyboxTexture, skyboxSampler, normalize(input.localPosition));
  return color;
}
"""
