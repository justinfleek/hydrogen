-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // gpu // webgpu // shader // postprocess
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Post-processing WGSL shaders.
--
-- Fullscreen quad rendering for image-space effects:
-- - Tonemapping (ACES filmic curve)
-- - Gamma correction
-- - Exposure control
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.PostProcess
  ( fullscreenVertexShader
  , tonemapFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FULLSCREEN QUAD / POST-PROCESSING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fullscreen vertex shader — generates a fullscreen triangle.
fullscreenVertexShader :: WGSLSource
fullscreenVertexShader = WGSLSource
  """
struct VertexOutput {
  @builtin(position) position: vec4<f32>,
  @location(0) uv: vec2<f32>,
}

@vertex
fn main(@builtin(vertex_index) vertexIndex: u32) -> VertexOutput {
  var output: VertexOutput;
  
  // Generate fullscreen triangle (covers entire screen with single triangle)
  // Vertex 0: (-1, -1), UV (0, 1)
  // Vertex 1: (3, -1),  UV (2, 1)
  // Vertex 2: (-1, 3),  UV (0, -1)
  let x = f32((vertexIndex & 1u) << 2u) - 1.0;
  let y = f32((vertexIndex & 2u) << 1u) - 1.0;
  
  output.position = vec4<f32>(x, y, 0.0, 1.0);
  output.uv = vec2<f32>((x + 1.0) * 0.5, (1.0 - y) * 0.5);
  
  return output;
}
"""

-- | Tonemap fragment shader — converts HDR to LDR with ACES filmic curve.
tonemapFragmentShader :: WGSLSource
tonemapFragmentShader = WGSLSource
  """
struct TonemapUniforms {
  exposure: f32,
  gamma: f32,
  _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> tonemap: TonemapUniforms;
@group(0) @binding(1) var hdrTexture: texture_2d<f32>;
@group(0) @binding(2) var hdrSampler: sampler;

struct FragmentInput {
  @location(0) uv: vec2<f32>,
}

// ACES filmic tone mapping curve
// Attempt to approximate the ACES RRT (Reference Rendering Transform)
fn acesFilm(x: vec3<f32>) -> vec3<f32> {
  let a = 2.51;
  let b = 0.03;
  let c = 2.43;
  let d = 0.59;
  let e = 0.14;
  return clamp((x * (a * x + b)) / (x * (c * x + d) + e), vec3<f32>(0.0), vec3<f32>(1.0));
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  var hdrColor = textureSample(hdrTexture, hdrSampler, input.uv).rgb;
  
  // Apply exposure
  hdrColor = hdrColor * tonemap.exposure;
  
  // Tone mapping
  let mapped = acesFilm(hdrColor);
  
  // Gamma correction
  let gammaCorrected = pow(mapped, vec3<f32>(1.0 / tonemap.gamma));
  
  return vec4<f32>(gammaCorrected, 1.0);
}
"""
