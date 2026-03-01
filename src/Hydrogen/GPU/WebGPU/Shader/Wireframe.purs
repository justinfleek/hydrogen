-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // gpu // webgpu // shader // wireframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Wireframe WGSL shaders.
--
-- Renders triangle edges using barycentric coordinates.
-- Supports:
-- - Configurable line width
-- - Anti-aliased edges
-- - Fill color behind wireframe
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.Wireframe
  ( wireframeVertexShader
  , wireframeFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- WIREFRAME SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Wireframe vertex shader — basic transform.
wireframeVertexShader :: WGSLSource
wireframeVertexShader = WGSLSource
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
  @location(1) barycentric: vec3<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) barycentric: vec3<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.barycentric = input.barycentric;
  return output;
}
"""

-- | Wireframe fragment shader — renders edges using barycentric coordinates.
wireframeFragmentShader :: WGSLSource
wireframeFragmentShader = WGSLSource
  """
struct WireframeUniforms {
  lineColor: vec4<f32>,
  fillColor: vec4<f32>,
  lineWidth: f32,
  _padding: vec3<f32>,
}

@group(1) @binding(0) var<uniform> wireframe: WireframeUniforms;

struct FragmentInput {
  @location(0) barycentric: vec3<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  // Calculate distance to nearest edge using barycentric coordinates
  let bary = input.barycentric;
  let d = min(min(bary.x, bary.y), bary.z);
  
  // Anti-aliased edge
  let lineWidthPx = wireframe.lineWidth;
  let derivative = fwidth(d);
  let edge = smoothstep(0.0, derivative * lineWidthPx, d);
  
  // Blend line and fill
  return mix(wireframe.lineColor, wireframe.fillColor, edge);
}
"""
