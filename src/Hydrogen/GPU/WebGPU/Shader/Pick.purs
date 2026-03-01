-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // webgpu // shader // pick
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU picking WGSL shaders.
--
-- Renders object IDs as colors for pixel-perfect GPU-accelerated picking.
-- Each object gets a unique ID encoded in RGBA, supporting up to 2^32 objects.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.Pick
  ( pickVertexShader
  , pickFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- GPU PICKING SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Picking vertex shader — same as basic transform.
pickVertexShader :: WGSLSource
pickVertexShader = WGSLSource
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
}

@vertex
fn main(input: VertexInput) -> @builtin(position) vec4<f32> {
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  return frame.viewProjection * worldPos;
}
"""

-- | Picking fragment shader — outputs object ID as color.
pickFragmentShader :: WGSLSource
pickFragmentShader = WGSLSource
  """
struct PickUniforms {
  objectId: u32,
  _padding: vec3<u32>,
}

@group(1) @binding(0) var<uniform> pick: PickUniforms;

@fragment
fn main() -> @location(0) vec4<u32> {
  // Encode object ID in RGBA (supports up to 2^32 objects)
  let r = pick.objectId & 0xFFu;
  let g = (pick.objectId >> 8u) & 0xFFu;
  let b = (pick.objectId >> 16u) & 0xFFu;
  let a = (pick.objectId >> 24u) & 0xFFu;
  return vec4<u32>(r, g, b, a);
}
"""
