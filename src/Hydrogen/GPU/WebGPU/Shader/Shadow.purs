-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // webgpu // shader // shadow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Shadow mapping WGSL shaders.
--
-- Renders scene depth from light's perspective to create shadow maps.
-- Fragment shader is minimal — only depth buffer output matters.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.Shadow
  ( shadowVertexShader
  , shadowFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SHADOW MAPPING SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shadow map vertex shader — renders depth from light's perspective.
shadowVertexShader :: WGSLSource
shadowVertexShader = WGSLSource
  """
struct LightViewUniforms {
  lightViewProjection: mat4x4<f32>,
}

struct ObjectUniforms {
  model: mat4x4<f32>,
  normalMatrix: mat3x3<f32>,
}

@group(0) @binding(0) var<uniform> lightView: LightViewUniforms;
@group(2) @binding(0) var<uniform> object: ObjectUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
}

struct VertexOutput {
  @builtin(position) position: vec4<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  let worldPos = object.model * vec4<f32>(input.position, 1.0);
  output.position = lightView.lightViewProjection * worldPos;
  return output;
}
"""

-- | Shadow map fragment shader — empty, only depth is written.
shadowFragmentShader :: WGSLSource
shadowFragmentShader = WGSLSource
  """
@fragment
fn main() {
  // Depth is written automatically by the depth attachment
}
"""
