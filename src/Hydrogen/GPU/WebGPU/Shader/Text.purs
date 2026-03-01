-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // gpu // webgpu // shader // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Signed Distance Field (SDF) text WGSL shaders.
--
-- Renders high-quality scalable text using SDF font atlases.
-- Supports:
-- - Anti-aliased edges at any scale
-- - Outline rendering
-- - Configurable softness
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Shader.Text
  ( sdfTextVertexShader
  , sdfTextFragmentShader
  ) where

import Hydrogen.GPU.WebGPU.Shader.Types (WGSLSource(WGSLSource))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SDF TEXT SHADERS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SDF text vertex shader — transforms glyph quads.
sdfTextVertexShader :: WGSLSource
sdfTextVertexShader = WGSLSource
  """
struct FrameUniforms {
  viewProjection: mat4x4<f32>,
  cameraPosition: vec3<f32>,
  time: f32,
}

struct TextUniforms {
  model: mat4x4<f32>,
  color: vec4<f32>,
  outlineColor: vec4<f32>,
  outlineWidth: f32,
  softness: f32,
  _padding: vec2<f32>,
}

@group(0) @binding(0) var<uniform> frame: FrameUniforms;
@group(1) @binding(0) var<uniform> text: TextUniforms;

struct VertexInput {
  @location(0) position: vec3<f32>,
  @location(1) uv: vec2<f32>,
}

struct VertexOutput {
  @builtin(position) clipPosition: vec4<f32>,
  @location(0) uv: vec2<f32>,
}

@vertex
fn main(input: VertexInput) -> VertexOutput {
  var output: VertexOutput;
  let worldPos = text.model * vec4<f32>(input.position, 1.0);
  output.clipPosition = frame.viewProjection * worldPos;
  output.uv = input.uv;
  return output;
}
"""

-- | SDF text fragment shader — renders signed distance field glyphs.
-- | Supports anti-aliasing and outlines.
sdfTextFragmentShader :: WGSLSource
sdfTextFragmentShader = WGSLSource
  """
struct TextUniforms {
  model: mat4x4<f32>,
  color: vec4<f32>,
  outlineColor: vec4<f32>,
  outlineWidth: f32,
  softness: f32,
  _padding: vec2<f32>,
}

@group(1) @binding(0) var<uniform> text: TextUniforms;
@group(1) @binding(1) var fontAtlas: texture_2d<f32>;
@group(1) @binding(2) var fontSampler: sampler;

struct FragmentInput {
  @location(0) uv: vec2<f32>,
}

@fragment
fn main(input: FragmentInput) -> @location(0) vec4<f32> {
  let distance = textureSample(fontAtlas, fontSampler, input.uv).r;
  
  // SDF threshold (0.5 = edge)
  let edge = 0.5;
  
  // Anti-aliasing width based on screen-space derivatives
  let screenPxDistance = fwidth(distance) * text.softness;
  
  // Fill alpha
  let fillAlpha = smoothstep(edge - screenPxDistance, edge + screenPxDistance, distance);
  
  // Outline
  let outlineEdge = edge - text.outlineWidth;
  let outlineAlpha = smoothstep(outlineEdge - screenPxDistance, outlineEdge + screenPxDistance, distance);
  
  // Blend fill and outline
  let outlineBlend = outlineAlpha - fillAlpha;
  let color = mix(text.outlineColor.rgb, text.color.rgb, fillAlpha);
  let alpha = max(fillAlpha * text.color.a, outlineBlend * text.outlineColor.a);
  
  return vec4<f32>(color, alpha);
}
"""
