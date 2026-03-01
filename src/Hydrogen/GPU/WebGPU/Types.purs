-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // gpu // webgpu // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Pure PureScript types wrapping WebGPU concepts.
-- No FFI here — these are the vocabulary.
--
-- This is a leader module that re-exports all submodules:
-- - Core: Adapter and device types
-- - Buffer: Buffer types
-- - Texture: Texture types
-- - Sampler: Sampler types
-- - Shader: Shader types
-- - Pipeline: Vertex, primitive, fragment, depth/stencil, multisample, 
--             pipeline, and bind group types
-- - RenderPass: Render pass and canvas configuration types
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types
  ( -- Re-exports from Core
    module Core
    -- Re-exports from Buffer
  , module Buffer
    -- Re-exports from Texture
  , module Texture
    -- Re-exports from Sampler
  , module Sampler
    -- Re-exports from Shader
  , module Shader
    -- Re-exports from Pipeline
  , module Pipeline
    -- Re-exports from RenderPass
  , module RenderPass
  ) where

import Hydrogen.GPU.WebGPU.Types.Core
  ( GPUAdapterDescriptor
  , GPUDeviceDescriptor
  , GPUQueueDescriptor
  , GPULimits
  , GPUFeatureName(..)
  , GPUPowerPreference(..)
  ) as Core

import Hydrogen.GPU.WebGPU.Types.Buffer
  ( GPUBufferDescriptor
  , GPUBufferUsage(..)
  , GPUMapMode(..)
  , combineBufferUsage
  , combineMapMode
  ) as Buffer

import Hydrogen.GPU.WebGPU.Types.Texture
  ( GPUTextureDescriptor
  , GPUTextureFormat(..)
  , GPUTextureUsage(..)
  , GPUTextureDimension(..)
  , GPUTextureViewDescriptor
  , GPUTextureViewDimension(..)
  , GPUTextureAspect(..)
  , combineTextureUsage
  ) as Texture

import Hydrogen.GPU.WebGPU.Types.Sampler
  ( GPUSamplerDescriptor
  , GPUAddressMode(..)
  , GPUFilterMode(..)
  , GPUMipmapFilterMode(..)
  , GPUCompareFunction(..)
  ) as Sampler

import Hydrogen.GPU.WebGPU.Types.Shader
  ( GPUShaderModuleDescriptor
  , WGSLSource(..)
  ) as Shader

import Hydrogen.GPU.WebGPU.Types.Pipeline
  ( GPUVertexState
  , GPUVertexBufferLayout
  , GPUVertexAttribute
  , GPUVertexFormat(..)
  , GPUVertexStepMode(..)
  , GPUPrimitiveState
  , GPUPrimitiveTopology(..)
  , GPUCullMode(..)
  , GPUFrontFace(..)
  , GPUIndexFormat(..)
  , GPUFragmentState
  , GPUColorTargetState
  , GPUBlendState
  , GPUBlendComponent
  , GPUBlendFactor(..)
  , GPUBlendOperation(..)
  , GPUColorWriteMask(..)
  , combineColorWriteMask
  , GPUDepthStencilState
  , GPUStencilFaceState
  , GPUStencilOperation(..)
  , GPUMultisampleState
  , GPURenderPipelineDescriptor
  , GPUComputePipelineDescriptor
  , GPUPipelineLayoutDescriptor
  , GPUBindGroupLayoutDescriptor
  , GPUBindGroupLayoutEntry
  , GPUBindGroupDescriptor
  , GPUBindGroupEntry
  , BindGroupResourceType(..)
  , GPUBufferBindingType(..)
  , GPUSamplerBindingType(..)
  , GPUTextureSampleType(..)
  , GPUStorageTextureAccess(..)
  , GPUShaderStage(..)
  , combineShaderStage
  ) as Pipeline

import Hydrogen.GPU.WebGPU.Types.RenderPass
  ( GPURenderPassDescriptor
  , GPURenderPassColorAttachment
  , GPURenderPassDepthStencilAttachment
  , GPULoadOp(..)
  , GPUStoreOp(..)
  , GPUCanvasConfiguration
  , GPUCanvasAlphaMode(..)
  ) as RenderPass
