-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // webgpu // types // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Core adapter and device types for WebGPU.
-- These are the foundational types for GPU initialization.
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.Core
  ( -- Adapter & Device
    GPUAdapterDescriptor
  , GPUDeviceDescriptor
  , GPUQueueDescriptor
  , GPULimits
  , GPUFeatureName(..)
  , GPUPowerPreference(..)
  ) where

import Prelude

import Data.Maybe (Maybe)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ADAPTER & DEVICE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Options for requesting a GPU adapter.
type GPUAdapterDescriptor =
  { powerPreference :: Maybe GPUPowerPreference
  , forceFallbackAdapter :: Boolean
  }

-- | Power preference for adapter selection.
data GPUPowerPreference
  = LowPower
  | HighPerformance

derive instance eqGPUPowerPreference :: Eq GPUPowerPreference
derive instance ordGPUPowerPreference :: Ord GPUPowerPreference

-- | Options for requesting a GPU device.
type GPUDeviceDescriptor =
  { requiredFeatures :: Array GPUFeatureName
  , requiredLimits :: Maybe GPULimits
  , label :: Maybe String
  }

-- | Queue descriptor (currently empty in WebGPU spec).
type GPUQueueDescriptor =
  { label :: Maybe String
  }

-- | Device limits. All values are maximums or minimums as appropriate.
type GPULimits =
  { maxTextureDimension1D :: Int
  , maxTextureDimension2D :: Int
  , maxTextureDimension3D :: Int
  , maxTextureArrayLayers :: Int
  , maxBindGroups :: Int
  , maxBindGroupsPlusVertexBuffers :: Int
  , maxBindingsPerBindGroup :: Int
  , maxDynamicUniformBuffersPerPipelineLayout :: Int
  , maxDynamicStorageBuffersPerPipelineLayout :: Int
  , maxSampledTexturesPerShaderStage :: Int
  , maxSamplersPerShaderStage :: Int
  , maxStorageBuffersPerShaderStage :: Int
  , maxStorageTexturesPerShaderStage :: Int
  , maxUniformBuffersPerShaderStage :: Int
  , maxUniformBufferBindingSize :: Int
  , maxStorageBufferBindingSize :: Int
  , minUniformBufferOffsetAlignment :: Int
  , minStorageBufferOffsetAlignment :: Int
  , maxVertexBuffers :: Int
  , maxBufferSize :: Number
  , maxVertexAttributes :: Int
  , maxVertexBufferArrayStride :: Int
  , maxInterStageShaderComponents :: Int
  , maxInterStageShaderVariables :: Int
  , maxColorAttachments :: Int
  , maxColorAttachmentBytesPerSample :: Int
  , maxComputeWorkgroupStorageSize :: Int
  , maxComputeInvocationsPerWorkgroup :: Int
  , maxComputeWorkgroupSizeX :: Int
  , maxComputeWorkgroupSizeY :: Int
  , maxComputeWorkgroupSizeZ :: Int
  , maxComputeWorkgroupsPerDimension :: Int
  }

-- | Optional GPU features.
data GPUFeatureName
  = DepthClipControl
  | FeatureDepth32FloatStencil8
  | TextureCompressionBC
  | TextureCompressionETC2
  | TextureCompressionASTC
  | TimestampQuery
  | IndirectFirstInstance
  | ShaderF16
  | RG11B10UfloatRenderable
  | BGRA8UnormStorage
  | Float32Filterable

derive instance eqGPUFeatureName :: Eq GPUFeatureName
derive instance ordGPUFeatureName :: Ord GPUFeatureName
