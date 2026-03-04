-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gpu // limits // feature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Features and Device Limits — Optional features and the complete
-- | device limits record.
-- |
-- | ## Features vs Limits
-- |
-- | - **Limits**: Numeric constraints on resource usage (all bounded)
-- | - **Features**: Boolean capabilities that may or may not be available
-- |
-- | Features extend base WebGPU functionality. Applications should check
-- | feature availability before using extended functionality.
-- |
-- | ## Device Limits Record
-- |
-- | The DeviceLimits record aggregates all bounded limit types into a single
-- | structure that describes a GPU device's capabilities.
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.GPU.Limits.Texture
-- | - Hydrogen.Schema.GPU.Limits.Binding
-- | - Hydrogen.Schema.GPU.Limits.Buffer
-- | - Hydrogen.Schema.GPU.Limits.Vertex
-- | - Hydrogen.Schema.GPU.Limits.Compute

module Hydrogen.Schema.GPU.Limits.Feature
  ( -- * GPU Features
    GPUFeature
      ( FeatureDepthClipControl
      , FeatureDepth32FloatStencil8
      , FeatureTextureCompressionBC
      , FeatureTextureCompressionETC2
      , FeatureTextureCompressionASTC
      , FeatureTimestampQuery
      , FeatureIndirectFirstInstance
      , FeatureShaderF16
      , FeatureRG11B10UfloatRenderable
      , FeatureBGRA8UnormStorage
      , FeatureFloat32Filterable
      )
  , allGPUFeatures
  , featureToString
  , featureFromString
  
  -- * Power Preference
  , PowerPreference(LowPower, HighPerformance, NoPreference)
  , powerPreferenceToString
  
  -- * Device Limits Record
  , DeviceLimits
  , defaultLimits
  , minGuaranteedLimits
  
  -- * Limit Accessors
  , limitsTextureDimension2D
  , limitsMaxBufferSize
  , limitsMaxBindGroups
  , limitsMaxComputeWorkgroupsPerDimension
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.GPU.Limits.Texture
  ( TextureDimension1D
  , TextureDimension2D
  , TextureDimension3D
  , TextureArrayLayers
  , clampTextureDimension1D
  , clampTextureDimension2D
  , clampTextureDimension3D
  , clampTextureArrayLayers
  )

import Hydrogen.Schema.GPU.Limits.Binding
  ( BindGroupCount
  , BindingsPerGroup
  , clampBindGroupCount
  , clampBindingsPerGroup
  )

import Hydrogen.Schema.GPU.Limits.Buffer
  ( BufferSize
  , UniformBufferBindingSize
  , StorageBufferBindingSize
  , bufferSizeMB
  , clampUniformBufferBindingSize
  , clampStorageBufferBindingSize
  )

import Hydrogen.Schema.GPU.Limits.Vertex
  ( VertexBufferCount
  , VertexAttributeCount
  , VertexBufferStride
  , clampVertexBufferCount
  , clampVertexAttributeCount
  , clampVertexBufferStride
  )

import Hydrogen.Schema.GPU.Limits.Compute
  ( WorkgroupSize
  , WorkgroupCount
  , WorkgroupStorageSize
  , ColorAttachmentCount
  , clampWorkgroupSize
  , clampWorkgroupCount
  , clampWorkgroupStorageSize
  , clampColorAttachmentCount
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // GPU features
-- ═════════════════════════════════════════════════════════════════════════════

-- | Optional GPU features.
-- |
-- | These extend base WebGPU functionality and may not be
-- | available on all hardware.
data GPUFeature
  = FeatureDepthClipControl
    -- ^ Control depth clipping behavior in the rasterizer
  | FeatureDepth32FloatStencil8
    -- ^ Use depth32float-stencil8 texture format
  | FeatureTextureCompressionBC
    -- ^ BC (S3TC/DXT) texture compression (common on desktop)
  | FeatureTextureCompressionETC2
    -- ^ ETC2 texture compression (common on mobile)
  | FeatureTextureCompressionASTC
    -- ^ ASTC texture compression (high quality, mobile)
  | FeatureTimestampQuery
    -- ^ GPU timestamp queries for profiling
  | FeatureIndirectFirstInstance
    -- ^ Support firstInstance in indirect draw calls
  | FeatureShaderF16
    -- ^ 16-bit float operations in shaders
  | FeatureRG11B10UfloatRenderable
    -- ^ Render to RG11B10Ufloat format (HDR)
  | FeatureBGRA8UnormStorage
    -- ^ Use BGRA8Unorm as storage texture
  | FeatureFloat32Filterable
    -- ^ Linear filtering on float32 textures

derive instance eqGPUFeature :: Eq GPUFeature
derive instance ordGPUFeature :: Ord GPUFeature

instance showGPUFeature :: Show GPUFeature where
  show = featureToString

-- | All GPU features.
allGPUFeatures :: Array GPUFeature
allGPUFeatures =
  [ FeatureDepthClipControl
  , FeatureDepth32FloatStencil8
  , FeatureTextureCompressionBC
  , FeatureTextureCompressionETC2
  , FeatureTextureCompressionASTC
  , FeatureTimestampQuery
  , FeatureIndirectFirstInstance
  , FeatureShaderF16
  , FeatureRG11B10UfloatRenderable
  , FeatureBGRA8UnormStorage
  , FeatureFloat32Filterable
  ]

-- | Convert feature to WebGPU spec string.
featureToString :: GPUFeature -> String
featureToString FeatureDepthClipControl = "depth-clip-control"
featureToString FeatureDepth32FloatStencil8 = "depth32float-stencil8"
featureToString FeatureTextureCompressionBC = "texture-compression-bc"
featureToString FeatureTextureCompressionETC2 = "texture-compression-etc2"
featureToString FeatureTextureCompressionASTC = "texture-compression-astc"
featureToString FeatureTimestampQuery = "timestamp-query"
featureToString FeatureIndirectFirstInstance = "indirect-first-instance"
featureToString FeatureShaderF16 = "shader-f16"
featureToString FeatureRG11B10UfloatRenderable = "rg11b10ufloat-renderable"
featureToString FeatureBGRA8UnormStorage = "bgra8unorm-storage"
featureToString FeatureFloat32Filterable = "float32-filterable"

-- | Parse feature from WebGPU spec string.
featureFromString :: String -> Maybe GPUFeature
featureFromString "depth-clip-control" = Just FeatureDepthClipControl
featureFromString "depth32float-stencil8" = Just FeatureDepth32FloatStencil8
featureFromString "texture-compression-bc" = Just FeatureTextureCompressionBC
featureFromString "texture-compression-etc2" = Just FeatureTextureCompressionETC2
featureFromString "texture-compression-astc" = Just FeatureTextureCompressionASTC
featureFromString "timestamp-query" = Just FeatureTimestampQuery
featureFromString "indirect-first-instance" = Just FeatureIndirectFirstInstance
featureFromString "shader-f16" = Just FeatureShaderF16
featureFromString "rg11b10ufloat-renderable" = Just FeatureRG11B10UfloatRenderable
featureFromString "bgra8unorm-storage" = Just FeatureBGRA8UnormStorage
featureFromString "float32-filterable" = Just FeatureFloat32Filterable
featureFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // power preference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Adapter power preference.
-- |
-- | Hints to the system which GPU to prefer when multiple are available.
data PowerPreference
  = LowPower
    -- ^ Prefer integrated GPU (better battery life)
  | HighPerformance
    -- ^ Prefer discrete GPU (better performance)
  | NoPreference
    -- ^ Let the system decide

derive instance eqPowerPreference :: Eq PowerPreference
derive instance ordPowerPreference :: Ord PowerPreference

instance showPowerPreference :: Show PowerPreference where
  show = powerPreferenceToString

-- | Convert power preference to WebGPU spec string.
powerPreferenceToString :: PowerPreference -> String
powerPreferenceToString LowPower = "low-power"
powerPreferenceToString HighPerformance = "high-performance"
powerPreferenceToString NoPreference = "undefined"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // device limits
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete device limits record with bounded types.
-- |
-- | This record captures the capabilities of a GPU device using
-- | bounded types to ensure all values are within WebGPU spec limits.
type DeviceLimits =
  { maxTextureDimension1D :: TextureDimension1D
  , maxTextureDimension2D :: TextureDimension2D
  , maxTextureDimension3D :: TextureDimension3D
  , maxTextureArrayLayers :: TextureArrayLayers
  , maxBindGroups :: BindGroupCount
  , maxBindingsPerBindGroup :: BindingsPerGroup
  , maxBufferSize :: BufferSize
  , maxUniformBufferBindingSize :: UniformBufferBindingSize
  , maxStorageBufferBindingSize :: StorageBufferBindingSize
  , maxVertexBuffers :: VertexBufferCount
  , maxVertexAttributes :: VertexAttributeCount
  , maxVertexBufferArrayStride :: VertexBufferStride
  , maxColorAttachments :: ColorAttachmentCount
  , maxComputeWorkgroupSizeX :: WorkgroupSize
  , maxComputeWorkgroupSizeY :: WorkgroupSize
  , maxComputeWorkgroupSizeZ :: WorkgroupSize
  , maxComputeWorkgroupsPerDimension :: WorkgroupCount
  , maxComputeWorkgroupStorageSize :: WorkgroupStorageSize
  }

-- | Default limits (WebGPU spec defaults).
-- |
-- | These are the guaranteed minimum limits that all WebGPU implementations
-- | must support. Real hardware typically supports higher limits.
defaultLimits :: DeviceLimits
defaultLimits =
  { maxTextureDimension1D: clampTextureDimension1D 8192
  , maxTextureDimension2D: clampTextureDimension2D 8192
  , maxTextureDimension3D: clampTextureDimension3D 2048
  , maxTextureArrayLayers: clampTextureArrayLayers 256
  , maxBindGroups: clampBindGroupCount 4
  , maxBindingsPerBindGroup: clampBindingsPerGroup 1000
  , maxBufferSize: bufferSizeMB 256
  , maxUniformBufferBindingSize: clampUniformBufferBindingSize 65536
  , maxStorageBufferBindingSize: clampStorageBufferBindingSize 134217728
  , maxVertexBuffers: clampVertexBufferCount 8
  , maxVertexAttributes: clampVertexAttributeCount 16
  , maxVertexBufferArrayStride: clampVertexBufferStride 2048
  , maxColorAttachments: clampColorAttachmentCount 8
  , maxComputeWorkgroupSizeX: clampWorkgroupSize 256
  , maxComputeWorkgroupSizeY: clampWorkgroupSize 256
  , maxComputeWorkgroupSizeZ: clampWorkgroupSize 64
  , maxComputeWorkgroupsPerDimension: clampWorkgroupCount 65535
  , maxComputeWorkgroupStorageSize: clampWorkgroupStorageSize 16384
  }

-- | Minimum guaranteed limits (alias for defaultLimits).
-- |
-- | All WebGPU hardware must support at least these limits.
minGuaranteedLimits :: DeviceLimits
minGuaranteedLimits = defaultLimits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // limit accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accessor for texture dimension 2D.
limitsTextureDimension2D :: DeviceLimits -> TextureDimension2D
limitsTextureDimension2D l = l.maxTextureDimension2D

-- | Accessor for max buffer size.
limitsMaxBufferSize :: DeviceLimits -> BufferSize
limitsMaxBufferSize l = l.maxBufferSize

-- | Accessor for max bind groups.
limitsMaxBindGroups :: DeviceLimits -> BindGroupCount
limitsMaxBindGroups l = l.maxBindGroups

-- | Accessor for max compute workgroups per dimension.
limitsMaxComputeWorkgroupsPerDimension :: DeviceLimits -> WorkgroupCount
limitsMaxComputeWorkgroupsPerDimension l = l.maxComputeWorkgroupsPerDimension
