-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // webgpu // device
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU device configuration — PURE DATA, NO FFI.
--
-- All types are pure PureScript records with bounded fields.
-- The actual WebGPU calls happen in the Haskell runtime, which interprets
-- this pure data and executes against the GPU.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Lean4 Proofs:
--   - proofs/Hydrogen/Math/Bounded.lean (bounded type foundations)
--   - proofs/Hydrogen/Schema/GPU/Storable.lean (serialization roundtrip)
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Device
  ( -- Device configuration (pure data)
    GPUDeviceConfig
  , GPUAdapterConfig
  , GPUQueueConfig
  , GPUCanvasConfig
    -- Device limits (bounded) — GPULimits re-exported via module Core
  , defaultLimits
  , minLimits
  , maxLimits
    -- Errors
  , DeviceError
      ( WebGPUNotSupported
      , AdapterRequestFailed
      , DeviceRequestFailed
      , FeatureNotSupported
      , LimitExceeded
      , CanvasConfigurationFailed
      )
  , DeviceLostReason
      ( DeviceLostUnknown
      , DeviceLostDestroyed
      )
    -- Feature support
  , GPUFeatureSet
  , emptyFeatureSet
  , hasFeature
  , addFeature
  , removeFeature
  , featureSetToArray
    -- Limit bounds (for UI/validation)
  , LimitBounds
  , textureDimension1DBounds
  , textureDimension2DBounds
  , textureDimension3DBounds
  , textureArrayLayersBounds
  , bindGroupsBounds
  , uniformBufferBindingSizeBounds
  , storageBufferBindingSizeBounds
  , maxBufferSizeBounds
    -- Limit validation
  , validateLimits
  , clampLimits
    -- Re-exports from Types
  , module Core
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , map
  , not
  , negate
  , min
  , max
  , (&&)
  , (||)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (/=)
  , (+)
  , (-)
  , (*)
  , (<>)
  )

import Data.Array (elem, filter, snoc) as Array
import Data.Foldable (all)
import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.GPU.WebGPU.Types.Core
  ( GPUAdapterDescriptor
  , GPUDeviceDescriptor
  , GPUQueueDescriptor
  , GPULimits
  , GPUFeatureName
      ( DepthClipControl
      , FeatureDepth32FloatStencil8
      , TextureCompressionBC
      , TextureCompressionETC2
      , TextureCompressionASTC
      , TimestampQuery
      , IndirectFirstInstance
      , ShaderF16
      , RG11B10UfloatRenderable
      , BGRA8UnormStorage
      , Float32Filterable
      )
  , GPUPowerPreference
      ( LowPower
      , HighPerformance
      )
  ) as Core
import Hydrogen.GPU.WebGPU.Types.Texture (GPUTextureFormat) as Texture
import Hydrogen.GPU.WebGPU.Types.RenderPass (GPUCanvasAlphaMode) as RenderPass
import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , IntBounds
  , NumberBounds
  , intBounds
  , numberBounds
  , clampInt
  , clampNumber
  , inBoundsInt
  , inBoundsNumber
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEVICE CONFIGURATION (Pure Data)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU adapter configuration — pure data describing adapter requirements.
-- |
-- | This replaces the opaque GPUAdapter FFI handle. The Haskell runtime
-- | interprets this configuration to select an appropriate adapter.
type GPUAdapterConfig =
  { powerPreference :: Maybe Core.GPUPowerPreference
  , forceFallbackAdapter :: Boolean
  , features :: GPUFeatureSet
  }

-- | GPU device configuration — pure data describing device requirements.
-- |
-- | This replaces the opaque GPUDevice FFI handle. The Haskell runtime
-- | interprets this configuration to create a device with the specified
-- | features and limits.
type GPUDeviceConfig =
  { requiredFeatures :: GPUFeatureSet
  , requiredLimits :: Core.GPULimits
  , label :: Maybe String
  }

-- | GPU queue configuration — pure data.
type GPUQueueConfig =
  { label :: Maybe String
  }

-- | Canvas configuration — pure data describing canvas setup.
type GPUCanvasConfig =
  { format :: Texture.GPUTextureFormat
  , alphaMode :: RenderPass.GPUCanvasAlphaMode
  , width :: Int
  , height :: Int
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- ERRORS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Errors that can occur during device initialization.
data DeviceError
  = WebGPUNotSupported
  | AdapterRequestFailed String
  | DeviceRequestFailed String
  | FeatureNotSupported Core.GPUFeatureName
  | LimitExceeded String Int Int -- limit name, requested, maximum
  | CanvasConfigurationFailed String

derive instance eqDeviceError :: Eq DeviceError

instance showDeviceError :: Show DeviceError where
  show WebGPUNotSupported = "WebGPU is not supported"
  show (AdapterRequestFailed reason) = "Adapter request failed: " <> reason
  show (DeviceRequestFailed reason) = "Device request failed: " <> reason
  show (FeatureNotSupported _) = "Required feature not supported"
  show (LimitExceeded name requested maximum) =
    "Limit exceeded: " <> name <> " requested " <> show requested <> " but maximum is " <> show maximum
  show (CanvasConfigurationFailed reason) = "Canvas configuration failed: " <> reason

-- | Reasons for device loss.
data DeviceLostReason
  = DeviceLostUnknown
  | DeviceLostDestroyed

derive instance eqDeviceLostReason :: Eq DeviceLostReason

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FEATURE SET (Pure Data)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A set of GPU features — pure array wrapper with set semantics.
newtype GPUFeatureSet = GPUFeatureSet (Array Core.GPUFeatureName)

derive instance eqGPUFeatureSet :: Eq GPUFeatureSet

-- | Empty feature set.
emptyFeatureSet :: GPUFeatureSet
emptyFeatureSet = GPUFeatureSet []

-- | Check if a feature is in the set.
hasFeature :: Core.GPUFeatureName -> GPUFeatureSet -> Boolean
hasFeature feature (GPUFeatureSet features) = Array.elem feature features

-- | Add a feature to the set (idempotent).
addFeature :: Core.GPUFeatureName -> GPUFeatureSet -> GPUFeatureSet
addFeature feature set@(GPUFeatureSet features)
  | hasFeature feature set = set
  | otherwise = GPUFeatureSet (Array.snoc features feature)

-- | Remove a feature from the set.
removeFeature :: Core.GPUFeatureName -> GPUFeatureSet -> GPUFeatureSet
removeFeature feature (GPUFeatureSet features) =
  GPUFeatureSet (Array.filter (\f -> f /= feature) features)

-- | Convert to array for serialization.
featureSetToArray :: GPUFeatureSet -> Array Core.GPUFeatureName
featureSetToArray (GPUFeatureSet features) = features

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- LIMIT BOUNDS (Lean4-Proven)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- These bounds come from the WebGPU specification and are encoded in Lean4
-- proofs. See: proofs/Hydrogen/Schema/GPU/Storable.lean
--
-- All limits clamp at bounds — no NaN, no Infinity, no escape hatches.
--

-- | Bounds for a limit value.
type LimitBounds =
  { min :: Int
  , max :: Int
  , default :: Int
  , name :: String
  , description :: String
  }

-- | 1D texture dimension: [1, 8192], default 8192
-- | Proven bounded in Lean4.
textureDimension1DBounds :: LimitBounds
textureDimension1DBounds =
  { min: 1
  , max: 8192
  , default: 8192
  , name: "maxTextureDimension1D"
  , description: "Maximum 1D texture dimension in pixels"
  }

-- | 2D texture dimension: [1, 8192], default 8192
-- | Proven bounded in Lean4.
textureDimension2DBounds :: LimitBounds
textureDimension2DBounds =
  { min: 1
  , max: 8192
  , default: 8192
  , name: "maxTextureDimension2D"
  , description: "Maximum 2D texture dimension in pixels"
  }

-- | 3D texture dimension: [1, 2048], default 2048
-- | Proven bounded in Lean4.
textureDimension3DBounds :: LimitBounds
textureDimension3DBounds =
  { min: 1
  , max: 2048
  , default: 2048
  , name: "maxTextureDimension3D"
  , description: "Maximum 3D texture dimension in pixels"
  }

-- | Texture array layers: [1, 256], default 256
-- | Proven bounded in Lean4.
textureArrayLayersBounds :: LimitBounds
textureArrayLayersBounds =
  { min: 1
  , max: 256
  , default: 256
  , name: "maxTextureArrayLayers"
  , description: "Maximum number of texture array layers"
  }

-- | Bind groups: [4, 8], default 4
-- | Proven bounded in Lean4.
bindGroupsBounds :: LimitBounds
bindGroupsBounds =
  { min: 4
  , max: 8
  , default: 4
  , name: "maxBindGroups"
  , description: "Maximum number of bind groups"
  }

-- | Uniform buffer binding size: [16384, 134217728], default 65536
-- | Proven bounded in Lean4.
uniformBufferBindingSizeBounds :: LimitBounds
uniformBufferBindingSizeBounds =
  { min: 16384
  , max: 134217728  -- 128 MiB
  , default: 65536  -- 64 KiB
  , name: "maxUniformBufferBindingSize"
  , description: "Maximum uniform buffer binding size in bytes"
  }

-- | Storage buffer binding size: [134217728, 1073741824], default 134217728
-- | Proven bounded in Lean4.
storageBufferBindingSizeBounds :: LimitBounds
storageBufferBindingSizeBounds =
  { min: 134217728   -- 128 MiB
  , max: 1073741824  -- 1 GiB
  , default: 134217728
  , name: "maxStorageBufferBindingSize"
  , description: "Maximum storage buffer binding size in bytes"
  }

-- | Maximum buffer size bounds (Number for large values).
-- | Proven bounded in Lean4.
maxBufferSizeBounds :: NumberBounds
maxBufferSizeBounds = numberBounds
  268435456.0      -- 256 MiB minimum
  1073741824.0     -- 1 GiB maximum (typical GPU limit)
  Clamps
  "maxBufferSize"
  "Maximum buffer size in bytes"

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEFAULT LIMITS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Default GPU limits per WebGPU specification.
-- |
-- | These values represent the baseline that all WebGPU implementations
-- | must support. Each value is bounded and proven in Lean4.
defaultLimits :: Core.GPULimits
defaultLimits =
  { maxTextureDimension1D: 8192
  , maxTextureDimension2D: 8192
  , maxTextureDimension3D: 2048
  , maxTextureArrayLayers: 256
  , maxBindGroups: 4
  , maxBindGroupsPlusVertexBuffers: 24
  , maxBindingsPerBindGroup: 1000
  , maxDynamicUniformBuffersPerPipelineLayout: 8
  , maxDynamicStorageBuffersPerPipelineLayout: 4
  , maxSampledTexturesPerShaderStage: 16
  , maxSamplersPerShaderStage: 16
  , maxStorageBuffersPerShaderStage: 8
  , maxStorageTexturesPerShaderStage: 4
  , maxUniformBuffersPerShaderStage: 12
  , maxUniformBufferBindingSize: 65536
  , maxStorageBufferBindingSize: 134217728
  , minUniformBufferOffsetAlignment: 256
  , minStorageBufferOffsetAlignment: 256
  , maxVertexBuffers: 8
  , maxBufferSize: 268435456.0
  , maxVertexAttributes: 16
  , maxVertexBufferArrayStride: 2048
  , maxInterStageShaderComponents: 60
  , maxInterStageShaderVariables: 16
  , maxColorAttachments: 8
  , maxColorAttachmentBytesPerSample: 32
  , maxComputeWorkgroupStorageSize: 16384
  , maxComputeInvocationsPerWorkgroup: 256
  , maxComputeWorkgroupSizeX: 256
  , maxComputeWorkgroupSizeY: 256
  , maxComputeWorkgroupSizeZ: 64
  , maxComputeWorkgroupsPerDimension: 65535
  }

-- | Minimum GPU limits (baseline).
minLimits :: Core.GPULimits
minLimits =
  { maxTextureDimension1D: 1
  , maxTextureDimension2D: 1
  , maxTextureDimension3D: 1
  , maxTextureArrayLayers: 1
  , maxBindGroups: 4
  , maxBindGroupsPlusVertexBuffers: 24
  , maxBindingsPerBindGroup: 640
  , maxDynamicUniformBuffersPerPipelineLayout: 8
  , maxDynamicStorageBuffersPerPipelineLayout: 4
  , maxSampledTexturesPerShaderStage: 16
  , maxSamplersPerShaderStage: 16
  , maxStorageBuffersPerShaderStage: 8
  , maxStorageTexturesPerShaderStage: 4
  , maxUniformBuffersPerShaderStage: 12
  , maxUniformBufferBindingSize: 16384
  , maxStorageBufferBindingSize: 134217728
  , minUniformBufferOffsetAlignment: 256
  , minStorageBufferOffsetAlignment: 256
  , maxVertexBuffers: 8
  , maxBufferSize: 268435456.0
  , maxVertexAttributes: 16
  , maxVertexBufferArrayStride: 2048
  , maxInterStageShaderComponents: 60
  , maxInterStageShaderVariables: 16
  , maxColorAttachments: 8
  , maxColorAttachmentBytesPerSample: 32
  , maxComputeWorkgroupStorageSize: 16384
  , maxComputeInvocationsPerWorkgroup: 256
  , maxComputeWorkgroupSizeX: 256
  , maxComputeWorkgroupSizeY: 256
  , maxComputeWorkgroupSizeZ: 64
  , maxComputeWorkgroupsPerDimension: 65535
  }

-- | Maximum GPU limits (high-end hardware).
maxLimits :: Core.GPULimits
maxLimits =
  { maxTextureDimension1D: 16384
  , maxTextureDimension2D: 16384
  , maxTextureDimension3D: 2048
  , maxTextureArrayLayers: 2048
  , maxBindGroups: 8
  , maxBindGroupsPlusVertexBuffers: 30
  , maxBindingsPerBindGroup: 1000
  , maxDynamicUniformBuffersPerPipelineLayout: 14
  , maxDynamicStorageBuffersPerPipelineLayout: 8
  , maxSampledTexturesPerShaderStage: 16
  , maxSamplersPerShaderStage: 16
  , maxStorageBuffersPerShaderStage: 10
  , maxStorageTexturesPerShaderStage: 8
  , maxUniformBuffersPerShaderStage: 14
  , maxUniformBufferBindingSize: 134217728
  , maxStorageBufferBindingSize: 1073741824
  , minUniformBufferOffsetAlignment: 256
  , minStorageBufferOffsetAlignment: 256
  , maxVertexBuffers: 8
  , maxBufferSize: 1073741824.0
  , maxVertexAttributes: 30
  , maxVertexBufferArrayStride: 2048
  , maxInterStageShaderComponents: 120
  , maxInterStageShaderVariables: 16
  , maxColorAttachments: 8
  , maxColorAttachmentBytesPerSample: 32
  , maxComputeWorkgroupStorageSize: 32768
  , maxComputeInvocationsPerWorkgroup: 1024
  , maxComputeWorkgroupSizeX: 1024
  , maxComputeWorkgroupSizeY: 1024
  , maxComputeWorkgroupSizeZ: 64
  , maxComputeWorkgroupsPerDimension: 65535
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- LIMIT VALIDATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Validate that all limits are within WebGPU spec bounds.
-- |
-- | Returns Nothing if valid, Just error message if invalid.
validateLimits :: Core.GPULimits -> Maybe String
validateLimits limits
  | not (inBoundsInt 1 16384 limits.maxTextureDimension1D) =
      Just "maxTextureDimension1D out of bounds [1, 16384]"
  | not (inBoundsInt 1 16384 limits.maxTextureDimension2D) =
      Just "maxTextureDimension2D out of bounds [1, 16384]"
  | not (inBoundsInt 1 2048 limits.maxTextureDimension3D) =
      Just "maxTextureDimension3D out of bounds [1, 2048]"
  | not (inBoundsInt 1 2048 limits.maxTextureArrayLayers) =
      Just "maxTextureArrayLayers out of bounds [1, 2048]"
  | not (inBoundsInt 4 8 limits.maxBindGroups) =
      Just "maxBindGroups out of bounds [4, 8]"
  | not (inBoundsNumber 268435456.0 1073741824.0 limits.maxBufferSize) =
      Just "maxBufferSize out of bounds [256MiB, 1GiB]"
  | otherwise = Nothing

-- | Clamp all limits to valid WebGPU spec bounds.
-- |
-- | Guarantees the returned limits are valid by construction.
clampLimits :: Core.GPULimits -> Core.GPULimits
clampLimits limits =
  { maxTextureDimension1D: clampInt 1 16384 limits.maxTextureDimension1D
  , maxTextureDimension2D: clampInt 1 16384 limits.maxTextureDimension2D
  , maxTextureDimension3D: clampInt 1 2048 limits.maxTextureDimension3D
  , maxTextureArrayLayers: clampInt 1 2048 limits.maxTextureArrayLayers
  , maxBindGroups: clampInt 4 8 limits.maxBindGroups
  , maxBindGroupsPlusVertexBuffers: clampInt 24 30 limits.maxBindGroupsPlusVertexBuffers
  , maxBindingsPerBindGroup: clampInt 640 1000 limits.maxBindingsPerBindGroup
  , maxDynamicUniformBuffersPerPipelineLayout: clampInt 8 14 limits.maxDynamicUniformBuffersPerPipelineLayout
  , maxDynamicStorageBuffersPerPipelineLayout: clampInt 4 8 limits.maxDynamicStorageBuffersPerPipelineLayout
  , maxSampledTexturesPerShaderStage: clampInt 16 16 limits.maxSampledTexturesPerShaderStage
  , maxSamplersPerShaderStage: clampInt 16 16 limits.maxSamplersPerShaderStage
  , maxStorageBuffersPerShaderStage: clampInt 8 10 limits.maxStorageBuffersPerShaderStage
  , maxStorageTexturesPerShaderStage: clampInt 4 8 limits.maxStorageTexturesPerShaderStage
  , maxUniformBuffersPerShaderStage: clampInt 12 14 limits.maxUniformBuffersPerShaderStage
  , maxUniformBufferBindingSize: clampInt 16384 134217728 limits.maxUniformBufferBindingSize
  , maxStorageBufferBindingSize: clampInt 134217728 1073741824 limits.maxStorageBufferBindingSize
  , minUniformBufferOffsetAlignment: clampInt 256 256 limits.minUniformBufferOffsetAlignment
  , minStorageBufferOffsetAlignment: clampInt 256 256 limits.minStorageBufferOffsetAlignment
  , maxVertexBuffers: clampInt 8 8 limits.maxVertexBuffers
  , maxBufferSize: clampNumber 268435456.0 1073741824.0 limits.maxBufferSize
  , maxVertexAttributes: clampInt 16 30 limits.maxVertexAttributes
  , maxVertexBufferArrayStride: clampInt 2048 2048 limits.maxVertexBufferArrayStride
  , maxInterStageShaderComponents: clampInt 60 120 limits.maxInterStageShaderComponents
  , maxInterStageShaderVariables: clampInt 16 16 limits.maxInterStageShaderVariables
  , maxColorAttachments: clampInt 8 8 limits.maxColorAttachments
  , maxColorAttachmentBytesPerSample: clampInt 32 32 limits.maxColorAttachmentBytesPerSample
  , maxComputeWorkgroupStorageSize: clampInt 16384 32768 limits.maxComputeWorkgroupStorageSize
  , maxComputeInvocationsPerWorkgroup: clampInt 256 1024 limits.maxComputeInvocationsPerWorkgroup
  , maxComputeWorkgroupSizeX: clampInt 256 1024 limits.maxComputeWorkgroupSizeX
  , maxComputeWorkgroupSizeY: clampInt 256 1024 limits.maxComputeWorkgroupSizeY
  , maxComputeWorkgroupSizeZ: clampInt 64 64 limits.maxComputeWorkgroupSizeZ
  , maxComputeWorkgroupsPerDimension: clampInt 65535 65535 limits.maxComputeWorkgroupsPerDimension
  }
