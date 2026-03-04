-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // gpu // limits
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Device Limits — Rollup module re-exporting all bounded limit types.
-- |
-- | ## Security Model
-- |
-- | An agent operating in a potentially malicious world model could receive:
-- |
-- | - `maxBufferSize: Infinity` → Memory exhaustion attack
-- | - `maxTextureDimension2D: -1` → Invalid state
-- | - `maxBindGroups: 999999999` → Unrealistic claim
-- |
-- | Bounded types clamp these to realistic WebGPU hardware limits.
-- |
-- | ## Presburger Decidability
-- |
-- | All limits are bounded integers. Resource constraint satisfaction
-- | is decidable via linear arithmetic:
-- |
-- | - "Does this buffer fit?" → `bufferSize ≤ maxBufferSize`
-- | - "Can we bind this many textures?" → `textureCount ≤ maxSampledTexturesPerShaderStage`
-- |
-- | ## Module Organization
-- |
-- | - Texture: TextureDimension1D/2D/3D, TextureArrayLayers
-- | - Binding: BindGroupCount, BindingsPerGroup
-- | - Buffer: BufferSize, BufferOffset, UniformBufferBindingSize, StorageBufferBindingSize
-- | - Vertex: VertexBufferCount, VertexAttributeCount, VertexBufferStride
-- | - Compute: WorkgroupSize, WorkgroupCount, WorkgroupStorageSize, ColorAttachmentCount
-- | - Feature: GPUFeature, PowerPreference, DeviceLimits
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits

module Hydrogen.Schema.GPU.Limits
  ( -- * Re-exports from Texture
    module Hydrogen.Schema.GPU.Limits.Texture
    
  -- * Re-exports from Binding
  , module Hydrogen.Schema.GPU.Limits.Binding
  
  -- * Re-exports from Buffer
  , module Hydrogen.Schema.GPU.Limits.Buffer
  
  -- * Re-exports from Vertex
  , module Hydrogen.Schema.GPU.Limits.Vertex
  
  -- * Re-exports from Compute
  , module Hydrogen.Schema.GPU.Limits.Compute
  
  -- * Re-exports from Feature
  , module Hydrogen.Schema.GPU.Limits.Feature
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.GPU.Limits.Texture
  ( TextureDimension1D
  , textureDimension1D
  , clampTextureDimension1D
  , unwrapTextureDimension1D
  , textureDimension1DBounds
  , TextureDimension2D
  , textureDimension2D
  , clampTextureDimension2D
  , unwrapTextureDimension2D
  , textureDimension2DBounds
  , TextureDimension3D
  , textureDimension3D
  , clampTextureDimension3D
  , unwrapTextureDimension3D
  , textureDimension3DBounds
  , TextureArrayLayers
  , textureArrayLayers
  , clampTextureArrayLayers
  , unwrapTextureArrayLayers
  , textureArrayLayersBounds
  )

import Hydrogen.Schema.GPU.Limits.Binding
  ( BindGroupCount
  , bindGroupCount
  , clampBindGroupCount
  , unwrapBindGroupCount
  , bindGroupCountBounds
  , BindingsPerGroup
  , bindingsPerGroup
  , clampBindingsPerGroup
  , unwrapBindingsPerGroup
  , bindingsPerGroupBounds
  )

import Hydrogen.Schema.GPU.Limits.Buffer
  ( BufferSize
  , bufferSize
  , clampBufferSize
  , unwrapBufferSize
  , bufferSizeBounds
  , bufferSizeZero
  , bufferSizeKB
  , bufferSizeMB
  , BufferOffset
  , bufferOffset
  , clampBufferOffset
  , unwrapBufferOffset
  , bufferOffsetBounds
  , UniformBufferBindingSize
  , uniformBufferBindingSize
  , clampUniformBufferBindingSize
  , unwrapUniformBufferBindingSize
  , uniformBufferBindingSizeBounds
  , StorageBufferBindingSize
  , storageBufferBindingSize
  , clampStorageBufferBindingSize
  , unwrapStorageBufferBindingSize
  , storageBufferBindingSizeBounds
  )

import Hydrogen.Schema.GPU.Limits.Vertex
  ( VertexBufferCount
  , vertexBufferCount
  , clampVertexBufferCount
  , unwrapVertexBufferCount
  , vertexBufferCountBounds
  , VertexAttributeCount
  , vertexAttributeCount
  , clampVertexAttributeCount
  , unwrapVertexAttributeCount
  , vertexAttributeCountBounds
  , VertexBufferStride
  , vertexBufferStride
  , clampVertexBufferStride
  , unwrapVertexBufferStride
  , vertexBufferStrideBounds
  )

import Hydrogen.Schema.GPU.Limits.Compute
  ( WorkgroupSize
  , workgroupSize
  , clampWorkgroupSize
  , unwrapWorkgroupSize
  , workgroupSizeBounds
  , WorkgroupCount
  , workgroupCount
  , clampWorkgroupCount
  , unwrapWorkgroupCount
  , workgroupCountBounds
  , WorkgroupStorageSize
  , workgroupStorageSize
  , clampWorkgroupStorageSize
  , unwrapWorkgroupStorageSize
  , workgroupStorageSizeBounds
  , ColorAttachmentCount
  , colorAttachmentCount
  , clampColorAttachmentCount
  , unwrapColorAttachmentCount
  , colorAttachmentCountBounds
  )

import Hydrogen.Schema.GPU.Limits.Feature
  ( GPUFeature
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
  , PowerPreference(LowPower, HighPerformance, NoPreference)
  , powerPreferenceToString
  , DeviceLimits
  , defaultLimits
  , minGuaranteedLimits
  , limitsTextureDimension2D
  , limitsMaxBufferSize
  , limitsMaxBindGroups
  , limitsMaxComputeWorkgroupsPerDimension
  )
