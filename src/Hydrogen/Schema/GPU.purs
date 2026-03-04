-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // schema // gpu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Schema — Core bounded types for GPU resource management.
-- |
-- | ## Contents
-- |
-- | This module re-exports core GPU schema types:
-- |
-- | - **Limits**: Bounded types for WebGPU device limits
-- |   - Texture dimensions, array layers
-- |   - Buffer sizes, offsets
-- |   - Bind groups, bindings per group
-- |   - Vertex buffers, attributes, strides
-- |   - Workgroup sizes, counts, storage
-- |   - Device features, power preference
-- |
-- | - **Effect**: Graded effects and co-effects for GPU operations
-- |   - GPUEffect (what operations CAN DO)
-- |   - GPUCoEffect (what operations NEED)
-- |   - GPUOp primitives
-- |   - GPUExpr composable AST
-- |
-- | - **Buffer**: Buffer descriptors with bounded sizes and co-effects
-- |
-- | - **Texture**: Texture descriptors with bounded dimensions
-- |   - Texture formats (complete WebGPU coverage)
-- |   - Texture usage flags
-- |   - Memory calculation
-- |
-- | - **Sampler**: Sampler descriptors with bounded parameters
-- |
-- | ## Extended Module
-- |
-- | For additional types (Handle, Command, Diffusion), see:
-- | `Hydrogen.Schema.GPU.Extended`
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Every type in this module is bounded with explicit limits.
-- | Constraint satisfaction is decidable via Presburger arithmetic.
-- | Same type value = same UUID5 = deterministic at swarm scale.

module Hydrogen.Schema.GPU
  ( -- * Re-exports from Limits
    module Hydrogen.Schema.GPU.Limits
    
  -- * Re-exports from Effect
  , module Hydrogen.Schema.GPU.Effect
  
  -- * Re-exports from Buffer
  , module Hydrogen.Schema.GPU.Buffer
  
  -- * Re-exports from Texture
  , module Hydrogen.Schema.GPU.Texture
  
  -- * Re-exports from Sampler
  , module Hydrogen.Schema.GPU.Sampler
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Bounded limit types
import Hydrogen.Schema.GPU.Limits
  ( -- Texture dimensions
    TextureDimension1D
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
  -- Binding limits
  , BindGroupCount
  , bindGroupCount
  , clampBindGroupCount
  , unwrapBindGroupCount
  , bindGroupCountBounds
  , BindingsPerGroup
  , bindingsPerGroup
  , clampBindingsPerGroup
  , unwrapBindingsPerGroup
  , bindingsPerGroupBounds
  -- Buffer limits
  , BufferSize
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
  -- Vertex limits
  , VertexBufferCount
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
  -- Compute limits
  , WorkgroupSize
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
  -- Features
  , GPUFeature
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

-- Graded effects and co-effects
import Hydrogen.Schema.GPU.Effect
  ( nsGPU
  , GPUEffect
      ( EffectNone
      , EffectAllocateMemory
      , EffectFreeMemory
      , EffectBindResource
      , EffectDraw
      , EffectDispatchCompute
      , EffectCopyBuffer
      , EffectCopyTexture
      , EffectPresent
      , EffectComposite
      )
  , allGPUEffects
  , effectCombine
  , effectNone
  , GPUCoEffect
      ( CoEffectNone
      , CoEffectDevice
      , CoEffectMemory
      , CoEffectBandwidth
      , CoEffectBufferBinding
      , CoEffectTextureBinding
      , CoEffectSamplerBinding
      , CoEffectPipeline
      , CoEffectRenderTarget
      , CoEffectWorkgroups
      , CoEffectComposite
      )
  , allGPUCoEffects
  , coEffectCombine
  , coEffectNone
  , GPUOp
      ( OpCreateBuffer
      , OpDestroyBuffer
      , OpWriteBuffer
      , OpReadBuffer
      , OpCreateTexture
      , OpDestroyTexture
      , OpWriteTexture
      , OpCreateSampler
      , OpCreateShaderModule
      , OpCreatePipeline
      , OpCreateBindGroup
      , OpBeginRenderPass
      , OpEndRenderPass
      , OpSetPipeline
      , OpSetBindGroup
      , OpSetVertexBuffer
      , OpSetIndexBuffer
      , OpDraw
      , OpDrawIndexed
      , OpDispatchCompute
      , OpCopyBufferToBuffer
      , OpCopyTextureToTexture
      , OpSubmit
      , OpPresent
      )
  , allGPUOps
  , gpuOpEffect
  , gpuOpCoEffect
  , GPUExpr
      ( GPUPure
      , GPUOp
      , GPUSeq
      , GPUPar
      , GPULoop
      , GPUConditional
      )
  , exprEffect
  , exprCoEffect
  , exprUUID
  )

-- Buffer descriptors
import Hydrogen.Schema.GPU.Buffer
  ( BufferUsage
      ( UsageMapRead
      , UsageMapWrite
      , UsageCopySrc
      , UsageCopyDst
      , UsageIndex
      , UsageVertex
      , UsageUniform
      , UsageStorage
      , UsageIndirect
      , UsageQueryResolve
      )
  , allBufferUsages
  , usageToString
  , usageToBitmask
  , usageSetToBitmask
  , hasUsage
  , addUsage
  , removeUsage
  , MapMode(MapModeRead, MapModeWrite)
  , mapModeToBitmask
  , combinedMapMode
  , BufferDescriptor
  , bufferDescriptor
  , bufferDescriptorValidated
  , descriptorSize
  , descriptorUsages
  , descriptorMappedAtCreation
  , descriptorLabel
  , descriptorWithLabel
  , descriptorWithUsage
  , bufferCoEffect
  , combineBufferCoEffects
  , totalBufferMemory
  , totalBufferCoEffect
  , vertexBufferDescriptor
  , indexBufferDescriptor
  , uniformBufferDescriptor
  , storageBufferDescriptor
  , stagingBufferDescriptor
  , readbackBufferDescriptor
  , validateDescriptor
  , hasMappingUsage
  , BufferValidationError
      ( ErrorSizeZero
      , ErrorNoUsages
      , ErrorInvalidMappingUsage
      )
  )

-- Texture descriptors and formats
import Hydrogen.Schema.GPU.Texture
  ( TextureFormat
      ( FormatR8Unorm
      , FormatR8Snorm
      , FormatR8Uint
      , FormatR8Sint
      , FormatR16Uint
      , FormatR16Sint
      , FormatR16Float
      , FormatRG8Unorm
      , FormatRG8Snorm
      , FormatRG8Uint
      , FormatRG8Sint
      , FormatR32Uint
      , FormatR32Sint
      , FormatR32Float
      , FormatRG16Uint
      , FormatRG16Sint
      , FormatRG16Float
      , FormatRGBA8Unorm
      , FormatRGBA8UnormSrgb
      , FormatRGBA8Snorm
      , FormatRGBA8Uint
      , FormatRGBA8Sint
      , FormatBGRA8Unorm
      , FormatBGRA8UnormSrgb
      , FormatRGB9E5Ufloat
      , FormatRGB10A2Uint
      , FormatRGB10A2Unorm
      , FormatRG11B10Ufloat
      , FormatRG32Uint
      , FormatRG32Sint
      , FormatRG32Float
      , FormatRGBA16Uint
      , FormatRGBA16Sint
      , FormatRGBA16Float
      , FormatRGBA32Uint
      , FormatRGBA32Sint
      , FormatRGBA32Float
      , FormatStencil8
      , FormatDepth16Unorm
      , FormatDepth24Plus
      , FormatDepth24PlusStencil8
      , FormatDepth32Float
      , FormatDepth32FloatStencil8
      )
  , textureFormatToString
  , textureFormatFromString
  , textureFormatBytesPerPixel
  , isDepthFormat
  , isStencilFormat
  , isCompressedFormat
  , isSrgbFormat
  , isFloatFormat
  , TextureDimensionType
      ( Texture1D
      , Texture2D
      , Texture3D
      )
  , dimensionTypeToString
  , TextureUsage
      ( TextureUsageCopySrc
      , TextureUsageCopyDst
      , TextureUsageTextureBinding
      , TextureUsageStorageBinding
      , TextureUsageRenderAttachment
      )
  , allTextureUsages
  , textureUsageToString
  , textureUsageToBitmask
  , textureUsageSetToBitmask
  , TextureSize2D
  , textureSize2D
  , textureSizeWidth
  , textureSizeHeight
  , TextureSize3D
  , textureSize3D
  , textureSize3DWidth
  , textureSize3DHeight
  , textureSize3DDepth
  , TextureDescriptor2D
  , textureDescriptor2D
  , textureMemoryBytes
  )

-- Sampler descriptors
import Hydrogen.Schema.GPU.Sampler
  ( AddressMode
      ( AddressClampToEdge
      , AddressRepeat
      , AddressMirrorRepeat
      )
  , addressModeToString
  , FilterMode
      ( FilterNearest
      , FilterLinear
      )
  , filterModeToString
  , MipmapFilterMode
      ( MipmapFilterNearest
      , MipmapFilterLinear
      )
  , mipmapFilterModeToString
  , CompareFunction
      ( CompareNever
      , CompareLess
      , CompareEqual
      , CompareLessEqual
      , CompareGreater
      , CompareNotEqual
      , CompareGreaterEqual
      , CompareAlways
      )
  , compareFunctionToString
  , MaxAnisotropy
  , maxAnisotropy
  , clampMaxAnisotropy
  , unwrapMaxAnisotropy
  , anisotropyBounds
  , LodClamp
  , lodClamp
  , clampLodClamp
  , unwrapLodClamp
  , SamplerDescriptor
  , samplerDescriptor
  , defaultSamplerDescriptor
  , linearSamplerDescriptor
  , nearestSamplerDescriptor
  , shadowSamplerDescriptor
  )


