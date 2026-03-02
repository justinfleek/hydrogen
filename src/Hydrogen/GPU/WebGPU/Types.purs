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

import Hydrogen.GPU.WebGPU.Types.Buffer
  ( GPUBufferDescriptor
  , GPUBufferUsage
      ( MapRead
      , MapWrite
      , CopySrc
      , CopyDst
      , Index
      , Vertex
      , Uniform
      , Storage
      , Indirect
      , QueryResolve
      )
  , GPUMapMode
      ( MapModeRead
      , MapModeWrite
      )
  , combineBufferUsage
  , combineMapMode
  ) as Buffer

import Hydrogen.GPU.WebGPU.Types.Texture
  ( GPUTextureDescriptor
  , GPUTextureFormat
      ( R8Unorm
      , R8Snorm
      , R8Uint
      , R8Sint
      , R16Uint
      , R16Sint
      , R16Float
      , RG8Unorm
      , RG8Snorm
      , RG8Uint
      , RG8Sint
      , R32Uint
      , R32Sint
      , R32Float
      , RG16Uint
      , RG16Sint
      , RG16Float
      , RGBA8Unorm
      , RGBA8UnormSrgb
      , RGBA8Snorm
      , RGBA8Uint
      , RGBA8Sint
      , BGRA8Unorm
      , BGRA8UnormSrgb
      , RGB9E5Ufloat
      , RGB10A2Uint
      , RGB10A2Unorm
      , RG11B10Ufloat
      , RG32Uint
      , RG32Sint
      , RG32Float
      , RGBA16Uint
      , RGBA16Sint
      , RGBA16Float
      , RGBA32Uint
      , RGBA32Sint
      , RGBA32Float
      , Stencil8
      , Depth16Unorm
      , Depth24Plus
      , Depth24PlusStencil8
      , Depth32Float
      , Depth32FloatStencil8
      )
  , GPUTextureUsage
      ( TextureCopySrc
      , TextureCopyDst
      , TextureBinding
      , StorageBinding
      , RenderAttachment
      )
  , GPUTextureDimension
      ( Dimension1D
      , Dimension2D
      , Dimension3D
      )
  , GPUTextureViewDescriptor
  , GPUTextureViewDimension
      ( View1D
      , View2D
      , View2DArray
      , ViewCube
      , ViewCubeArray
      , View3D
      )
  , GPUTextureAspect
      ( AspectAll
      , AspectStencilOnly
      , AspectDepthOnly
      )
  , combineTextureUsage
  ) as Texture

import Hydrogen.GPU.WebGPU.Types.Sampler
  ( GPUSamplerDescriptor
  , GPUAddressMode
      ( ClampToEdge
      , Repeat
      , MirrorRepeat
      )
  , GPUFilterMode
      ( FilterNearest
      , FilterLinear
      )
  , GPUMipmapFilterMode
      ( MipmapNearest
      , MipmapLinear
      )
  , GPUCompareFunction
      ( CompareNever
      , CompareLess
      , CompareEqual
      , CompareLessEqual
      , CompareGreater
      , CompareNotEqual
      , CompareGreaterEqual
      , CompareAlways
      )
  ) as Sampler

import Hydrogen.GPU.WebGPU.Types.Shader
  ( GPUShaderModuleDescriptor
  , WGSLSource(WGSLSource)
  ) as Shader

import Hydrogen.GPU.WebGPU.Types.Pipeline
  ( GPUVertexState
  , GPUVertexBufferLayout
  , GPUVertexAttribute
  , GPUVertexFormat
      ( Uint8x2
      , Uint8x4
      , Sint8x2
      , Sint8x4
      , Unorm8x2
      , Unorm8x4
      , Snorm8x2
      , Snorm8x4
      , Uint16x2
      , Uint16x4
      , Sint16x2
      , Sint16x4
      , Unorm16x2
      , Unorm16x4
      , Snorm16x2
      , Snorm16x4
      , Float16x2
      , Float16x4
      , Float32
      , Float32x2
      , Float32x3
      , Float32x4
      , Uint32
      , Uint32x2
      , Uint32x3
      , Uint32x4
      , Sint32
      , Sint32x2
      , Sint32x3
      , Sint32x4
      )
  , GPUVertexStepMode
      ( StepVertex
      , StepInstance
      )
  , GPUPrimitiveState
  , GPUPrimitiveTopology
      ( PointList
      , LineList
      , LineStrip
      , TriangleList
      , TriangleStrip
      )
  , GPUCullMode
      ( CullNone
      , CullFront
      , CullBack
      )
  , GPUFrontFace
      ( FrontCCW
      , FrontCW
      )
  , GPUIndexFormat
      ( IndexUint16
      , IndexUint32
      )
  , GPUFragmentState
  , GPUColorTargetState
  , GPUBlendState
  , GPUBlendComponent
  , GPUBlendFactor
      ( BlendZero
      , BlendOne
      , BlendSrc
      , BlendOneMinusSrc
      , BlendSrcAlpha
      , BlendOneMinusSrcAlpha
      , BlendDst
      , BlendOneMinusDst
      , BlendDstAlpha
      , BlendOneMinusDstAlpha
      , BlendSrcAlphaSaturated
      , BlendConstant
      , BlendOneMinusConstant
      )
  , GPUBlendOperation
      ( BlendAdd
      , BlendSubtract
      , BlendReverseSubtract
      , BlendMin
      , BlendMax
      )
  , GPUColorWriteMask
      ( WriteRed
      , WriteGreen
      , WriteBlue
      , WriteAlpha
      , WriteAll
      )
  , combineColorWriteMask
  , GPUDepthStencilState
  , GPUStencilFaceState
  , GPUStencilOperation
      ( StencilKeep
      , StencilZero
      , StencilReplace
      , StencilInvert
      , StencilIncrementClamp
      , StencilDecrementClamp
      , StencilIncrementWrap
      , StencilDecrementWrap
      )
  , GPUMultisampleState
  , GPURenderPipelineDescriptor
  , GPUComputePipelineDescriptor
  , GPUPipelineLayoutDescriptor
  , GPUBindGroupLayoutDescriptor
  , GPUBindGroupLayoutEntry
  , GPUBindGroupDescriptor
  , GPUBindGroupEntry
  , BindGroupResourceType
      ( BufferResource
      , SamplerResource
      , TextureViewResource
      )
  , GPUBufferBindingType
      ( BufferUniform
      , BufferStorage
      , BufferReadOnlyStorage
      )
  , GPUSamplerBindingType
      ( SamplerFiltering
      , SamplerNonFiltering
      , SamplerComparison
      )
  , GPUTextureSampleType
      ( SampleFloat
      , SampleUnfilterableFloat
      , SampleDepth
      , SampleSint
      , SampleUint
      )
  , GPUStorageTextureAccess
      ( StorageWriteOnly
      , StorageReadOnly
      , StorageReadWrite
      )
  , GPUShaderStage
      ( StageVertex
      , StageFragment
      , StageCompute
      )
  , combineShaderStage
  ) as Pipeline

import Hydrogen.GPU.WebGPU.Types.RenderPass
  ( GPURenderPassDescriptor
  , GPURenderPassColorAttachment
  , GPURenderPassDepthStencilAttachment
  , GPULoadOp
      ( LoadOpLoad
      , LoadOpClear
      )
  , GPUStoreOp
      ( StoreOpStore
      , StoreOpDiscard
      )
  , GPUCanvasConfiguration
  , GPUCanvasAlphaMode
      ( AlphaOpaque
      , AlphaPremultiplied
      )
  ) as RenderPass
