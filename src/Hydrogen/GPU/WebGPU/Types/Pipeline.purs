-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // webgpu // types // pipeline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- GPU pipeline types for WebGPU.
-- Pipelines define the full rendering or compute configuration.
--
-- This module includes:
-- - Vertex state
-- - Primitive state
-- - Fragment state
-- - Depth/stencil state
-- - Multisample state
-- - Pipeline descriptors
-- - Bind group types
--
-- Reference: WebGPU Specification
-- https://www.w3.org/TR/webgpu/
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Types.Pipeline
  ( -- Vertex State
    GPUVertexState
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
    -- Primitive State
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
    -- Fragment State
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
    -- Depth/Stencil State
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
    -- Multisample State
  , GPUMultisampleState
    -- Pipeline
  , GPURenderPipelineDescriptor
  , GPUComputePipelineDescriptor
  , GPUPipelineLayoutDescriptor
    -- Bind Group
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
  ) where

import Prelude

import Data.Foldable (foldr)
import Data.Maybe (Maybe)

import Hydrogen.GPU.WebGPU.Types.Sampler (GPUCompareFunction)
import Hydrogen.GPU.WebGPU.Types.Texture (GPUTextureFormat, GPUTextureViewDimension)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- VERTEX STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vertex shader state.
type GPUVertexState =
  { entryPoint :: String
  , buffers :: Array GPUVertexBufferLayout
  , constants :: Array { key :: String, value :: Number }
  }

-- | Vertex buffer layout.
type GPUVertexBufferLayout =
  { arrayStride :: Int
  , stepMode :: GPUVertexStepMode
  , attributes :: Array GPUVertexAttribute
  }

-- | Vertex attribute.
type GPUVertexAttribute =
  { format :: GPUVertexFormat
  , offset :: Int
  , shaderLocation :: Int
  }

-- | Vertex attribute formats.
data GPUVertexFormat
  = Uint8x2
  | Uint8x4
  | Sint8x2
  | Sint8x4
  | Unorm8x2
  | Unorm8x4
  | Snorm8x2
  | Snorm8x4
  | Uint16x2
  | Uint16x4
  | Sint16x2
  | Sint16x4
  | Unorm16x2
  | Unorm16x4
  | Snorm16x2
  | Snorm16x4
  | Float16x2
  | Float16x4
  | Float32
  | Float32x2
  | Float32x3
  | Float32x4
  | Uint32
  | Uint32x2
  | Uint32x3
  | Uint32x4
  | Sint32
  | Sint32x2
  | Sint32x3
  | Sint32x4

derive instance eqGPUVertexFormat :: Eq GPUVertexFormat
derive instance ordGPUVertexFormat :: Ord GPUVertexFormat

-- | Vertex step mode.
data GPUVertexStepMode
  = StepVertex
  | StepInstance

derive instance eqGPUVertexStepMode :: Eq GPUVertexStepMode
derive instance ordGPUVertexStepMode :: Ord GPUVertexStepMode

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PRIMITIVE STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Primitive assembly state.
type GPUPrimitiveState =
  { topology :: GPUPrimitiveTopology
  , stripIndexFormat :: Maybe GPUIndexFormat
  , frontFace :: GPUFrontFace
  , cullMode :: GPUCullMode
  , unclippedDepth :: Boolean
  }

-- | Primitive topology.
data GPUPrimitiveTopology
  = PointList
  | LineList
  | LineStrip
  | TriangleList
  | TriangleStrip

derive instance eqGPUPrimitiveTopology :: Eq GPUPrimitiveTopology
derive instance ordGPUPrimitiveTopology :: Ord GPUPrimitiveTopology

-- | Front face winding order.
data GPUFrontFace
  = FrontCCW
  | FrontCW

derive instance eqGPUFrontFace :: Eq GPUFrontFace
derive instance ordGPUFrontFace :: Ord GPUFrontFace

-- | Cull mode.
data GPUCullMode
  = CullNone
  | CullFront
  | CullBack

derive instance eqGPUCullMode :: Eq GPUCullMode
derive instance ordGPUCullMode :: Ord GPUCullMode

-- | Index format.
data GPUIndexFormat
  = IndexUint16
  | IndexUint32

derive instance eqGPUIndexFormat :: Eq GPUIndexFormat
derive instance ordGPUIndexFormat :: Ord GPUIndexFormat

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRAGMENT STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Fragment shader state.
type GPUFragmentState =
  { entryPoint :: String
  , targets :: Array GPUColorTargetState
  , constants :: Array { key :: String, value :: Number }
  }

-- | Color target state.
type GPUColorTargetState =
  { format :: GPUTextureFormat
  , blend :: Maybe GPUBlendState
  , writeMask :: Array GPUColorWriteMask
  }

-- | Blend state.
type GPUBlendState =
  { color :: GPUBlendComponent
  , alpha :: GPUBlendComponent
  }

-- | Blend component (color or alpha).
type GPUBlendComponent =
  { operation :: GPUBlendOperation
  , srcFactor :: GPUBlendFactor
  , dstFactor :: GPUBlendFactor
  }

-- | Blend factors.
data GPUBlendFactor
  = BlendZero
  | BlendOne
  | BlendSrc
  | BlendOneMinusSrc
  | BlendSrcAlpha
  | BlendOneMinusSrcAlpha
  | BlendDst
  | BlendOneMinusDst
  | BlendDstAlpha
  | BlendOneMinusDstAlpha
  | BlendSrcAlphaSaturated
  | BlendConstant
  | BlendOneMinusConstant

derive instance eqGPUBlendFactor :: Eq GPUBlendFactor
derive instance ordGPUBlendFactor :: Ord GPUBlendFactor

-- | Blend operations.
data GPUBlendOperation
  = BlendAdd
  | BlendSubtract
  | BlendReverseSubtract
  | BlendMin
  | BlendMax

derive instance eqGPUBlendOperation :: Eq GPUBlendOperation
derive instance ordGPUBlendOperation :: Ord GPUBlendOperation

-- | Color write mask flags.
data GPUColorWriteMask
  = WriteRed
  | WriteGreen
  | WriteBlue
  | WriteAlpha
  | WriteAll

derive instance eqGPUColorWriteMask :: Eq GPUColorWriteMask
derive instance ordGPUColorWriteMask :: Ord GPUColorWriteMask

-- | Combine color write masks into a bitmask.
combineColorWriteMask :: Array GPUColorWriteMask -> Int
combineColorWriteMask = foldr (\m acc -> acc + maskToInt m) 0
  where
  maskToInt :: GPUColorWriteMask -> Int
  maskToInt = case _ of
    WriteRed -> 1
    WriteGreen -> 2
    WriteBlue -> 4
    WriteAlpha -> 8
    WriteAll -> 15

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEPTH/STENCIL STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Depth/stencil state.
type GPUDepthStencilState =
  { format :: GPUTextureFormat
  , depthWriteEnabled :: Boolean
  , depthCompare :: GPUCompareFunction
  , stencilFront :: GPUStencilFaceState
  , stencilBack :: GPUStencilFaceState
  , stencilReadMask :: Int
  , stencilWriteMask :: Int
  , depthBias :: Int
  , depthBiasSlopeScale :: Number
  , depthBiasClamp :: Number
  }

-- | Stencil face state.
type GPUStencilFaceState =
  { compare :: GPUCompareFunction
  , failOp :: GPUStencilOperation
  , depthFailOp :: GPUStencilOperation
  , passOp :: GPUStencilOperation
  }

-- | Stencil operations.
data GPUStencilOperation
  = StencilKeep
  | StencilZero
  | StencilReplace
  | StencilInvert
  | StencilIncrementClamp
  | StencilDecrementClamp
  | StencilIncrementWrap
  | StencilDecrementWrap

derive instance eqGPUStencilOperation :: Eq GPUStencilOperation
derive instance ordGPUStencilOperation :: Ord GPUStencilOperation

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- MULTISAMPLE STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Multisample state.
type GPUMultisampleState =
  { count :: Int
  , mask :: Int
  , alphaToCoverageEnabled :: Boolean
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- PIPELINE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render pipeline descriptor.
type GPURenderPipelineDescriptor =
  { vertex :: GPUVertexState
  , primitive :: GPUPrimitiveState
  , depthStencil :: Maybe GPUDepthStencilState
  , multisample :: GPUMultisampleState
  , fragment :: Maybe GPUFragmentState
  , label :: Maybe String
  }

-- | Compute pipeline descriptor.
type GPUComputePipelineDescriptor =
  { compute ::
      { entryPoint :: String
      , constants :: Array { key :: String, value :: Number }
      }
  , label :: Maybe String
  }

-- | Pipeline layout descriptor.
type GPUPipelineLayoutDescriptor =
  { bindGroupLayouts :: Array GPUBindGroupLayoutDescriptor
  , label :: Maybe String
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- BIND GROUP
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Bind group layout descriptor.
type GPUBindGroupLayoutDescriptor =
  { entries :: Array GPUBindGroupLayoutEntry
  , label :: Maybe String
  }

-- | Bind group layout entry.
type GPUBindGroupLayoutEntry =
  { binding :: Int
  , visibility :: Array GPUShaderStage
  , buffer :: Maybe { type :: GPUBufferBindingType, hasDynamicOffset :: Boolean, minBindingSize :: Int }
  , sampler :: Maybe { type :: GPUSamplerBindingType }
  , texture :: Maybe { sampleType :: GPUTextureSampleType, viewDimension :: GPUTextureViewDimension, multisampled :: Boolean }
  , storageTexture :: Maybe { access :: GPUStorageTextureAccess, format :: GPUTextureFormat, viewDimension :: GPUTextureViewDimension }
  }

-- | Bind group descriptor.
type GPUBindGroupDescriptor =
  { entries :: Array GPUBindGroupEntry
  , label :: Maybe String
  }

-- | Bind group entry (references actual resources).
type GPUBindGroupEntry =
  { binding :: Int
  , resourceType :: BindGroupResourceType
  }

-- | Resource type for bind group entry.
data BindGroupResourceType
  = BufferResource { offset :: Int, size :: Int }
  | SamplerResource
  | TextureViewResource

derive instance eqBindGroupResourceType :: Eq BindGroupResourceType

-- | Buffer binding type.
data GPUBufferBindingType
  = BufferUniform
  | BufferStorage
  | BufferReadOnlyStorage

derive instance eqGPUBufferBindingType :: Eq GPUBufferBindingType
derive instance ordGPUBufferBindingType :: Ord GPUBufferBindingType

-- | Sampler binding type.
data GPUSamplerBindingType
  = SamplerFiltering
  | SamplerNonFiltering
  | SamplerComparison

derive instance eqGPUSamplerBindingType :: Eq GPUSamplerBindingType
derive instance ordGPUSamplerBindingType :: Ord GPUSamplerBindingType

-- | Texture sample type.
data GPUTextureSampleType
  = SampleFloat
  | SampleUnfilterableFloat
  | SampleDepth
  | SampleSint
  | SampleUint

derive instance eqGPUTextureSampleType :: Eq GPUTextureSampleType
derive instance ordGPUTextureSampleType :: Ord GPUTextureSampleType

-- | Storage texture access.
data GPUStorageTextureAccess
  = StorageWriteOnly
  | StorageReadOnly
  | StorageReadWrite

derive instance eqGPUStorageTextureAccess :: Eq GPUStorageTextureAccess
derive instance ordGPUStorageTextureAccess :: Ord GPUStorageTextureAccess

-- | Shader stage visibility.
data GPUShaderStage
  = StageVertex
  | StageFragment
  | StageCompute

derive instance eqGPUShaderStage :: Eq GPUShaderStage
derive instance ordGPUShaderStage :: Ord GPUShaderStage

-- | Combine shader stages into a bitmask.
combineShaderStage :: Array GPUShaderStage -> Int
combineShaderStage = foldr (\s acc -> acc + stageToInt s) 0
  where
  stageToInt :: GPUShaderStage -> Int
  stageToInt = case _ of
    StageVertex -> 1
    StageFragment -> 2
    StageCompute -> 4
