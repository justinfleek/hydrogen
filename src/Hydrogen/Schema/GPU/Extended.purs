-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // gpu // extended
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Schema Extended — Handle, Command, and Diffusion types.
-- |
-- | ## Contents
-- |
-- | This module re-exports extended GPU schema types:
-- |
-- | - **Handle**: Typed references to GPU resources (BufferHandle, TextureHandle, etc.)
-- | - **Command**: Pure ADT representing GPU operations (GPUCommand)
-- | - **Diffusion**: res4lyf compatible types (SchedulerType, NoiseType, etc.)
-- |
-- | ## Separation from Core
-- |
-- | The core module (Hydrogen.Schema.GPU) contains:
-- | - Limits (bounded dimension/buffer/compute types)
-- | - Effect (graded effects and co-effects)
-- | - Buffer, Texture, Sampler (descriptors)
-- |
-- | This extended module contains:
-- | - Handle (resource references)
-- | - Command (GPU operation ADT)
-- | - Diffusion (res4lyf types)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.GPU (BufferDescriptor, GPUEffect, BufferSize)
-- | import Hydrogen.Schema.GPU.Extended (BufferHandle, GPUCommand)
-- | ```

module Hydrogen.Schema.GPU.Extended
  ( -- * Re-exports from Handle
    module Hydrogen.Schema.GPU.Handle
    
  -- * Re-exports from Command
  , module Hydrogen.Schema.GPU.Command
  
  -- * Re-exports from Diffusion Types
  , module Hydrogen.GPU.Diffusion.Types
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

-- Resource handles
import Hydrogen.Schema.GPU.Handle
  ( HandleId
  , handleId
  , unwrapHandleId
  , BufferHandle
  , bufferHandle
  , bufferHandleId
  , TextureHandle
  , textureHandle
  , textureHandleId
  , TextureViewHandle
  , textureViewHandle
  , textureViewHandleId
  , SamplerHandle
  , samplerHandle
  , samplerHandleId
  , ShaderModuleHandle
  , shaderModuleHandle
  , shaderModuleHandleId
  , RenderPipelineHandle
  , renderPipelineHandle
  , renderPipelineHandleId
  , ComputePipelineHandle
  , computePipelineHandle
  , computePipelineHandleId
  , BindGroupHandle
  , bindGroupHandle
  , bindGroupHandleId
  , BindGroupLayoutHandle
  , bindGroupLayoutHandle
  , bindGroupLayoutHandleId
  , PipelineLayoutHandle
  , pipelineLayoutHandle
  , pipelineLayoutHandleId
  , CommandBufferHandle
  , commandBufferHandle
  , commandBufferHandleId
  , QuerySetHandle
  , querySetHandle
  , querySetHandleId
  , HandleCounter
  , initialHandleCounter
  , nextBufferHandle
  , nextTextureHandle
  , nextSamplerHandle
  , nextShaderModuleHandle
  , nextRenderPipelineHandle
  , nextComputePipelineHandle
  , nextBindGroupHandle
  , nextCommandBufferHandle
  )

-- GPU Commands
import Hydrogen.Schema.GPU.Command
  ( GPUCommand
      ( CmdCreateBuffer
      , CmdCreateTexture
      , CmdCreateTextureView
      , CmdCreateSampler
      , CmdCreateShaderModule
      , CmdCreateRenderPipeline
      , CmdCreateComputePipeline
      , CmdCreateBindGroup
      , CmdDestroyBuffer
      , CmdDestroyTexture
      , CmdWriteBuffer
      , CmdWriteTexture
      , CmdCopyBufferToBuffer
      , CmdCopyTextureToTexture
      , CmdBeginRenderPass
      , CmdEndRenderPass
      , CmdSetRenderPipeline
      , CmdSetBindGroup
      , CmdSetVertexBuffer
      , CmdSetIndexBuffer
      , CmdDraw
      , CmdDrawIndexed
      , CmdSetViewport
      , CmdSetScissorRect
      , CmdBeginComputePass
      , CmdEndComputePass
      , CmdSetComputePipeline
      , CmdDispatch
      , CmdSubmit
      )
  , commandEffect
  , commandCoEffect
  , RenderPassDescriptor
  , renderPassDescriptor
  , ColorAttachment
  , colorAttachment
  , DepthStencilAttachment
  , depthStencilAttachment
  , LoadOp(LoadOpClear, LoadOpLoad)
  , StoreOp(StoreOpStore, StoreOpDiscard)
  , DrawParams
  , drawParams
  , DrawIndexedParams
  , drawIndexedParams
  , DispatchParams
  , dispatchParams
  , Viewport
  , viewport
  , ScissorRect
  , scissorRect
  , IndexFormat(IndexUint16, IndexUint32)
  , indexFormatToString
  , BindGroupEntry
  , BindingResource(BindBuffer, BindTexture, BindSampler)
  , BindingCounts
  , countBindings
  , bindGroupCoEffect
  )

-- Diffusion types (res4lyf compatible)
import Hydrogen.GPU.Diffusion.Types
  ( SchedulerType
      ( SchedulerNormal
      , SchedulerKarras
      , SchedulerExponential
      , SchedulerSGMUniform
      , SchedulerSimple
      , SchedulerDDIMUniform
      , SchedulerBeta
      , SchedulerLinearQuadratic
      , SchedulerBeta57
      , SchedulerPolyExponential
      , SchedulerVPSDE
      , SchedulerLCMSD
      , SchedulerLCMSDXL
      , SchedulerAYS
      , SchedulerGITS
      , SchedulerConstant
      )
  , NoiseType
      ( NoiseGaussian
      , NoiseBrownian
      , NoiseUniform
      , NoiseLaplacian
      , NoiseStudentT
      , NoisePerlin
      , NoiseWavelet
      , NoiseFractalBrown
      , NoiseFractalPink
      , NoiseFractalWhite
      , NoiseFractalBlue
      , NoiseFractalViolet
      , NoisePyramidBilinear
      , NoisePyramidBicubic
      , NoisePyramidNearest
      , NoiseHiresPyramidBilinear
      , NoiseHiresPyramidBicubic
      , NoiseSimplex
      , NoiseNone
      )
  , NoiseMode
      ( NoiseModeNone
      , NoiseModeHard
      , NoiseModeLorentzian
      , NoiseModeSoft
      , NoiseModeSoftLinear
      , NoiseModeSofter
      , NoiseModeEpsilon
      , NoiseModeSinusoidal
      , NoiseModeExp
      , NoiseModeVPSDE
      , NoiseModeER4
      , NoiseModeHardVar
      )
  , GuideMode
      ( GuideModeFlow
      , GuideModeSync
      , GuideModeLure
      , GuideModeData
      , GuideModeEpsilon
      , GuideModeInversion
      , GuideModePseudoimplicit
      , GuideModeFullyPseudoimplicit
      , GuideModeNone
      )
  , ImplicitType
      ( ImplicitRebound
      , ImplicitRetroEta
      , ImplicitBongmath
      , ImplicitPredictorCorrector
      )
  , LatentTensor
  , LatentShape
  , TensorDtype
      ( DtypeFloat16
      , DtypeFloat32
      , DtypeBFloat16
      )
  , TensorDevice
      ( DeviceCPU
      , DeviceCUDA
      , DeviceWebGPU
      )
  , Conditioning
      ( ConditioningText
      , ConditioningImage
      , ConditioningComposite
      , ConditioningNone
      )
  , TextConditioning
  , ImageConditioning
  , ImageConditionType
      ( ConditionControlNet
      , ConditionIPAdapter
      , ConditionReference
      , ConditionT2IAdapter
      )
  , NoiseSchedule
  , SigmaSchedule
  , DiffusionBlendMode
      ( BlendLinear
      , BlendSoftmax
      , BlendMultiply
      , BlendFeathered
      )
  , StepStrategy
      ( StrategyStandard
      , StrategySubstep
      , StrategyAncestral
      , StrategySDE
      )
  , SubstepConfig
  , SubstepMethod
      ( SubstepEuler
      , SubstepHeun
      , SubstepRK4
      , SubstepDPMSolver
      )
  )
