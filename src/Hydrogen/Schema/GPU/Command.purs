-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // gpu // command
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Commands — Pure ADT representing GPU operations.
-- |
-- | ## Design Philosophy
-- |
-- | GPU commands are PURE DATA describing what operations to perform.
-- | The runtime interprets these commands against actual WebGPU.
-- |
-- | This separation enables:
-- | - Deterministic command composition without FFI
-- | - Lean4 verification of command sequences
-- | - Graded effect/co-effect tracking
-- | - Command optimization (batching, reordering)
-- |
-- | ## Command Categories
-- |
-- | 1. **Resource Creation**: CreateBuffer, CreateTexture, CreateSampler, etc.
-- | 2. **Resource Destruction**: DestroyBuffer, DestroyTexture
-- | 3. **Data Transfer**: WriteBuffer, WriteTexture, CopyBufferToBuffer
-- | 4. **Rendering**: BeginRenderPass, SetPipeline, Draw, EndRenderPass
-- | 5. **Compute**: BeginComputePass, Dispatch, EndComputePass
-- | 6. **Submission**: Submit command buffers to queue
-- |
-- | ## Co-Effect Semantics
-- |
-- | Each command declares its resource requirements:
-- | - CreateBuffer → CoEffectMemory (buffer size)
-- | - SetBindGroup → CoEffectBufferBinding + CoEffectTextureBinding
-- | - Dispatch → CoEffectWorkgroups
-- |
-- | Memory co-effects are ADDITIVE (sum).
-- | Workgroup co-effects use MAX (parallel capacity).
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.GPU.Handle
-- | - Hydrogen.Schema.GPU.Buffer
-- | - Hydrogen.Schema.GPU.Texture
-- | - Hydrogen.Schema.GPU.Sampler
-- | - Hydrogen.Schema.GPU.Effect

module Hydrogen.Schema.GPU.Command
  ( -- * GPU Command ADT
    GPUCommand
      ( -- Resource Creation
        CmdCreateBuffer
      , CmdCreateTexture
      , CmdCreateTextureView
      , CmdCreateSampler
      , CmdCreateShaderModule
      , CmdCreateRenderPipeline
      , CmdCreateComputePipeline
      , CmdCreateBindGroup
        -- Resource Destruction
      , CmdDestroyBuffer
      , CmdDestroyTexture
        -- Data Transfer
      , CmdWriteBuffer
      , CmdWriteTexture
      , CmdCopyBufferToBuffer
      , CmdCopyTextureToTexture
        -- Render Pass
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
        -- Compute Pass
      , CmdBeginComputePass
      , CmdEndComputePass
      , CmdSetComputePipeline
      , CmdDispatch
        -- Submission
      , CmdSubmit
      )
  
  -- * Command Effect/Co-Effect
  , commandEffect
  , commandCoEffect
  
  -- * Render Pass Descriptor
  , RenderPassDescriptor
  , renderPassDescriptor
  , ColorAttachment
  , colorAttachment
  , DepthStencilAttachment
  , depthStencilAttachment
  , LoadOp(LoadOpClear, LoadOpLoad)
  , StoreOp(StoreOpStore, StoreOpDiscard)
  
  -- * Draw Parameters
  , DrawParams
  , drawParams
  , DrawIndexedParams
  , drawIndexedParams
  
  -- * Dispatch Parameters
  , DispatchParams
  , dispatchParams
  
  -- * Viewport/Scissor
  , Viewport
  , viewport
  , ScissorRect
  , scissorRect
  
  -- * Index Format
  , IndexFormat(IndexUint16, IndexUint32)
  , indexFormatToString
  
  -- * Bind Group Types
  , BindGroupEntry
  , BindingResource(BindBuffer, BindTexture, BindSampler)
  , BindingCounts
  , countBindings
  , bindGroupCoEffect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (*)
  , (>)
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.GPU.Handle
  ( BufferHandle
  , TextureHandle
  , TextureViewHandle
  , SamplerHandle
  , ShaderModuleHandle
  , RenderPipelineHandle
  , ComputePipelineHandle
  , BindGroupHandle
  , CommandBufferHandle
  )

import Hydrogen.Schema.GPU.Buffer
  ( BufferDescriptor
  , totalBufferMemory
  )

import Hydrogen.Schema.GPU.Texture
  ( TextureDescriptor2D
  , textureMemoryBytes
  )

import Hydrogen.Schema.GPU.Sampler
  ( SamplerDescriptor
  )

import Hydrogen.Schema.GPU.Limits.Buffer
  ( BufferSize
  , BufferOffset
  , unwrapBufferSize
  , unwrapBufferOffset
  )

import Hydrogen.Schema.GPU.Limits.Compute
  ( WorkgroupCount
  , unwrapWorkgroupCount
  )

import Hydrogen.Schema.GPU.Effect
  ( GPUEffect
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
  , GPUCoEffect
      ( CoEffectNone
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
  , coEffectCombine
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // load/store ops
-- ═════════════════════════════════════════════════════════════════════════════

-- | Load operation for render pass attachments.
data LoadOp
  = LoadOpClear
    -- ^ Clear the attachment to a specified value
  | LoadOpLoad
    -- ^ Load existing contents

derive instance eqLoadOp :: Eq LoadOp
derive instance ordLoadOp :: Ord LoadOp

instance showLoadOp :: Show LoadOp where
  show LoadOpClear = "clear"
  show LoadOpLoad = "load"

-- | Store operation for render pass attachments.
data StoreOp
  = StoreOpStore
    -- ^ Store the results
  | StoreOpDiscard
    -- ^ Discard the results (optimization for transient attachments)

derive instance eqStoreOp :: Eq StoreOp
derive instance ordStoreOp :: Ord StoreOp

instance showStoreOp :: Show StoreOp where
  show StoreOpStore = "store"
  show StoreOpDiscard = "discard"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // index format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index buffer format.
data IndexFormat
  = IndexUint16
    -- ^ 16-bit unsigned indices (max 65535 vertices)
  | IndexUint32
    -- ^ 32-bit unsigned indices (max ~4 billion vertices)

derive instance eqIndexFormat :: Eq IndexFormat
derive instance ordIndexFormat :: Ord IndexFormat

instance showIndexFormat :: Show IndexFormat where
  show = indexFormatToString

-- | Convert index format to WebGPU string.
indexFormatToString :: IndexFormat -> String
indexFormatToString IndexUint16 = "uint16"
indexFormatToString IndexUint32 = "uint32"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // color attachment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color attachment for render pass.
type ColorAttachment =
  { view :: TextureViewHandle
  , resolveTarget :: Maybe TextureViewHandle
  , loadOp :: LoadOp
  , storeOp :: StoreOp
  , clearValue :: { r :: Number, g :: Number, b :: Number, a :: Number }
  }

-- | Create a color attachment.
colorAttachment
  :: TextureViewHandle
  -> LoadOp
  -> StoreOp
  -> { r :: Number, g :: Number, b :: Number, a :: Number }
  -> ColorAttachment
colorAttachment view loadOp storeOp clearValue =
  { view: view
  , resolveTarget: Nothing
  , loadOp: loadOp
  , storeOp: storeOp
  , clearValue: clearValue
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // depth stencil attachment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Depth/stencil attachment for render pass.
type DepthStencilAttachment =
  { view :: TextureViewHandle
  , depthLoadOp :: LoadOp
  , depthStoreOp :: StoreOp
  , depthClearValue :: Number
  , stencilLoadOp :: LoadOp
  , stencilStoreOp :: StoreOp
  , stencilClearValue :: Int
  }

-- | Create a depth/stencil attachment.
depthStencilAttachment
  :: TextureViewHandle
  -> Number
  -> DepthStencilAttachment
depthStencilAttachment view depthClear =
  { view: view
  , depthLoadOp: LoadOpClear
  , depthStoreOp: StoreOpStore
  , depthClearValue: depthClear
  , stencilLoadOp: LoadOpClear
  , stencilStoreOp: StoreOpStore
  , stencilClearValue: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // render pass descriptor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render pass descriptor.
type RenderPassDescriptor =
  { colorAttachments :: Array ColorAttachment
  , depthStencilAttachment :: Maybe DepthStencilAttachment
  , label :: Maybe String
  }

-- | Create a render pass descriptor.
renderPassDescriptor
  :: Array ColorAttachment
  -> Maybe DepthStencilAttachment
  -> Maybe String
  -> RenderPassDescriptor
renderPassDescriptor colors depth label =
  { colorAttachments: colors
  , depthStencilAttachment: depth
  , label: label
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // draw params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameters for a draw call.
type DrawParams =
  { vertexCount :: Int
  , instanceCount :: Int
  , firstVertex :: Int
  , firstInstance :: Int
  }

-- | Create draw parameters.
drawParams :: Int -> Int -> DrawParams
drawParams vertexCount instanceCount =
  { vertexCount: vertexCount
  , instanceCount: instanceCount
  , firstVertex: 0
  , firstInstance: 0
  }

-- | Parameters for an indexed draw call.
type DrawIndexedParams =
  { indexCount :: Int
  , instanceCount :: Int
  , firstIndex :: Int
  , baseVertex :: Int
  , firstInstance :: Int
  }

-- | Create indexed draw parameters.
drawIndexedParams :: Int -> Int -> DrawIndexedParams
drawIndexedParams indexCount instanceCount =
  { indexCount: indexCount
  , instanceCount: instanceCount
  , firstIndex: 0
  , baseVertex: 0
  , firstInstance: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // dispatch params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parameters for a compute dispatch.
type DispatchParams =
  { workgroupCountX :: WorkgroupCount
  , workgroupCountY :: WorkgroupCount
  , workgroupCountZ :: WorkgroupCount
  }

-- | Create dispatch parameters.
dispatchParams
  :: WorkgroupCount
  -> WorkgroupCount
  -> WorkgroupCount
  -> DispatchParams
dispatchParams x y z =
  { workgroupCountX: x
  , workgroupCountY: y
  , workgroupCountZ: z
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // viewport / scissor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport specification.
type Viewport =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  , minDepth :: Number
  , maxDepth :: Number
  }

-- | Create a viewport.
viewport :: Number -> Number -> Number -> Number -> Viewport
viewport x y width height =
  { x: x
  , y: y
  , width: width
  , height: height
  , minDepth: 0.0
  , maxDepth: 1.0
  }

-- | Scissor rectangle specification.
type ScissorRect =
  { x :: Int
  , y :: Int
  , width :: Int
  , height :: Int
  }

-- | Create a scissor rectangle.
scissorRect :: Int -> Int -> Int -> Int -> ScissorRect
scissorRect x y width height =
  { x: x
  , y: y
  , width: width
  , height: height
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gpu command
-- ═════════════════════════════════════════════════════════════════════════════

-- | GPU Command ADT — Pure data describing GPU operations.
-- |
-- | Each command variant contains the information needed to execute
-- | the operation. The runtime interprets these against WebGPU.
data GPUCommand
  -- Resource Creation
  = CmdCreateBuffer BufferHandle BufferDescriptor
    -- ^ Create a buffer with the given descriptor
  | CmdCreateTexture TextureHandle TextureDescriptor2D
    -- ^ Create a texture with the given descriptor
  | CmdCreateTextureView TextureViewHandle TextureHandle
    -- ^ Create a view of a texture
  | CmdCreateSampler SamplerHandle SamplerDescriptor
    -- ^ Create a sampler with the given descriptor
  | CmdCreateShaderModule ShaderModuleHandle String
    -- ^ Create a shader module from WGSL source
  | CmdCreateRenderPipeline RenderPipelineHandle ShaderModuleHandle
    -- ^ Create a render pipeline (simplified - full descriptor needed)
  | CmdCreateComputePipeline ComputePipelineHandle ShaderModuleHandle
    -- ^ Create a compute pipeline (simplified - full descriptor needed)
  | CmdCreateBindGroup BindGroupHandle (Array BindGroupEntry)
    -- ^ Create a bind group with entries
  
  -- Resource Destruction
  | CmdDestroyBuffer BufferHandle
    -- ^ Destroy a buffer
  | CmdDestroyTexture TextureHandle
    -- ^ Destroy a texture
  
  -- Data Transfer
  | CmdWriteBuffer BufferHandle BufferOffset BufferSize
    -- ^ Write data to a buffer at offset with size bytes
  | CmdWriteTexture TextureHandle TextureDescriptor2D
    -- ^ Write data to a texture (descriptor provides size for bandwidth calculation)
  | CmdCopyBufferToBuffer BufferHandle BufferOffset BufferHandle BufferOffset BufferSize
    -- ^ Copy from source buffer+offset to dest buffer+offset, size bytes
  | CmdCopyTextureToTexture TextureHandle TextureHandle TextureDescriptor2D
    -- ^ Copy from source texture to dest texture (descriptor is source size)
  
  -- Render Pass
  | CmdBeginRenderPass RenderPassDescriptor
    -- ^ Begin a render pass
  | CmdEndRenderPass
    -- ^ End the current render pass
  | CmdSetRenderPipeline RenderPipelineHandle
    -- ^ Set the render pipeline for subsequent draws
  | CmdSetBindGroup Int BindGroupHandle
    -- ^ Set a bind group at the given index
  | CmdSetVertexBuffer Int BufferHandle
    -- ^ Set a vertex buffer at the given slot
  | CmdSetIndexBuffer BufferHandle IndexFormat
    -- ^ Set the index buffer
  | CmdDraw DrawParams
    -- ^ Draw primitives
  | CmdDrawIndexed DrawIndexedParams
    -- ^ Draw indexed primitives
  | CmdSetViewport Viewport
    -- ^ Set the viewport
  | CmdSetScissorRect ScissorRect
    -- ^ Set the scissor rectangle
  
  -- Compute Pass
  | CmdBeginComputePass
    -- ^ Begin a compute pass
  | CmdEndComputePass
    -- ^ End the current compute pass
  | CmdSetComputePipeline ComputePipelineHandle
    -- ^ Set the compute pipeline for subsequent dispatches
  | CmdDispatch DispatchParams
    -- ^ Dispatch compute workgroups
  
  -- Submission
  | CmdSubmit (Array CommandBufferHandle)
    -- ^ Submit command buffers to the queue

-- | Bind group entry (simplified).
type BindGroupEntry =
  { binding :: Int
  , resource :: BindingResource
  }

-- | Binding resource types.
data BindingResource
  = BindBuffer BufferHandle
  | BindTexture TextureViewHandle
  | BindSampler SamplerHandle

-- | Count binding types in an array of bind group entries.
-- |
-- | Returns a record with counts of each binding type:
-- | - buffers: number of BindBuffer entries
-- | - textures: number of BindTexture entries  
-- | - samplers: number of BindSampler entries
type BindingCounts =
  { buffers :: Int
  , textures :: Int
  , samplers :: Int
  }

-- | Count the bindings in a bind group entry array.
countBindings :: Array BindGroupEntry -> BindingCounts
countBindings entries = foldl countEntry { buffers: 0, textures: 0, samplers: 0 } entries
  where
    countEntry :: BindingCounts -> BindGroupEntry -> BindingCounts
    countEntry counts entry = case entry.resource of
      BindBuffer _ -> counts { buffers = counts.buffers + 1 }
      BindTexture _ -> counts { textures = counts.textures + 1 }
      BindSampler _ -> counts { samplers = counts.samplers + 1 }

-- | Compute the co-effect for a bind group from its entries.
-- |
-- | The co-effect is the COMPOSITE of:
-- | - CoEffectBufferBinding (count of buffer bindings)
-- | - CoEffectTextureBinding (count of texture bindings)
-- | - CoEffectSamplerBinding (count of sampler bindings)
bindGroupCoEffect :: Array BindGroupEntry -> GPUCoEffect
bindGroupCoEffect entries =
  let counts = countBindings entries
      bufferCoEff = if counts.buffers > 0 
                    then CoEffectBufferBinding counts.buffers 
                    else CoEffectNone
      textureCoEff = if counts.textures > 0 
                     then CoEffectTextureBinding counts.textures 
                     else CoEffectNone
      samplerCoEff = if counts.samplers > 0 
                     then CoEffectSamplerBinding counts.samplers 
                     else CoEffectNone
  in coEffectCombine bufferCoEff (coEffectCombine textureCoEff samplerCoEff)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // effect / co-effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate the effect (what the command CAN DO) for a command.
commandEffect :: GPUCommand -> GPUEffect
commandEffect (CmdCreateBuffer _ _) = EffectAllocateMemory
commandEffect (CmdCreateTexture _ _) = EffectAllocateMemory
commandEffect (CmdCreateTextureView _ _) = EffectNone
commandEffect (CmdCreateSampler _ _) = EffectNone
commandEffect (CmdCreateShaderModule _ _) = EffectNone
commandEffect (CmdCreateRenderPipeline _ _) = EffectNone
commandEffect (CmdCreateComputePipeline _ _) = EffectNone
commandEffect (CmdCreateBindGroup _ _) = EffectBindResource
commandEffect (CmdDestroyBuffer _) = EffectFreeMemory
commandEffect (CmdDestroyTexture _) = EffectFreeMemory
commandEffect (CmdWriteBuffer _ _ _) = EffectCopyBuffer
commandEffect (CmdWriteTexture _ _) = EffectCopyTexture
commandEffect (CmdCopyBufferToBuffer _ _ _ _ _) = EffectCopyBuffer
commandEffect (CmdCopyTextureToTexture _ _ _) = EffectCopyTexture
commandEffect (CmdBeginRenderPass _) = EffectNone
commandEffect CmdEndRenderPass = EffectNone
commandEffect (CmdSetRenderPipeline _) = EffectBindResource
commandEffect (CmdSetBindGroup _ _) = EffectBindResource
commandEffect (CmdSetVertexBuffer _ _) = EffectBindResource
commandEffect (CmdSetIndexBuffer _ _) = EffectBindResource
commandEffect (CmdDraw _) = EffectDraw
commandEffect (CmdDrawIndexed _) = EffectDraw
commandEffect (CmdSetViewport _) = EffectNone
commandEffect (CmdSetScissorRect _) = EffectNone
commandEffect CmdBeginComputePass = EffectNone
commandEffect CmdEndComputePass = EffectNone
commandEffect (CmdSetComputePipeline _) = EffectBindResource
commandEffect (CmdDispatch _) = EffectDispatchCompute
commandEffect (CmdSubmit _) = EffectPresent

-- | Calculate the co-effect (what the command NEEDS) for a command.
commandCoEffect :: GPUCommand -> GPUCoEffect
commandCoEffect (CmdCreateBuffer _ desc) = CoEffectMemory (unwrapBufferSize desc.size)
commandCoEffect (CmdCreateTexture _ desc) = CoEffectMemory (textureMemoryBytes desc)
commandCoEffect (CmdCreateTextureView _ _) = CoEffectNone
commandCoEffect (CmdCreateSampler _ _) = CoEffectNone
commandCoEffect (CmdCreateShaderModule _ _) = CoEffectNone
commandCoEffect (CmdCreateRenderPipeline _ _) = CoEffectPipeline
commandCoEffect (CmdCreateComputePipeline _ _) = CoEffectPipeline
commandCoEffect (CmdCreateBindGroup _ entries) = bindGroupCoEffect entries
commandCoEffect (CmdDestroyBuffer _) = CoEffectNone
commandCoEffect (CmdDestroyTexture _) = CoEffectNone
-- Data transfer commands consume bandwidth (bytes transferred)
commandCoEffect (CmdWriteBuffer _ _ size) = CoEffectBandwidth (unwrapBufferSize size)
commandCoEffect (CmdWriteTexture _ desc) = CoEffectBandwidth (textureMemoryBytes desc)
commandCoEffect (CmdCopyBufferToBuffer _ _ _ _ size) = CoEffectBandwidth (unwrapBufferSize size)
commandCoEffect (CmdCopyTextureToTexture _ _ desc) = CoEffectBandwidth (textureMemoryBytes desc)
commandCoEffect (CmdBeginRenderPass _) = CoEffectRenderTarget
commandCoEffect CmdEndRenderPass = CoEffectNone
commandCoEffect (CmdSetRenderPipeline _) = CoEffectPipeline
-- SetBindGroup/SetVertexBuffer/SetIndexBuffer reference already-created resources.
-- Their co-effect is CoEffectNone because the memory/binding was allocated at creation.
commandCoEffect (CmdSetBindGroup _ _) = CoEffectNone
commandCoEffect (CmdSetVertexBuffer _ _) = CoEffectNone
commandCoEffect (CmdSetIndexBuffer _ _) = CoEffectNone
commandCoEffect (CmdDraw _) = CoEffectNone
commandCoEffect (CmdDrawIndexed _) = CoEffectNone
commandCoEffect (CmdSetViewport _) = CoEffectNone
commandCoEffect (CmdSetScissorRect _) = CoEffectNone
commandCoEffect CmdBeginComputePass = CoEffectNone
commandCoEffect CmdEndComputePass = CoEffectNone
commandCoEffect (CmdSetComputePipeline _) = CoEffectPipeline
commandCoEffect (CmdDispatch params) = 
  let total = unwrapWorkgroupCount params.workgroupCountX 
            * unwrapWorkgroupCount params.workgroupCountY 
            * unwrapWorkgroupCount params.workgroupCountZ
  in CoEffectWorkgroups total
commandCoEffect (CmdSubmit _) = CoEffectNone
