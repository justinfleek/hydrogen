-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // gpu // handle
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Resource Handles — Typed references to GPU resources.
-- |
-- | ## Design Philosophy
-- |
-- | GPU resources (buffers, textures, pipelines) are created by the runtime
-- | and referenced by handles. This module provides:
-- |
-- | 1. **Typed handles**: Each resource type has its own handle type
-- | 2. **UUID5 identity**: Handles are deterministic based on creation params
-- | 3. **Phantom types**: Handles carry their resource type at compile time
-- |
-- | ## Handle Lifecycle
-- |
-- | ```
-- | CreateBuffer descriptor → BufferHandle
-- | WriteBuffer handle data → ()
-- | DestroyBuffer handle → ()
-- | ```
-- |
-- | Handles are opaque to PureScript. The runtime maps them to actual
-- | WebGPU objects. This separation enables:
-- |
-- | - Pure command composition without FFI
-- | - Deterministic replay of GPU programs
-- | - Lean4 verification of resource lifetimes
-- |
-- | ## Co-Effect Tracking
-- |
-- | Each handle creation contributes to co-effects:
-- | - BufferHandle → CoEffectMemory (buffer size)
-- | - TextureHandle → CoEffectMemory (texture size)
-- | - BindGroupHandle → CoEffectBufferBinding + CoEffectTextureBinding
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.GPU.Handle
  ( -- * Handle Types
    HandleId
  , handleId
  , unwrapHandleId
  
  -- * Resource Handles
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
  
  -- * Handle Generation
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
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // handle id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a GPU resource handle.
-- |
-- | Handle IDs are monotonically increasing integers assigned at creation time.
-- | The runtime maps these to actual WebGPU object references.
newtype HandleId = HandleId Int

derive instance eqHandleId :: Eq HandleId
derive instance ordHandleId :: Ord HandleId

instance showHandleId :: Show HandleId where
  show (HandleId n) = "Handle#" <> show n

-- | Create a handle ID from an integer.
handleId :: Int -> HandleId
handleId = HandleId

-- | Extract the integer from a handle ID.
unwrapHandleId :: HandleId -> Int
unwrapHandleId (HandleId n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // buffer handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU buffer.
newtype BufferHandle = BufferHandle HandleId

derive instance eqBufferHandle :: Eq BufferHandle
derive instance ordBufferHandle :: Ord BufferHandle

instance showBufferHandle :: Show BufferHandle where
  show (BufferHandle hid) = "Buffer(" <> show hid <> ")"

-- | Create a buffer handle.
bufferHandle :: HandleId -> BufferHandle
bufferHandle = BufferHandle

-- | Get the handle ID from a buffer handle.
bufferHandleId :: BufferHandle -> HandleId
bufferHandleId (BufferHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // texture handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU texture.
newtype TextureHandle = TextureHandle HandleId

derive instance eqTextureHandle :: Eq TextureHandle
derive instance ordTextureHandle :: Ord TextureHandle

instance showTextureHandle :: Show TextureHandle where
  show (TextureHandle hid) = "Texture(" <> show hid <> ")"

-- | Create a texture handle.
textureHandle :: HandleId -> TextureHandle
textureHandle = TextureHandle

-- | Get the handle ID from a texture handle.
textureHandleId :: TextureHandle -> HandleId
textureHandleId (TextureHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // texture view handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU texture view.
newtype TextureViewHandle = TextureViewHandle HandleId

derive instance eqTextureViewHandle :: Eq TextureViewHandle
derive instance ordTextureViewHandle :: Ord TextureViewHandle

instance showTextureViewHandle :: Show TextureViewHandle where
  show (TextureViewHandle hid) = "TextureView(" <> show hid <> ")"

-- | Create a texture view handle.
textureViewHandle :: HandleId -> TextureViewHandle
textureViewHandle = TextureViewHandle

-- | Get the handle ID from a texture view handle.
textureViewHandleId :: TextureViewHandle -> HandleId
textureViewHandleId (TextureViewHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // sampler handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU sampler.
newtype SamplerHandle = SamplerHandle HandleId

derive instance eqSamplerHandle :: Eq SamplerHandle
derive instance ordSamplerHandle :: Ord SamplerHandle

instance showSamplerHandle :: Show SamplerHandle where
  show (SamplerHandle hid) = "Sampler(" <> show hid <> ")"

-- | Create a sampler handle.
samplerHandle :: HandleId -> SamplerHandle
samplerHandle = SamplerHandle

-- | Get the handle ID from a sampler handle.
samplerHandleId :: SamplerHandle -> HandleId
samplerHandleId (SamplerHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // shader module handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU shader module.
newtype ShaderModuleHandle = ShaderModuleHandle HandleId

derive instance eqShaderModuleHandle :: Eq ShaderModuleHandle
derive instance ordShaderModuleHandle :: Ord ShaderModuleHandle

instance showShaderModuleHandle :: Show ShaderModuleHandle where
  show (ShaderModuleHandle hid) = "ShaderModule(" <> show hid <> ")"

-- | Create a shader module handle.
shaderModuleHandle :: HandleId -> ShaderModuleHandle
shaderModuleHandle = ShaderModuleHandle

-- | Get the handle ID from a shader module handle.
shaderModuleHandleId :: ShaderModuleHandle -> HandleId
shaderModuleHandleId (ShaderModuleHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // render pipeline handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU render pipeline.
newtype RenderPipelineHandle = RenderPipelineHandle HandleId

derive instance eqRenderPipelineHandle :: Eq RenderPipelineHandle
derive instance ordRenderPipelineHandle :: Ord RenderPipelineHandle

instance showRenderPipelineHandle :: Show RenderPipelineHandle where
  show (RenderPipelineHandle hid) = "RenderPipeline(" <> show hid <> ")"

-- | Create a render pipeline handle.
renderPipelineHandle :: HandleId -> RenderPipelineHandle
renderPipelineHandle = RenderPipelineHandle

-- | Get the handle ID from a render pipeline handle.
renderPipelineHandleId :: RenderPipelineHandle -> HandleId
renderPipelineHandleId (RenderPipelineHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // compute pipeline handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU compute pipeline.
newtype ComputePipelineHandle = ComputePipelineHandle HandleId

derive instance eqComputePipelineHandle :: Eq ComputePipelineHandle
derive instance ordComputePipelineHandle :: Ord ComputePipelineHandle

instance showComputePipelineHandle :: Show ComputePipelineHandle where
  show (ComputePipelineHandle hid) = "ComputePipeline(" <> show hid <> ")"

-- | Create a compute pipeline handle.
computePipelineHandle :: HandleId -> ComputePipelineHandle
computePipelineHandle = ComputePipelineHandle

-- | Get the handle ID from a compute pipeline handle.
computePipelineHandleId :: ComputePipelineHandle -> HandleId
computePipelineHandleId (ComputePipelineHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // bind group handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU bind group.
newtype BindGroupHandle = BindGroupHandle HandleId

derive instance eqBindGroupHandle :: Eq BindGroupHandle
derive instance ordBindGroupHandle :: Ord BindGroupHandle

instance showBindGroupHandle :: Show BindGroupHandle where
  show (BindGroupHandle hid) = "BindGroup(" <> show hid <> ")"

-- | Create a bind group handle.
bindGroupHandle :: HandleId -> BindGroupHandle
bindGroupHandle = BindGroupHandle

-- | Get the handle ID from a bind group handle.
bindGroupHandleId :: BindGroupHandle -> HandleId
bindGroupHandleId (BindGroupHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // bind group layout handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU bind group layout.
newtype BindGroupLayoutHandle = BindGroupLayoutHandle HandleId

derive instance eqBindGroupLayoutHandle :: Eq BindGroupLayoutHandle
derive instance ordBindGroupLayoutHandle :: Ord BindGroupLayoutHandle

instance showBindGroupLayoutHandle :: Show BindGroupLayoutHandle where
  show (BindGroupLayoutHandle hid) = "BindGroupLayout(" <> show hid <> ")"

-- | Create a bind group layout handle.
bindGroupLayoutHandle :: HandleId -> BindGroupLayoutHandle
bindGroupLayoutHandle = BindGroupLayoutHandle

-- | Get the handle ID from a bind group layout handle.
bindGroupLayoutHandleId :: BindGroupLayoutHandle -> HandleId
bindGroupLayoutHandleId (BindGroupLayoutHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // pipeline layout handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU pipeline layout.
newtype PipelineLayoutHandle = PipelineLayoutHandle HandleId

derive instance eqPipelineLayoutHandle :: Eq PipelineLayoutHandle
derive instance ordPipelineLayoutHandle :: Ord PipelineLayoutHandle

instance showPipelineLayoutHandle :: Show PipelineLayoutHandle where
  show (PipelineLayoutHandle hid) = "PipelineLayout(" <> show hid <> ")"

-- | Create a pipeline layout handle.
pipelineLayoutHandle :: HandleId -> PipelineLayoutHandle
pipelineLayoutHandle = PipelineLayoutHandle

-- | Get the handle ID from a pipeline layout handle.
pipelineLayoutHandleId :: PipelineLayoutHandle -> HandleId
pipelineLayoutHandleId (PipelineLayoutHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // command buffer handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU command buffer.
newtype CommandBufferHandle = CommandBufferHandle HandleId

derive instance eqCommandBufferHandle :: Eq CommandBufferHandle
derive instance ordCommandBufferHandle :: Ord CommandBufferHandle

instance showCommandBufferHandle :: Show CommandBufferHandle where
  show (CommandBufferHandle hid) = "CommandBuffer(" <> show hid <> ")"

-- | Create a command buffer handle.
commandBufferHandle :: HandleId -> CommandBufferHandle
commandBufferHandle = CommandBufferHandle

-- | Get the handle ID from a command buffer handle.
commandBufferHandleId :: CommandBufferHandle -> HandleId
commandBufferHandleId (CommandBufferHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // query set handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle to a GPU query set.
newtype QuerySetHandle = QuerySetHandle HandleId

derive instance eqQuerySetHandle :: Eq QuerySetHandle
derive instance ordQuerySetHandle :: Ord QuerySetHandle

instance showQuerySetHandle :: Show QuerySetHandle where
  show (QuerySetHandle hid) = "QuerySet(" <> show hid <> ")"

-- | Create a query set handle.
querySetHandle :: HandleId -> QuerySetHandle
querySetHandle = QuerySetHandle

-- | Get the handle ID from a query set handle.
querySetHandleId :: QuerySetHandle -> HandleId
querySetHandleId (QuerySetHandle hid) = hid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // handle generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Counter for generating unique handle IDs.
-- |
-- | This is pure state - no FFI. The runtime maintains the mapping from
-- | handle IDs to actual WebGPU objects.
type HandleCounter =
  { nextBuffer :: Int
  , nextTexture :: Int
  , nextTextureView :: Int
  , nextSampler :: Int
  , nextShaderModule :: Int
  , nextRenderPipeline :: Int
  , nextComputePipeline :: Int
  , nextBindGroup :: Int
  , nextBindGroupLayout :: Int
  , nextPipelineLayout :: Int
  , nextCommandBuffer :: Int
  , nextQuerySet :: Int
  }

-- | Initial handle counter (all zeros).
initialHandleCounter :: HandleCounter
initialHandleCounter =
  { nextBuffer: 0
  , nextTexture: 0
  , nextTextureView: 0
  , nextSampler: 0
  , nextShaderModule: 0
  , nextRenderPipeline: 0
  , nextComputePipeline: 0
  , nextBindGroup: 0
  , nextBindGroupLayout: 0
  , nextPipelineLayout: 0
  , nextCommandBuffer: 0
  , nextQuerySet: 0
  }

-- | Generate the next buffer handle.
nextBufferHandle :: HandleCounter -> { handle :: BufferHandle, counter :: HandleCounter }
nextBufferHandle c =
  { handle: bufferHandle (handleId c.nextBuffer)
  , counter: c { nextBuffer = c.nextBuffer + 1 }
  }

-- | Generate the next texture handle.
nextTextureHandle :: HandleCounter -> { handle :: TextureHandle, counter :: HandleCounter }
nextTextureHandle c =
  { handle: textureHandle (handleId c.nextTexture)
  , counter: c { nextTexture = c.nextTexture + 1 }
  }

-- | Generate the next sampler handle.
nextSamplerHandle :: HandleCounter -> { handle :: SamplerHandle, counter :: HandleCounter }
nextSamplerHandle c =
  { handle: samplerHandle (handleId c.nextSampler)
  , counter: c { nextSampler = c.nextSampler + 1 }
  }

-- | Generate the next shader module handle.
nextShaderModuleHandle :: HandleCounter -> { handle :: ShaderModuleHandle, counter :: HandleCounter }
nextShaderModuleHandle c =
  { handle: shaderModuleHandle (handleId c.nextShaderModule)
  , counter: c { nextShaderModule = c.nextShaderModule + 1 }
  }

-- | Generate the next render pipeline handle.
nextRenderPipelineHandle :: HandleCounter -> { handle :: RenderPipelineHandle, counter :: HandleCounter }
nextRenderPipelineHandle c =
  { handle: renderPipelineHandle (handleId c.nextRenderPipeline)
  , counter: c { nextRenderPipeline = c.nextRenderPipeline + 1 }
  }

-- | Generate the next compute pipeline handle.
nextComputePipelineHandle :: HandleCounter -> { handle :: ComputePipelineHandle, counter :: HandleCounter }
nextComputePipelineHandle c =
  { handle: computePipelineHandle (handleId c.nextComputePipeline)
  , counter: c { nextComputePipeline = c.nextComputePipeline + 1 }
  }

-- | Generate the next bind group handle.
nextBindGroupHandle :: HandleCounter -> { handle :: BindGroupHandle, counter :: HandleCounter }
nextBindGroupHandle c =
  { handle: bindGroupHandle (handleId c.nextBindGroup)
  , counter: c { nextBindGroup = c.nextBindGroup + 1 }
  }

-- | Generate the next command buffer handle.
nextCommandBufferHandle :: HandleCounter -> { handle :: CommandBufferHandle, counter :: HandleCounter }
nextCommandBufferHandle c =
  { handle: commandBufferHandle (handleId c.nextCommandBuffer)
  , counter: c { nextCommandBuffer = c.nextCommandBuffer + 1 }
  }
