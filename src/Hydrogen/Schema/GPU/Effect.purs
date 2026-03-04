-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // schema // gpu // effect
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Effects and Co-Effects — Graded monads for GPU operations.
-- |
-- | ## Research Foundation
-- |
-- | Based on Orchard-style graded monads where operations carry their
-- | capability requirements in the type. GPU operations have:
-- |
-- | - **Effects**: What the operation CAN DO (allocate, bind, draw, present)
-- | - **Co-Effects**: What the operation NEEDS (device, memory, bindings)
-- |
-- | ## Landauer Connection
-- |
-- | GPU operations are fundamentally about moving data between memory
-- | hierarchies. Each transfer has an information-theoretic cost:
-- |
-- | - CPU → GPU: Upload (high latency, batched)
-- | - GPU → CPU: Readback (synchronization point)
-- | - VRAM → Cache: Binding (affects shader performance)
-- |
-- | The co-effect system tracks these costs for optimization.
-- |
-- | ## Presburger Decidability
-- |
-- | All resource bounds (memory bytes, binding slots, vertex counts)
-- | are bounded integers. Constraint satisfaction is decidable.
-- |
-- | ## ILP Optimization
-- |
-- | GPU command scheduling is an ILP problem:
-- | - Minimize state changes (pipeline, bind group switches)
-- | - Maximize batching (draw calls with same state)
-- | - Subject to: memory limits, binding slot limits
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Semigroup, Monoid)
-- | - Hydrogen.Schema.Attestation.UUID5

module Hydrogen.Schema.GPU.Effect
  ( -- * UUID5 Namespace
    nsGPU
  
  -- * GPU Effects (what operations CAN DO)
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
  
  -- * GPU Co-Effects (what operations NEED)
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
  
  -- * GPU Operations
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
  
  -- * GPU Expression AST
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
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , show
  , max
  , mempty
  , (==)
  , (+)
  , (<>)
  )

import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // uuid5 namespace
-- ═════════════════════════════════════════════════════════════════════════════

-- | Root namespace for all GPU schema UUIDs.
nsGPU :: UUID5.UUID5
nsGPU = UUID5.uuid5 UUID5.nsElement "gpu"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // gpu effects (graded)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What GPU operations CAN DO.
-- |
-- | Graded monoid: effects combine via union.
-- | Grade algebra: E₁ ⊗ E₂ = union of capabilities.
data GPUEffect
  = EffectNone             -- ^ Pure computation, no GPU side effects
  | EffectAllocateMemory   -- ^ Can allocate GPU memory
  | EffectFreeMemory       -- ^ Can free GPU memory
  | EffectBindResource     -- ^ Can bind resources to pipeline
  | EffectDraw             -- ^ Can issue draw calls
  | EffectDispatchCompute  -- ^ Can dispatch compute shaders
  | EffectCopyBuffer       -- ^ Can copy buffer data
  | EffectCopyTexture      -- ^ Can copy texture data
  | EffectPresent          -- ^ Can present to screen
  | EffectComposite        -- ^ Combination of effects
      (Array GPUEffect)

derive instance eqGPUEffect :: Eq GPUEffect
derive instance ordGPUEffect :: Ord GPUEffect

instance showGPUEffect :: Show GPUEffect where
  show EffectNone = "none"
  show EffectAllocateMemory = "allocate-memory"
  show EffectFreeMemory = "free-memory"
  show EffectBindResource = "bind-resource"
  show EffectDraw = "draw"
  show EffectDispatchCompute = "dispatch-compute"
  show EffectCopyBuffer = "copy-buffer"
  show EffectCopyTexture = "copy-texture"
  show EffectPresent = "present"
  show (EffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupGPUEffect :: Semigroup GPUEffect where
  append = effectCombine

instance monoidGPUEffect :: Monoid GPUEffect where
  mempty = EffectNone

-- | All primitive GPU effects.
allGPUEffects :: Array GPUEffect
allGPUEffects =
  [ EffectNone
  , EffectAllocateMemory
  , EffectFreeMemory
  , EffectBindResource
  , EffectDraw
  , EffectDispatchCompute
  , EffectCopyBuffer
  , EffectCopyTexture
  , EffectPresent
  ]

-- | Combine two effects (monoid operation).
effectCombine :: GPUEffect -> GPUEffect -> GPUEffect
effectCombine EffectNone e = e
effectCombine e EffectNone = e
effectCombine (EffectComposite a) (EffectComposite b) = EffectComposite (a <> b)
effectCombine (EffectComposite a) e = EffectComposite (a <> [e])
effectCombine e (EffectComposite b) = EffectComposite ([e] <> b)
effectCombine e1 e2 = if e1 == e2 then e1 else EffectComposite [e1, e2]

-- | No effects (identity).
effectNone :: GPUEffect
effectNone = EffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // gpu co-effects (needs)
-- ═════════════════════════════════════════════════════════════════════════════

-- | What GPU operations NEED (resources/dependencies).
-- |
-- | Co-effect algebra: tracks what must be provided by the environment.
-- | Resource requirements are additive (memory sums, bindings sum).
-- |
-- | ## Bandwidth Semantics
-- |
-- | CoEffectBandwidth tracks data transfer costs (bytes transferred).
-- | This is distinct from CoEffectMemory (bytes allocated):
-- |
-- | - Memory: Static cost at allocation time
-- | - Bandwidth: Dynamic cost per transfer operation
-- |
-- | Bandwidth is additive: two WriteBuffer calls sum their bytes.
data GPUCoEffect
  = CoEffectNone               -- ^ No special requirements
  | CoEffectDevice             -- ^ Needs GPU device
  | CoEffectMemory Int         -- ^ Memory needed (bytes) - ALLOCATION cost
  | CoEffectBandwidth Int      -- ^ Transfer bandwidth (bytes) - TRANSFER cost
  | CoEffectBufferBinding Int  -- ^ Buffer binding slots needed
  | CoEffectTextureBinding Int -- ^ Texture binding slots needed
  | CoEffectSamplerBinding Int -- ^ Sampler binding slots needed
  | CoEffectPipeline           -- ^ Needs active pipeline
  | CoEffectRenderTarget       -- ^ Needs render target (framebuffer)
  | CoEffectWorkgroups Int     -- ^ Compute workgroups needed (max, not sum)
  | CoEffectComposite          -- ^ Multiple requirements
      (Array GPUCoEffect)

derive instance eqGPUCoEffect :: Eq GPUCoEffect
derive instance ordGPUCoEffect :: Ord GPUCoEffect

instance showGPUCoEffect :: Show GPUCoEffect where
  show CoEffectNone = "none"
  show CoEffectDevice = "device"
  show (CoEffectMemory n) = "memory(" <> show n <> " bytes)"
  show (CoEffectBandwidth n) = "bandwidth(" <> show n <> " bytes)"
  show (CoEffectBufferBinding n) = "buffer-bindings(" <> show n <> ")"
  show (CoEffectTextureBinding n) = "texture-bindings(" <> show n <> ")"
  show (CoEffectSamplerBinding n) = "sampler-bindings(" <> show n <> ")"
  show CoEffectPipeline = "pipeline"
  show CoEffectRenderTarget = "render-target"
  show (CoEffectWorkgroups n) = "workgroups(" <> show n <> ")"
  show (CoEffectComposite effs) = "composite(" <> show effs <> ")"

instance semigroupGPUCoEffect :: Semigroup GPUCoEffect where
  append = coEffectCombine

instance monoidGPUCoEffect :: Monoid GPUCoEffect where
  mempty = CoEffectNone

-- | All primitive co-effects.
allGPUCoEffects :: Array GPUCoEffect
allGPUCoEffects =
  [ CoEffectNone
  , CoEffectDevice
  , CoEffectPipeline
  , CoEffectRenderTarget
  ]

-- | Combine co-effects.
-- |
-- | ## Combining Semantics
-- |
-- | - Memory: ADDITIVE (sum of allocations)
-- | - Bandwidth: ADDITIVE (sum of transfers)
-- | - Bindings: ADDITIVE (sum of slots)
-- | - Workgroups: MAX (parallel capacity needed)
-- | - Dissimilar: COMPOSITE (wrapped in array)
coEffectCombine :: GPUCoEffect -> GPUCoEffect -> GPUCoEffect
coEffectCombine CoEffectNone e = e
coEffectCombine e CoEffectNone = e
coEffectCombine (CoEffectMemory a) (CoEffectMemory b) = CoEffectMemory (a + b)
coEffectCombine (CoEffectBandwidth a) (CoEffectBandwidth b) = CoEffectBandwidth (a + b)
coEffectCombine (CoEffectBufferBinding a) (CoEffectBufferBinding b) = 
  CoEffectBufferBinding (a + b)
coEffectCombine (CoEffectTextureBinding a) (CoEffectTextureBinding b) = 
  CoEffectTextureBinding (a + b)
coEffectCombine (CoEffectSamplerBinding a) (CoEffectSamplerBinding b) = 
  CoEffectSamplerBinding (a + b)
coEffectCombine (CoEffectWorkgroups a) (CoEffectWorkgroups b) = 
  CoEffectWorkgroups (max a b)  -- Workgroups use max (parallel capacity)
coEffectCombine (CoEffectComposite a) (CoEffectComposite b) = CoEffectComposite (a <> b)
coEffectCombine (CoEffectComposite a) e = CoEffectComposite (a <> [e])
coEffectCombine e (CoEffectComposite b) = CoEffectComposite ([e] <> b)
coEffectCombine e1 e2 = if e1 == e2 then e1 else CoEffectComposite [e1, e2]

-- | No co-effects (identity).
coEffectNone :: GPUCoEffect
coEffectNone = CoEffectNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gpu operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Primitive GPU operations.
-- |
-- | Each operation has a known effect (what it does) and
-- | co-effect (what it needs). These are the vocabulary
-- | for building GPU command buffers.
data GPUOp
  = -- Resource creation/destruction
    OpCreateBuffer           -- ^ Allocate buffer
  | OpDestroyBuffer          -- ^ Free buffer
  | OpWriteBuffer            -- ^ Upload data to buffer
  | OpReadBuffer             -- ^ Download data from buffer
  | OpCreateTexture          -- ^ Allocate texture
  | OpDestroyTexture         -- ^ Free texture
  | OpWriteTexture           -- ^ Upload data to texture
  | OpCreateSampler          -- ^ Create sampler state
  | OpCreateShaderModule     -- ^ Compile shader
  | OpCreatePipeline         -- ^ Create render/compute pipeline
  | OpCreateBindGroup        -- ^ Create resource binding
  
  -- Render pass
  | OpBeginRenderPass        -- ^ Begin rendering to target
  | OpEndRenderPass          -- ^ End rendering
  | OpSetPipeline            -- ^ Bind pipeline
  | OpSetBindGroup           -- ^ Bind resources
  | OpSetVertexBuffer        -- ^ Bind vertex data
  | OpSetIndexBuffer         -- ^ Bind index data
  | OpDraw                   -- ^ Draw primitives
  | OpDrawIndexed            -- ^ Draw indexed primitives
  
  -- Compute
  | OpDispatchCompute        -- ^ Run compute shader
  
  -- Copy
  | OpCopyBufferToBuffer     -- ^ Copy between buffers
  | OpCopyTextureToTexture   -- ^ Copy between textures
  
  -- Submission
  | OpSubmit                 -- ^ Submit command buffer
  | OpPresent                -- ^ Present to screen

derive instance eqGPUOp :: Eq GPUOp
derive instance ordGPUOp :: Ord GPUOp

instance showGPUOp :: Show GPUOp where
  show OpCreateBuffer = "create-buffer"
  show OpDestroyBuffer = "destroy-buffer"
  show OpWriteBuffer = "write-buffer"
  show OpReadBuffer = "read-buffer"
  show OpCreateTexture = "create-texture"
  show OpDestroyTexture = "destroy-texture"
  show OpWriteTexture = "write-texture"
  show OpCreateSampler = "create-sampler"
  show OpCreateShaderModule = "create-shader-module"
  show OpCreatePipeline = "create-pipeline"
  show OpCreateBindGroup = "create-bind-group"
  show OpBeginRenderPass = "begin-render-pass"
  show OpEndRenderPass = "end-render-pass"
  show OpSetPipeline = "set-pipeline"
  show OpSetBindGroup = "set-bind-group"
  show OpSetVertexBuffer = "set-vertex-buffer"
  show OpSetIndexBuffer = "set-index-buffer"
  show OpDraw = "draw"
  show OpDrawIndexed = "draw-indexed"
  show OpDispatchCompute = "dispatch-compute"
  show OpCopyBufferToBuffer = "copy-buffer-to-buffer"
  show OpCopyTextureToTexture = "copy-texture-to-texture"
  show OpSubmit = "submit"
  show OpPresent = "present"

-- | All GPU operations.
allGPUOps :: Array GPUOp
allGPUOps =
  [ OpCreateBuffer, OpDestroyBuffer, OpWriteBuffer, OpReadBuffer
  , OpCreateTexture, OpDestroyTexture, OpWriteTexture
  , OpCreateSampler, OpCreateShaderModule, OpCreatePipeline, OpCreateBindGroup
  , OpBeginRenderPass, OpEndRenderPass
  , OpSetPipeline, OpSetBindGroup, OpSetVertexBuffer, OpSetIndexBuffer
  , OpDraw, OpDrawIndexed
  , OpDispatchCompute
  , OpCopyBufferToBuffer, OpCopyTextureToTexture
  , OpSubmit, OpPresent
  ]

-- | Effect produced by GPU operation.
gpuOpEffect :: GPUOp -> GPUEffect
gpuOpEffect OpCreateBuffer = EffectAllocateMemory
gpuOpEffect OpDestroyBuffer = EffectFreeMemory
gpuOpEffect OpWriteBuffer = EffectCopyBuffer
gpuOpEffect OpReadBuffer = EffectCopyBuffer
gpuOpEffect OpCreateTexture = EffectAllocateMemory
gpuOpEffect OpDestroyTexture = EffectFreeMemory
gpuOpEffect OpWriteTexture = EffectCopyTexture
gpuOpEffect OpCreateSampler = EffectAllocateMemory
gpuOpEffect OpCreateShaderModule = EffectAllocateMemory
gpuOpEffect OpCreatePipeline = EffectAllocateMemory
gpuOpEffect OpCreateBindGroup = EffectAllocateMemory
gpuOpEffect OpBeginRenderPass = EffectBindResource
gpuOpEffect OpEndRenderPass = EffectNone
gpuOpEffect OpSetPipeline = EffectBindResource
gpuOpEffect OpSetBindGroup = EffectBindResource
gpuOpEffect OpSetVertexBuffer = EffectBindResource
gpuOpEffect OpSetIndexBuffer = EffectBindResource
gpuOpEffect OpDraw = EffectDraw
gpuOpEffect OpDrawIndexed = EffectDraw
gpuOpEffect OpDispatchCompute = EffectDispatchCompute
gpuOpEffect OpCopyBufferToBuffer = EffectCopyBuffer
gpuOpEffect OpCopyTextureToTexture = EffectCopyTexture
gpuOpEffect OpSubmit = EffectNone
gpuOpEffect OpPresent = EffectPresent

-- | Co-effect required by GPU operation.
gpuOpCoEffect :: GPUOp -> GPUCoEffect
gpuOpCoEffect OpCreateBuffer = CoEffectDevice
gpuOpCoEffect OpDestroyBuffer = CoEffectDevice
gpuOpCoEffect OpWriteBuffer = CoEffectDevice
gpuOpCoEffect OpReadBuffer = CoEffectDevice
gpuOpCoEffect OpCreateTexture = CoEffectDevice
gpuOpCoEffect OpDestroyTexture = CoEffectDevice
gpuOpCoEffect OpWriteTexture = CoEffectDevice
gpuOpCoEffect OpCreateSampler = CoEffectDevice
gpuOpCoEffect OpCreateShaderModule = CoEffectDevice
gpuOpCoEffect OpCreatePipeline = CoEffectDevice
gpuOpCoEffect OpCreateBindGroup = CoEffectDevice
gpuOpCoEffect OpBeginRenderPass = CoEffectRenderTarget
gpuOpCoEffect OpEndRenderPass = CoEffectNone
gpuOpCoEffect OpSetPipeline = CoEffectPipeline
gpuOpCoEffect OpSetBindGroup = CoEffectPipeline
gpuOpCoEffect OpSetVertexBuffer = coEffectCombine CoEffectPipeline (CoEffectBufferBinding 1)
gpuOpCoEffect OpSetIndexBuffer = coEffectCombine CoEffectPipeline (CoEffectBufferBinding 1)
gpuOpCoEffect OpDraw = CoEffectPipeline
gpuOpCoEffect OpDrawIndexed = CoEffectPipeline
gpuOpCoEffect OpDispatchCompute = coEffectCombine CoEffectPipeline (CoEffectWorkgroups 1)
gpuOpCoEffect OpCopyBufferToBuffer = CoEffectDevice
gpuOpCoEffect OpCopyTextureToTexture = CoEffectDevice
gpuOpCoEffect OpSubmit = CoEffectDevice
gpuOpCoEffect OpPresent = CoEffectRenderTarget

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // gpu expression ast
-- ═════════════════════════════════════════════════════════════════════════════

-- | GPU command AST.
-- |
-- | Every expression carries its effect grade and co-effect requirements.
-- | This enables static analysis and optimization before execution.
data GPUExpr
  = -- | Pure value (no effects)
    GPUPure Int
    
  | -- | GPU operation
    GPUOp GPUOp
    
  | -- | Sequential composition
    GPUSeq GPUExpr GPUExpr
    
  | -- | Parallel composition (independent operations)
    GPUPar GPUExpr GPUExpr
    
  | -- | Loop (repeated operations)
    GPULoop Int GPUExpr
    
  | -- | Conditional (branch based on pure value)
    GPUConditional Int GPUExpr GPUExpr

derive instance eqGPUExpr :: Eq GPUExpr
derive instance ordGPUExpr :: Ord GPUExpr

instance showGPUExpr :: Show GPUExpr where
  show (GPUPure n) = "pure(" <> show n <> ")"
  show (GPUOp op) = "op(" <> show op <> ")"
  show (GPUSeq e1 e2) = "seq(" <> show e1 <> ", " <> show e2 <> ")"
  show (GPUPar e1 e2) = "par(" <> show e1 <> ", " <> show e2 <> ")"
  show (GPULoop n e) = "loop(" <> show n <> ", " <> show e <> ")"
  show (GPUConditional c t f) = "if(" <> show c <> ", " <> show t <> ", " <> show f <> ")"

-- | Compute effect grade of expression.
exprEffect :: GPUExpr -> GPUEffect
exprEffect (GPUPure _) = EffectNone
exprEffect (GPUOp op) = gpuOpEffect op
exprEffect (GPUSeq e1 e2) = effectCombine (exprEffect e1) (exprEffect e2)
exprEffect (GPUPar e1 e2) = effectCombine (exprEffect e1) (exprEffect e2)
exprEffect (GPULoop _ e) = exprEffect e
exprEffect (GPUConditional _ t f) = effectCombine (exprEffect t) (exprEffect f)

-- | Compute co-effect requirements of expression.
exprCoEffect :: GPUExpr -> GPUCoEffect
exprCoEffect (GPUPure _) = CoEffectNone
exprCoEffect (GPUOp op) = gpuOpCoEffect op
exprCoEffect (GPUSeq e1 e2) = coEffectCombine (exprCoEffect e1) (exprCoEffect e2)
exprCoEffect (GPUPar e1 e2) = coEffectCombine (exprCoEffect e1) (exprCoEffect e2)
exprCoEffect (GPULoop _ e) = exprCoEffect e
exprCoEffect (GPUConditional _ t f) = coEffectCombine (exprCoEffect t) (exprCoEffect f)

-- | Compute deterministic UUID for expression.
exprUUID :: GPUExpr -> UUID5.UUID5
exprUUID expr = UUID5.uuid5 nsGPU (show expr)
