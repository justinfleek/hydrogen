-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // gpu // webgpu // scene3d // render // commands
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Render Commands — Pure data describing GPU operations.
--
-- Commands are immutable descriptions of what to do.
-- The runtime executes them against the GPU via Device.purs FFI.
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render.Commands
  ( -- Render commands (pure data)
    RenderCommand
      ( ClearCommand
      , SetPipelineCommand
      , SetBindGroupCommand
      , SetVertexBufferCommand
      , SetIndexBufferCommand
      , DrawIndexedCommand
      , DrawCommand
      )
    -- Command parameter types
  , ClearParams
  , DrawIndexedParams
  , DrawParams
  , IndexFormat(Uint16, Uint32)
  , BufferRef(BufferRef)
  , BindGroupData
  ) where

import Prelude (class Eq)

import Hydrogen.GPU.WebGPU.Pipeline (PipelineKey)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER COMMANDS (PURE DATA)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A single GPU render command.
-- | Pure data describing what to do — executed by runtime.
data RenderCommand
  = ClearCommand ClearParams
  | SetPipelineCommand PipelineKey
  | SetBindGroupCommand Int BindGroupData
  | SetVertexBufferCommand Int BufferRef
  | SetIndexBufferCommand BufferRef IndexFormat
  | DrawIndexedCommand DrawIndexedParams
  | DrawCommand DrawParams

derive instance eqRenderCommand :: Eq RenderCommand

-- | Clear parameters.
type ClearParams =
  { color :: Vec4 Number
  , depth :: Number
  , stencil :: Int
  }

-- | Draw indexed parameters.
type DrawIndexedParams =
  { indexCount :: Int
  , instanceCount :: Int
  , firstIndex :: Int
  , baseVertex :: Int
  , firstInstance :: Int
  }

-- | Draw (non-indexed) parameters.
type DrawParams =
  { vertexCount :: Int
  , instanceCount :: Int
  , firstVertex :: Int
  , firstInstance :: Int
  }

-- | Index format.
data IndexFormat = Uint16 | Uint32

derive instance eqIndexFormat :: Eq IndexFormat

-- | Buffer reference (ID for runtime to resolve).
newtype BufferRef = BufferRef Int

derive instance eqBufferRef :: Eq BufferRef

-- | Bind group data.
type BindGroupData =
  { uniforms :: Array Number
  , textures :: Array Int
  , samplers :: Array Int
  }
