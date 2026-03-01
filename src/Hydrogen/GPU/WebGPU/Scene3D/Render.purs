-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // gpu // webgpu // scene3d // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Scene3D Renderer — The core interpreter.
--
-- Takes pure Scene3D data, produces RenderCommands (also pure data).
-- RenderCommands are then executed against the GPU via Device.purs FFI.
--
-- ARCHITECTURE:
-- Scene3D (pure data)
--     | extractRenderState
-- RenderState (camera matrices, sorted meshes, light uniforms)
--     | generateRenderCommands
-- Array RenderCommand (pure draw call descriptions)
--     | (executed by runtime via Device.purs FFI)
-- GPU pixels
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- This is a leader module that re-exports from submodules:
-- - Commands.purs  — Render command types
-- - Uniforms.purs  — Uniform buffer structures
-- - Batching.purs  — Mesh batching and command generation
-- - Culling.purs   — Frustum culling and depth sorting
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render
  ( -- Render commands (pure data)
    module Commands
    -- Render state (extracted from Scene3D)
  , module Batching
    -- Frame uniforms
  , module Uniforms
    -- Culling and sorting
  , module Culling
  ) where

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RE-EXPORTS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

import Hydrogen.GPU.WebGPU.Scene3D.Render.Commands
  ( RenderCommand
      ( ClearCommand
      , SetPipelineCommand
      , SetBindGroupCommand
      , SetVertexBufferCommand
      , SetIndexBufferCommand
      , DrawIndexedCommand
      , DrawCommand
      )
  , ClearParams
  , DrawIndexedParams
  , DrawParams
  , IndexFormat(Uint16, Uint32)
  , BufferRef(BufferRef)
  , BindGroupData
  ) as Commands

import Hydrogen.GPU.WebGPU.Scene3D.Render.Uniforms
  ( FrameUniforms
  , computeFrameUniforms
  , LightUniforms
  , LightData
  , computeLightUniforms
  , ObjectUniforms
  , computeObjectUniforms
  , MaterialUniforms
  , computeMaterialUniforms
  , computeEulerRotation
  , identityTransform
  ) as Uniforms

import Hydrogen.GPU.WebGPU.Scene3D.Render.Batching
  ( RenderState
  , extractRenderState
  , RenderBatch
  , batchByMaterial
  , generateRenderCommands
  , generateShadowCommands
  , generatePickCommands
  ) as Batching

import Hydrogen.GPU.WebGPU.Scene3D.Render.Culling
  ( frustumCull
  , sortByDepth
  ) as Culling
