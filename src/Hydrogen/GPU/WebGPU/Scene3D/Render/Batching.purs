-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // gpu // webgpu // scene3d // render // batching
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Render Batching — Groups meshes by material for efficient rendering.
--
-- Minimizes GPU state changes by:
-- - Grouping meshes with the same pipeline
-- - Generating commands in batch order
--
-- Also handles render state extraction and command generation.
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render.Batching
  ( -- Render state
    RenderState
  , extractRenderState
    -- Mesh batching
  , RenderBatch
  , batchByMaterial
    -- Command generation
  , generateRenderCommands
  , generateShadowCommands
  , generatePickCommands
  ) where

import Prelude
  ( class Eq
  , map
  , (+)
  , (/)
  , (<>)
  , (==)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.Scene3D.Background
  ( Background3D
      ( SolidBackground
      , GradientBackground
      , EnvironmentBackground
      )
  )
import Hydrogen.GPU.Scene3D.Core (Scene3D)
import Hydrogen.GPU.Scene3D.Mesh (MeshParams)
import Hydrogen.GPU.WebGPU.Pipeline
  ( PipelineKey
  , pipelineKeyFromMaterial
  )
import Hydrogen.GPU.WebGPU.Scene3D.Geometry (MeshData, generateMesh)
import Hydrogen.GPU.WebGPU.Scene3D.Render.Commands
  ( RenderCommand
      ( ClearCommand
      , SetPipelineCommand
      , SetBindGroupCommand
      , SetVertexBufferCommand
      , SetIndexBufferCommand
      , DrawIndexedCommand
      )
  , BufferRef(BufferRef)
  , IndexFormat(Uint16)
  )
import Hydrogen.GPU.WebGPU.Scene3D.Render.Uniforms
  ( FrameUniforms
  , LightUniforms
  , computeFrameUniforms
  , computeLightUniforms
  , computeObjectUniforms
  , computeMaterialUniforms
  , frameUniformsToBindGroup
  , lightUniformsToBindGroup
  , objectUniformsToBindGroup
  , materialUniformsToBindGroup
  )
import Hydrogen.Schema.Color.RGB (RGBA, rgbaToRecord)
import Hydrogen.Schema.Dimension.Vector.Vec4 (Vec4, vec4)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER STATE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Render state extracted from Scene3D.
-- | Contains computed matrices and sorted/batched meshes.
type RenderState msg =
  { frameUniforms :: FrameUniforms
  , lightUniforms :: LightUniforms
  , batches :: Array (RenderBatch msg)
  , clearColor :: Vec4 Number
  , skybox :: Maybe Int  -- Skybox texture ID if present
  }

-- | Extract render state from a Scene3D.
extractRenderState :: forall msg. Scene3D msg -> RenderState msg
extractRenderState scene =
  { frameUniforms: computeFrameUniforms scene.camera
  , lightUniforms: computeLightUniforms scene.lights
  , batches: batchByMaterial scene.meshes
  , clearColor: backgroundToClearColor scene.background
  , skybox: backgroundToSkybox scene.background
  }

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- RENDER BATCHING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | A render batch groups meshes by pipeline.
-- | Same pipeline = one state change, multiple draw calls.
type RenderBatch msg =
  { pipelineKey :: PipelineKey
  , meshes :: Array (MeshParams msg)
  }

-- | Batch meshes by material (same material = same pipeline).
batchByMaterial :: forall msg. Array (MeshParams msg) -> Array (RenderBatch msg)
batchByMaterial meshes =
  let
    -- Group by pipeline key
    grouped = groupBy (\m -> pipelineKeyFromMaterial m.material) meshes
  in
    map (\{ key, items } -> { pipelineKey: key, meshes: items }) grouped

-- Simple groupBy implementation
groupBy :: forall a k. Eq k => (a -> k) -> Array a -> Array { key :: k, items :: Array a }
groupBy keyFn arr = foldl insertItem [] arr
  where
    insertItem groups item =
      let key = keyFn item
      in case findGroup key groups of
        Just idx -> updateAt idx (\g -> g { items = Array.snoc g.items item }) groups
        Nothing -> Array.snoc groups { key, items: [item] }
    
    findGroup :: k -> Array { key :: k, items :: Array a } -> Maybe Int
    findGroup k groups = findIndex (\g -> g.key == k) groups
    
    findIndex :: forall b. (b -> Boolean) -> Array b -> Maybe Int
    findIndex pred xs = go 0 xs
      where
        go _ [] = Nothing
        go i arr' = case Array.head arr' of
          Nothing -> Nothing
          Just x -> if pred x then Just i else go (i + 1) (Array.drop 1 arr')
    
    updateAt :: forall b. Int -> (b -> b) -> Array b -> Array b
    updateAt idx f xs = case Array.index xs idx of
      Nothing -> xs
      Just x -> case Array.updateAt idx (f x) xs of
        Nothing -> xs
        Just updated -> updated

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- COMMAND GENERATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Generate render commands from Scene3D.
generateRenderCommands :: forall msg. Scene3D msg -> Array RenderCommand
generateRenderCommands scene =
  let
    state = extractRenderState scene
    clearCmd = ClearCommand
      { color: state.clearColor
      , depth: 1.0
      , stencil: 0
      }
    batchCmds = Array.concatMap (generateBatchCommands state) state.batches
  in
    [clearCmd] <> batchCmds

-- | Generate commands for a single batch.
generateBatchCommands :: forall msg. RenderState msg -> RenderBatch msg -> Array RenderCommand
generateBatchCommands state batch =
  let
    pipelineCmd = SetPipelineCommand batch.pipelineKey
    frameBindCmd = SetBindGroupCommand 0 (frameUniformsToBindGroup state.frameUniforms)
    lightBindCmd = SetBindGroupCommand 3 (lightUniformsToBindGroup state.lightUniforms)
    meshCmds = Array.concatMap (generateMeshCommands state) batch.meshes
  in
    [pipelineCmd, frameBindCmd, lightBindCmd] <> meshCmds

-- | Generate commands for a single mesh.
generateMeshCommands :: forall msg. RenderState msg -> MeshParams msg -> Array RenderCommand
generateMeshCommands _state mesh =
  let
    objectUniforms = computeObjectUniforms mesh
    materialUniforms = computeMaterialUniforms mesh.material
    
    -- Generate geometry data from mesh descriptor
    meshData :: MeshData
    meshData = generateMesh mesh.geometry
    
    materialBindCmd = SetBindGroupCommand 1 (materialUniformsToBindGroup materialUniforms)
    objectBindCmd = SetBindGroupCommand 2 (objectUniformsToBindGroup objectUniforms)
    vertexCmd = SetVertexBufferCommand 0 (BufferRef 0)  -- Runtime resolves
    indexCmd = SetIndexBufferCommand (BufferRef 0) Uint16
    drawCmd = DrawIndexedCommand
      { indexCount: Array.length meshData.indices
      , instanceCount: 1
      , firstIndex: 0
      , baseVertex: 0
      , firstInstance: 0
      }
  in
    [materialBindCmd, objectBindCmd, vertexCmd, indexCmd, drawCmd]

-- | Generate shadow pass commands.
generateShadowCommands :: forall msg. Scene3D msg -> Array RenderCommand
generateShadowCommands _scene =
  -- Shadow pass uses depth-only pipeline
  -- For each shadow-casting light, render all meshes from light's POV
  []  -- Implement when shadow mapping is needed

-- | Generate pick pass commands.
generatePickCommands :: forall msg. Scene3D msg -> Array RenderCommand
generatePickCommands _scene =
  -- Pick pass uses pick pipeline, outputs object IDs
  []  -- Implement when picking is needed

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

backgroundToClearColor :: Background3D -> Vec4 Number
backgroundToClearColor = case _ of
  SolidBackground color -> rgbaToVec4 color
  GradientBackground topColor _ _ -> rgbaToVec4 topColor
  EnvironmentBackground _ -> vec4 0.0 0.0 0.0 1.0  -- Environment map renders over clear

backgroundToSkybox :: Background3D -> Maybe Int
backgroundToSkybox = case _ of
  EnvironmentBackground envMap -> Just envMap.cubeMapId
  _ -> Nothing

rgbaToVec4 :: RGBA -> Vec4 Number
rgbaToVec4 color =
  let c = rgbaToRecord color
  in vec4 
    (toNumber c.r / 255.0) 
    (toNumber c.g / 255.0) 
    (toNumber c.b / 255.0) 
    (toNumber c.a / 255.0)
