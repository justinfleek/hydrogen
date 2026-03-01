-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // gpu // webgpu // scene3d // render // culling
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--
-- Culling and Sorting — Visibility determination and render order.
--
-- Provides:
-- - Frustum culling (remove meshes outside view frustum)
-- - Depth sorting (back-to-front for transparency)
--
-- NO MUTATION. NO FFI IN THIS MODULE. PURE FUNCTIONS ONLY.
--
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

module Hydrogen.GPU.WebGPU.Scene3D.Render.Culling
  ( -- Culling
    frustumCull
    -- Sorting
  , sortByDepth
  ) where

import Prelude
  ( Ordering(LT, GT, EQ)
  , negate
  , ($)
  , (*)
  , (+)
  , (-)
  , (<)
  , (>)
  , (>=)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.GPU.Scene3D.Mesh (MeshParams)
import Hydrogen.GPU.Scene3D.Position (Position3D, positionToMeters)
import Hydrogen.GPU.WebGPU.Scene3D.Render.Uniforms (FrameUniforms)
import Hydrogen.Schema.Dimension.Matrix.Mat4 (toArray16)
import Hydrogen.Schema.Dimension.Vector.Vec3 (Vec3, vec3, getX3, getY3, getZ3)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- DEPTH SORTING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sort meshes by depth (back to front for transparency).
sortByDepth :: forall msg. Vec3 Number -> Array (MeshParams msg) -> Array (MeshParams msg)
sortByDepth cameraPos meshes =
  Array.sortBy compareDepth meshes
  where
    compareDepth a b =
      let
        distA = distanceSquared cameraPos (unwrapPosition3D a.position)
        distB = distanceSquared cameraPos (unwrapPosition3D b.position)
      in
        -- Sort far to near for correct alpha blending
        if distA > distB then LT else if distA < distB then GT else EQ
    
    distanceSquared p1 p2 =
      let
        dx = vecX p1 - vecX p2
        dy = vecY p1 - vecY p2
        dz = vecZ p1 - vecZ p2
      in
        dx * dx + dy * dy + dz * dz

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- FRUSTUM CULLING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Frustum cull meshes (remove meshes outside view frustum).
-- |
-- | Tests mesh center against near/far planes using camera depth.
-- | Full implementation would extract 6 frustum planes from viewProjection.
frustumCull :: forall msg. FrameUniforms -> Array (MeshParams msg) -> Array (MeshParams msg)
frustumCull frameUniforms meshes =
  Array.filter (isInFrustum frameUniforms) meshes

-- | Test if mesh center is within frustum depth range.
isInFrustum :: forall msg. FrameUniforms -> MeshParams msg -> Boolean
isInFrustum frameUniforms mesh =
  let
    -- Get mesh position in world space
    meshPos = unwrapPosition3D mesh.position
    meshX = vecX meshPos
    meshY = vecY meshPos  
    meshZ = vecZ meshPos
    
    -- Transform to view space using view matrix
    viewMat = frameUniforms.viewMatrix
    viewArr = toArray16 viewMat
    
    -- Manual transform: viewZ = row 2 dot (meshX, meshY, meshZ, 1)
    -- View space Z (negated because camera looks down -Z)
    viewZ = negate $ 
      getViewElement viewArr 2 * meshX +
      getViewElement viewArr 6 * meshY +
      getViewElement viewArr 10 * meshZ +
      getViewElement viewArr 14
    
    -- Check against near/far (approximate - assumes reasonable bounding sphere)
    boundingRadius = 10.0  -- Conservative estimate; real impl would compute from mesh
  in
    viewZ + boundingRadius >= 0.1 -- Near plane check
    
-- | Get element from 16-element matrix array.
getViewElement :: Array Number -> Int -> Number
getViewElement arr idx = 
  case Array.index arr idx of
    Just n -> n
    Nothing -> 0.0

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- UTILITY FUNCTIONS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- Vec3 accessors
vecX :: Vec3 Number -> Number
vecX = getX3

vecY :: Vec3 Number -> Number
vecY = getY3

vecZ :: Vec3 Number -> Number
vecZ = getZ3

-- Position unwrap helper
unwrapPosition3D :: Position3D -> Vec3 Number
unwrapPosition3D pos =
  let m = positionToMeters pos
  in vec3 m.x m.y m.z
