-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // draw // batching
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand.Batching — Sorting and Batching for GPU Dispatch
-- |
-- | This module provides operations for preparing command buffers for
-- | efficient GPU dispatch:
-- | - Depth sorting (painter's algorithm for 2D)
-- | - Material batching (minimize state changes)
-- | - Depth comparison utilities
-- |
-- | The interpreter uses these to optimize draw call count.

module Hydrogen.GPU.DrawCommand.Batching
  ( -- * Depth Operations
    sortByDepth
  , compareDepth
  , getDepth
  
  -- * Material Batching
  , batchByMaterial
  , MaterialKey(MaterialSolid, MaterialTextured, MaterialClip, MaterialTypography, MaterialMeta)
  , getMaterial
  ) where

import Prelude
  ( class Eq
  , class Ord
  , Ordering
  , compare
  , map
  , (==)
  )

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Ord (comparing)
import Hydrogen.GPU.Coordinates as Coord
import Hydrogen.GPU.DrawCommand.Types
  ( DrawCommand
      ( DrawRect
      , DrawQuad
      , DrawGlyph
      , DrawPath
      , DrawParticle
      , DrawImage
      , DrawVideo
      , Draw3D
      , DrawScene3D
      , PushClip
      , PopClip
      , Noop
      , DrawGlyphPath
      , DrawGlyphInstance
      , DrawWord
      , DefinePathData
      , UpdateAnimationState
      )
  , CommandBuffer
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // depth operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract depth from a command for sorting.
-- |
-- | Returns the underlying Number from bounded DepthValue types.
-- | Non-rendering commands return 0.0.
getDepth :: forall msg. DrawCommand msg -> Number
getDepth = case _ of
  DrawRect p -> Coord.unwrapDepthValue p.depth
  DrawQuad p -> Coord.unwrapDepthValue p.depth
  DrawGlyph p -> Coord.unwrapDepthValue p.depth
  DrawPath p -> Coord.unwrapDepthValue p.depth
  DrawParticle p -> Coord.unwrapDepthValue p.z
  -- Media commands
  DrawImage p -> Coord.unwrapDepthValue p.depth
  DrawVideo p -> Coord.unwrapDepthValue p.depth
  Draw3D p -> Coord.unwrapDepthValue p.depth
  DrawScene3D p -> Coord.unwrapDepthValue p.depth
  PushClip _ -> 0.0
  PopClip -> 0.0
  Noop -> 0.0
  -- v2 typography commands
  DrawGlyphPath p -> Coord.unwrapDepthValue p.depth
  DrawGlyphInstance p -> Coord.unwrapDepthValue p.depth
  DrawWord p -> Coord.unwrapDepthValue p.depth
  DefinePathData _ -> 0.0
  UpdateAnimationState _ -> 0.0

-- | Sort commands by depth (painter's algorithm for 2D).
-- |
-- | Lower depth draws first (is behind). For WebGPU with depth buffer,
-- | sorting is optional but helps reduce overdraw.
sortByDepth :: forall msg. CommandBuffer msg -> CommandBuffer msg
sortByDepth = Array.sortBy (comparing getDepth)

-- | Compare two commands by their depth values.
-- |
-- | Returns Ordering (LT, EQ, GT) based on depth comparison.
-- | Useful for custom sorting strategies or priority queues.
compareDepth :: forall msg. DrawCommand msg -> DrawCommand msg -> Ordering
compareDepth a b = compare (getDepth a) (getDepth b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // material batching
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material key for batching.
-- |
-- | Commands with the same material can be drawn together.
-- | Currently simplified — real batching would consider texture atlas pages,
-- | blend modes, etc.
data MaterialKey
  = MaterialSolid
  | MaterialTextured Int  -- texture/atlas ID
  | MaterialClip
  | MaterialTypography Int  -- fontId for v2 typography geometry
  | MaterialMeta           -- Non-rendering commands (define, update)

derive instance eqMaterialKey :: Eq MaterialKey
derive instance ordMaterialKey :: Ord MaterialKey

-- | Get material key from command.
getMaterial :: forall msg. DrawCommand msg -> MaterialKey
getMaterial = case _ of
  DrawRect _ -> MaterialSolid
  DrawQuad _ -> MaterialSolid
  DrawGlyph p -> MaterialTextured p.fontId
  DrawPath _ -> MaterialSolid
  DrawParticle _ -> MaterialSolid
  -- Media commands: textured materials
  DrawImage _ -> MaterialTextured 0
  DrawVideo _ -> MaterialTextured 0
  Draw3D _ -> MaterialTextured 0
  DrawScene3D _ -> MaterialTextured 0  -- 3D scene is textured
  PushClip _ -> MaterialClip
  PopClip -> MaterialClip
  Noop -> MaterialSolid
  -- v2 typography commands
  DrawGlyphPath p -> MaterialTypography p.fontId
  DrawGlyphInstance _ -> MaterialSolid
  DrawWord _ -> MaterialSolid
  DefinePathData _ -> MaterialMeta
  UpdateAnimationState _ -> MaterialMeta

-- | Group commands by material for batched rendering.
-- |
-- | Returns array of batches, each batch can be drawn with a single
-- | state change. Order within batches preserves original depth order.
batchByMaterial :: forall msg. CommandBuffer msg -> Array (CommandBuffer msg)
batchByMaterial buf =
  let sorted = sortByDepth buf
      grouped = Array.groupBy (\a b -> getMaterial a == getMaterial b) sorted
  in map NEA.toArray grouped
