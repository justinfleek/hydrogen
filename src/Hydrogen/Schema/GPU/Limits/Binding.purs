-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gpu // limits // binding
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binding Limits — Bounded types for WebGPU bind group constraints.
-- |
-- | ## WebGPU Binding Model
-- |
-- | WebGPU uses a hierarchical binding model:
-- | - Bind groups contain bindings
-- | - Bindings reference resources (buffers, textures, samplers)
-- | - Shaders access resources via bind group and binding indices
-- |
-- | ## Limits
-- |
-- | - maxBindGroups: 4 (guaranteed minimum)
-- | - maxBindingsPerBindGroup: 1000 (guaranteed minimum)
-- |
-- | Reference: https://www.w3.org/TR/webgpu/#limits
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Bounded

module Hydrogen.Schema.GPU.Limits.Binding
  ( -- * Bind Group Count
    BindGroupCount
  , bindGroupCount
  , clampBindGroupCount
  , unwrapBindGroupCount
  , bindGroupCountBounds
  
  -- * Bindings Per Group
  , BindingsPerGroup
  , bindingsPerGroup
  , clampBindingsPerGroup
  , unwrapBindingsPerGroup
  , bindingsPerGroupBounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded
  ( BoundsBehavior(Clamps)
  , IntBounds
  , intBounds
  , clampInt
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // bind group count
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of bind groups.
-- |
-- | Bounds: 0 to 4 (WebGPU guaranteed minimum)
-- |
-- | Bind groups are the primary way to pass resources to shaders.
-- | The 4-group limit encourages organizing bindings by update frequency:
-- |
-- | - Group 0: Per-frame resources (view/projection matrices)
-- | - Group 1: Per-material resources (textures, material properties)
-- | - Group 2: Per-object resources (model matrix, instance data)
-- | - Group 3: Per-draw resources (dynamic uniforms)
newtype BindGroupCount = BindGroupCount Int

derive instance eqBindGroupCount :: Eq BindGroupCount
derive instance ordBindGroupCount :: Ord BindGroupCount

instance showBindGroupCount :: Show BindGroupCount where
  show (BindGroupCount n) = "BindGroups(" <> show n <> ")"

-- | Bounds specification for bind group count.
bindGroupCountBounds :: IntBounds
bindGroupCountBounds = intBounds 0 4 Clamps "bindGroupCount" "Bind group count (0-4)"

-- | Smart constructor with validation.
-- |
-- | Returns Nothing for values outside [0, 4].
bindGroupCount :: Int -> Maybe BindGroupCount
bindGroupCount n
  | n >= 0 && n <= 4 = Just (BindGroupCount n)
  | otherwise = Nothing

-- | Clamping constructor.
-- |
-- | Values below 0 become 0, values above 4 become 4.
clampBindGroupCount :: Int -> BindGroupCount
clampBindGroupCount n = BindGroupCount (clampInt 0 4 n)

-- | Extract the underlying Int value.
unwrapBindGroupCount :: BindGroupCount -> Int
unwrapBindGroupCount (BindGroupCount n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // bindings per group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bindings per bind group.
-- |
-- | Bounds: 0 to 1000 (WebGPU guaranteed minimum)
-- |
-- | Each binding within a group can reference:
-- | - Uniform buffers
-- | - Storage buffers
-- | - Textures
-- | - Samplers
-- | - External textures
-- |
-- | The high limit (1000) allows flexible resource organization,
-- | but practical pipelines typically use far fewer bindings.
newtype BindingsPerGroup = BindingsPerGroup Int

derive instance eqBindingsPerGroup :: Eq BindingsPerGroup
derive instance ordBindingsPerGroup :: Ord BindingsPerGroup

instance showBindingsPerGroup :: Show BindingsPerGroup where
  show (BindingsPerGroup n) = "BindingsPerGroup(" <> show n <> ")"

-- | Bounds specification for bindings per group.
bindingsPerGroupBounds :: IntBounds
bindingsPerGroupBounds = intBounds 0 1000 Clamps "bindingsPerGroup" "Bindings per group (0-1000)"

-- | Smart constructor with validation.
bindingsPerGroup :: Int -> Maybe BindingsPerGroup
bindingsPerGroup n
  | n >= 0 && n <= 1000 = Just (BindingsPerGroup n)
  | otherwise = Nothing

-- | Clamping constructor.
clampBindingsPerGroup :: Int -> BindingsPerGroup
clampBindingsPerGroup n = BindingsPerGroup (clampInt 0 1000 n)

-- | Extract the underlying Int value.
unwrapBindingsPerGroup :: BindingsPerGroup -> Int
unwrapBindingsPerGroup (BindingsPerGroup n) = n
