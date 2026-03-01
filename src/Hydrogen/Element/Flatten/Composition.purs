-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // flatten // composition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition flattening: Group, Transform → DrawCommand.
-- |
-- | ## Purpose
-- |
-- | Handles composite elements that contain other elements.
-- | Groups flatten children sequentially with state threading.
-- | Transforms apply coordinate transformations (partial support).
-- |
-- | ## State Threading
-- |
-- | When flattening children, state (pickId, depth) must be threaded
-- | through to ensure consistent ordering and unique identifiers.

module Hydrogen.Element.Flatten.Composition
  ( flattenGroup
  , flattenTransform
  , flattenChildren
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- Element.Core
import Hydrogen.Element.Core
  ( Element
  , GroupSpec
  , TransformSpec
  )

-- GPU primitives
import Hydrogen.GPU.DrawCommand (DrawCommand)

-- Local types and helpers
import Hydrogen.Element.Flatten.Types (FlattenState, FlattenResult)
import Hydrogen.Element.Flatten.Helpers (arrayUncons)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // group
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Group element by recursively flattening children.
-- |
-- | Children are flattened in order, with state threading through
-- | to ensure pickIds and depth values are consistent.
flattenGroup :: forall msg. (FlattenState -> Element -> FlattenResult msg) -> FlattenState -> GroupSpec -> FlattenResult msg
flattenGroup flattenWithState state spec =
  let
    -- Thread state through all children
    result = flattenChildren flattenWithState state spec.children
  in
    result

-- | Recursively flatten an array of children.
flattenChildren :: forall msg. (FlattenState -> Element -> FlattenResult msg) -> FlattenState -> Array Element -> FlattenResult msg
flattenChildren flattenWithState state children =
  foldlChildren state [] children
  where
    foldlChildren :: FlattenState -> Array (DrawCommand msg) -> Array Element -> FlattenResult msg
    foldlChildren s acc [] = { commands: acc, state: s }
    foldlChildren s acc elems = case arrayUncons elems of
      Nothing -> { commands: acc, state: s }
      Just { head, tail } ->
        let result = flattenWithState s head
        in foldlChildren result.state (acc <> result.commands) tail

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // transform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Transform element by wrapping child in clip/transform commands.
-- |
-- | Note: Full transform support requires GPU-level transform matrices.
-- | For now, transforms are applied during coordinate conversion.
-- | Complex transforms (rotation, skew) would need DrawCommand extensions.
flattenTransform :: forall msg. (FlattenState -> Element -> FlattenResult msg) -> FlattenState -> TransformSpec -> FlattenResult msg
flattenTransform flattenWithState state spec =
  -- For now, flatten the child directly
  -- Full transform support would apply the transform matrix here
  -- and potentially emit PushTransform/PopTransform commands
  flattenWithState state spec.child
