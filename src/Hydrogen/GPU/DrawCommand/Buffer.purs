-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // gpu // draw // buffer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand.Buffer — Command Buffer Operations
-- |
-- | This module provides operations for working with command buffers:
-- | - Creating empty and singleton buffers
-- | - Appending and concatenating buffers
-- | - Adding pick IDs for hit testing
-- | - Validation utilities
-- |
-- | Command buffers are the unit of work passed to the GPU interpreter.

module Hydrogen.GPU.DrawCommand.Buffer
  ( -- * Buffer Creation
    emptyBuffer
  , singleton
  
  -- * Buffer Operations
  , append
  , concat
  , withPickId
  
  -- * Validation
  , validateBuffer
  ) where

import Prelude (Unit, unit)
import Data.Array as Array
import Data.Maybe (Maybe(Just))
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
  , PickId
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // buffer creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty command buffer.
emptyBuffer :: forall msg. CommandBuffer msg
emptyBuffer = []

-- | Single-command buffer.
singleton :: forall msg. DrawCommand msg -> CommandBuffer msg
singleton cmd = [cmd]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // buffer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Append a command to a buffer.
append :: forall msg. DrawCommand msg -> CommandBuffer msg -> CommandBuffer msg
append cmd buf = Array.snoc buf cmd

-- | Concatenate command buffers.
concat :: forall msg. Array (CommandBuffer msg) -> CommandBuffer msg
concat = Array.concat

-- | Add a pick ID to a command for hit testing.
-- |
-- | The pick buffer renders each interactive element with its pick ID
-- | as the pixel value. On interaction, we read the pixel at cursor
-- | position and look up the corresponding message.
withPickId :: forall msg. PickId -> DrawCommand msg -> DrawCommand msg
withPickId pid cmd = case cmd of
  DrawRect p -> DrawRect (p { pickId = Just pid })
  DrawQuad p -> DrawQuad (p { pickId = Just pid })
  DrawGlyph p -> DrawGlyph (p { pickId = Just pid })
  DrawPath p -> DrawPath (p { pickId = Just pid })
  DrawParticle p -> DrawParticle (p { pickId = Just pid })
  -- Media commands
  DrawImage p -> DrawImage (p { pickId = Just pid })
  DrawVideo p -> DrawVideo (p { pickId = Just pid })
  Draw3D p -> Draw3D (p { pickId = Just pid })
  -- v2 typography commands
  DrawGlyphPath p -> DrawGlyphPath (p { pickId = Just pid })
  DrawGlyphInstance p -> DrawGlyphInstance (p { pickId = Just pid })
  DrawWord p -> DrawWord (p { pickId = Just pid })
  -- Non-interactive commands pass through unchanged
  DefinePathData pd -> DefinePathData pd
  UpdateAnimationState as -> UpdateAnimationState as
  PushClip c -> PushClip c
  PopClip -> PopClip
  Noop -> Noop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validate a command buffer, returning Unit.
-- |
-- | Currently performs no-op validation (all buffers are valid by construction
-- | due to the type system). This function exists for:
-- | 1. Future invariant checking (e.g., clip push/pop balance)
-- | 2. Integration with effect pipelines that expect Unit
-- | 3. Explicit documentation that validation was considered
validateBuffer :: forall msg. CommandBuffer msg -> Unit
validateBuffer _buf = unit
