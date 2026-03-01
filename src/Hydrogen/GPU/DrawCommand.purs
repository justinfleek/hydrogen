-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // hydrogen // gpu // draw
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand — The GPU Primitive Vocabulary
-- |
-- | This module defines the complete set of GPU drawing operations. Every
-- | visual element in Hydrogen ultimately reduces to an array of DrawCommands.
-- |
-- | ## Design Principles
-- |
-- | 1. **Flat, not nested**: Arrays of commands, not trees. Trees require
-- |    traversal; arrays can be concatenated and batched.
-- |
-- | 2. **Immediate mode**: Each frame is a complete description. No retained
-- |    state, no diffing, no "what changed since last frame."
-- |
-- | 3. **Schema atoms only**: All parameters use bounded Schema types.
-- |    No strings, no CSS, no unbounded values.
-- |
-- | 4. **GPU-native**: Commands map directly to GPU operations. The interpreter
-- |    batches by material/texture and dispatches draw calls.
-- |
-- | 5. **Pick buffer ready**: Every interactive command carries an ID for
-- |    GPU-based hit testing via pick buffer.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Agent → Element → flatten → Array DrawCommand → interpret → WebGPU
-- |                                                          ↓
-- |                                               Array msg ← pick buffer
-- | ```
-- |
-- | At billion-agent scale, each agent emits its commands. The interpreter
-- | concatenates, sorts by material, and dispatches to GPU. No per-agent
-- | state synchronization required.
-- |
-- | ## Module Structure
-- |
-- | This leader module re-exports from submodules:
-- | - `DrawCommand.Types`: Core types (DrawCommand, PickId, parameter records)
-- | - `DrawCommand.Params`: v1 parameter constructors
-- | - `DrawCommand.Typography`: v2 typography parameter constructors
-- | - `DrawCommand.Constructors`: Command constructors
-- | - `DrawCommand.Buffer`: Buffer operations
-- | - `DrawCommand.Batching`: Sorting and batching
-- |
-- | ## Usage
-- |
-- | Components don't create DrawCommands directly — they create Element values.
-- | The flattener converts Element trees to DrawCommand arrays. This module
-- | is for the interpreter and advanced use cases.
-- |
-- | ```purescript
-- | import Hydrogen.GPU.DrawCommand as DC
-- |
-- | -- The interpreter receives these
-- | commands :: Array (DC.DrawCommand msg)
-- | commands =
-- |   [ DC.drawRect rectParams
-- |   , DC.drawGlyph glyphParams
-- |   ]
-- | ```

module Hydrogen.GPU.DrawCommand
  ( -- * Core Types (from Types)
    module Types
  
  -- * Parameter Constructors (from Params)
  , module Params
  
  -- * Typography Parameters (from Typography)
  , module Typography
  
  -- * Command Constructors (from Constructors)
  , module Constructors
  
  -- * CommandBuffer Operations (from Buffer)
  , module Buffer
  
  -- * Sorting & Batching (from Batching)
  , module Batching

  -- * Bounded Coordinate Types (re-exported)
  , module Coord
  ) where

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
  , pickId
  , unwrapPickId
  , Point2D
  , Point3D
  , RectParams
  , ImageParams
  , VideoParams
  , Model3DParams
  , QuadParams
  , GlyphParams
  , PathParams
  , PathSegment(MoveTo, LineTo, QuadraticTo, CubicTo, ClosePath)
  , ParticleParams
  , ClipRegion(ClipRect, ClipPath)
  , GlyphPathParams
  , ContourData
  , BoundingBox3D
  , GlyphInstanceParams
  , Rotation3D
  , Scale3D
  , SpringState
  , WordParams
  , StaggerConfig
  , StaggerDirection
  , EasingFunction
  , PathDataParams
  , AnimationStateParams
  , AnimationUpdateMode(AnimationReplace, AnimationAdditive, AnimationBlend)
  , AnimationTarget
  , TargetType(TargetGlyphInstance, TargetWord, TargetPathData, TargetControlPoint)
  , ColorDelta
  ) as Types

import Hydrogen.GPU.DrawCommand.Params
  ( rectParams
  , imageParams
  , videoParams
  , model3DParams
  , quadParams
  , glyphParams
  , pathParams
  , particleParams
  ) as Params

import Hydrogen.GPU.DrawCommand.Typography
  ( glyphPathParams
  , glyphInstanceParams
  , wordParams
  , pathDataParams
  , animationStateParams
  , staggerLeftToRight
  , staggerRightToLeft
  , staggerCenterOut
  , staggerEdgesIn
  , staggerTopToBottom
  , staggerBottomToTop
  , staggerRandom
  , easeLinear
  , easeInQuad
  , easeOutQuad
  , easeInOutQuad
  , easeInCubic
  , easeOutCubic
  , easeInOutCubic
  , easeInElastic
  , easeOutElastic
  , easeInOutElastic
  , easeInBounce
  , easeOutBounce
  , easeSpring
  ) as Typography

import Hydrogen.GPU.DrawCommand.Constructors
  ( drawRect
  , drawQuad
  , drawGlyph
  , drawPath
  , drawParticle
  , drawImage
  , drawVideo
  , draw3D
  , pushClip
  , popClip
  , noop
  , drawGlyphPath
  , drawGlyphInstance
  , drawWord
  , definePathData
  , updateAnimationState
  ) as Constructors

import Hydrogen.GPU.DrawCommand.Buffer
  ( emptyBuffer
  , singleton
  , append
  , concat
  , withPickId
  , validateBuffer
  ) as Buffer

import Hydrogen.GPU.DrawCommand.Batching
  ( sortByDepth
  , batchByMaterial
  , compareDepth
  ) as Batching

import Hydrogen.GPU.Coordinates as Coord
