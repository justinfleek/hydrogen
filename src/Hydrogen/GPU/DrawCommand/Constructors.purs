-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // gpu // draw // constructors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DrawCommand.Constructors — Command Constructor Functions
-- |
-- | This module provides constructor functions that wrap parameters into
-- | DrawCommand values. These are the functions used by the flattener and
-- | by advanced code that constructs command buffers directly.
-- |
-- | Most application code uses Elements, not DrawCommands directly.

module Hydrogen.GPU.DrawCommand.Constructors
  ( -- * v1 Command Constructors
    drawRect
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
  
  -- * v2 Typography Command Constructors
  , drawGlyphPath
  , drawGlyphInstance
  , drawWord
  , definePathData
  , updateAnimationState
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
  , RectParams
  , QuadParams
  , GlyphParams
  , PathParams
  , ParticleParams
  , ImageParams
  , VideoParams
  , Model3DParams
  , ClipRegion
  , GlyphPathParams
  , GlyphInstanceParams
  , WordParams
  , PathDataParams
  , AnimationStateParams
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // v1 command constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Draw a rectangle.
drawRect :: forall msg. RectParams msg -> DrawCommand msg
drawRect = DrawRect

-- | Draw a quadrilateral.
drawQuad :: forall msg. QuadParams msg -> DrawCommand msg
drawQuad = DrawQuad

-- | Draw a text glyph.
drawGlyph :: forall msg. GlyphParams msg -> DrawCommand msg
drawGlyph = DrawGlyph

-- | Draw a vector path.
drawPath :: forall msg. PathParams msg -> DrawCommand msg
drawPath = DrawPath

-- | Draw a particle.
drawParticle :: forall msg. ParticleParams msg -> DrawCommand msg
drawParticle = DrawParticle

-- | Draw an image.
drawImage :: forall msg. ImageParams msg -> DrawCommand msg
drawImage = DrawImage

-- | Draw a video frame.
drawVideo :: forall msg. VideoParams msg -> DrawCommand msg
drawVideo = DrawVideo

-- | Draw a 3D model.
draw3D :: forall msg. Model3DParams msg -> DrawCommand msg
draw3D = Draw3D

-- | Push a clipping region onto the clip stack.
pushClip :: forall msg. ClipRegion -> DrawCommand msg
pushClip = PushClip

-- | Pop the current clipping region.
popClip :: forall msg. DrawCommand msg
popClip = PopClip

-- | No operation. Useful as identity element.
noop :: forall msg. DrawCommand msg
noop = Noop

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // v2 command constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Draw a glyph as vector bezier paths (typography as geometry).
drawGlyphPath :: forall msg. GlyphPathParams msg -> DrawCommand msg
drawGlyphPath = DrawGlyphPath

-- | Draw an animated glyph instance referencing shared path data.
drawGlyphInstance :: forall msg. GlyphInstanceParams msg -> DrawCommand msg
drawGlyphInstance = DrawGlyphInstance

-- | Draw a word (collection of glyphs with shared animation state).
drawWord :: forall msg. WordParams msg -> DrawCommand msg
drawWord = DrawWord

-- | Define shared path data for instancing.
definePathData :: forall msg. PathDataParams -> DrawCommand msg
definePathData = DefinePathData

-- | Update animation state for targets.
updateAnimationState :: forall msg. AnimationStateParams -> DrawCommand msg
updateAnimationState = UpdateAnimationState
