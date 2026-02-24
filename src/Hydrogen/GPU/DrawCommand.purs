-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // gpu // draw
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
  ( -- * Core Types
    DrawCommand(..)
  , CommandBuffer
  , PickId
  , pickId
  , unwrapPickId
  
  -- * Rect Parameters
  , RectParams
  , rectParams
  
  -- * Quad Parameters (arbitrary 4-point)
  , Point2D
  , QuadParams
  , quadParams
  
  -- * Glyph Parameters (SDF text)
  , GlyphParams
  , glyphParams
  
  -- * Path Parameters (vector paths)
  , PathParams
  , PathSegment(..)
  , pathParams
  
  -- * Particle Parameters (billion-agent viz)
  , ParticleParams
  , particleParams
  
  -- * Clip Operations
  , ClipRegion(..)
  
  -- * Command Constructors
  , drawRect
  , drawQuad
  , drawGlyph
  , drawPath
  , drawParticle
  , pushClip
  , popClip
  , noop
  
  -- * CommandBuffer Operations
  , emptyBuffer
  , singleton
  , append
  , concat
  , withPickId
  
  -- * Sorting & Batching (for interpreter)
  , sortByDepth
  , batchByMaterial
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , compare
  , map
  , show
  , unit
  , (<>)
  , (==)
  )

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(Nothing, Just))
import Data.Ord (comparing)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for pick buffer hit testing.
-- | When an interaction occurs, the pick buffer pixel value maps back to this ID.
-- | The interpreter maintains a Map PickId msg for dispatching.
newtype PickId = PickId Int

derive instance eqPickId :: Eq PickId
derive instance ordPickId :: Ord PickId

instance showPickId :: Show PickId where
  show (PickId n) = "PickId(" <> show n <> ")"

-- | Create a PickId from an Int.
pickId :: Int -> PickId
pickId = PickId

-- | Unwrap a PickId to its Int value.
unwrapPickId :: PickId -> Int
unwrapPickId (PickId n) = n

-- | A draw command — single GPU primitive operation.
-- |
-- | The `msg` type parameter carries the message to dispatch when this
-- | element is interacted with (via pick buffer).
data DrawCommand msg
  = DrawRect (RectParams msg)
  | DrawQuad (QuadParams msg)
  | DrawGlyph (GlyphParams msg)
  | DrawPath (PathParams msg)
  | DrawParticle (ParticleParams msg)
  | PushClip ClipRegion
  | PopClip
  | Noop

-- | A command buffer — array of commands ready for GPU dispatch.
-- | This is the unit of work passed to the interpreter.
type CommandBuffer msg = Array (DrawCommand msg)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // rect parameters
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a rectangle.
-- |
-- | Rectangles are the most common primitive. Rounded corners are handled
-- | via SDF in the shader — no extra geometry needed.
type RectParams msg =
  { x :: Device.Pixel           -- Left edge
  , y :: Device.Pixel           -- Top edge
  , width :: Device.Pixel       -- Width
  , height :: Device.Pixel      -- Height
  , fill :: RGB.RGBA            -- Fill color with alpha
  , cornerRadius :: Radius.Corners  -- Per-corner radius
  , depth :: Number             -- Z-order (higher = on top)
  , pickId :: Maybe PickId      -- For hit testing (Nothing = not interactive)
  , onClick :: Maybe msg        -- Message on click
  }

-- | Create rectangle parameters with defaults.
rectParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Device.Pixel       -- width
  -> Device.Pixel       -- height
  -> RGB.RGBA           -- fill
  -> RectParams msg
rectParams x y width height fill =
  { x
  , y
  , width
  , height
  , fill
  , cornerRadius: Radius.cornersAll Radius.none
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // quad parameters
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A 2D point for quad vertices.
type Point2D =
  { x :: Device.Pixel
  , y :: Device.Pixel
  }

-- | Parameters for drawing an arbitrary quadrilateral.
-- |
-- | Four vertices in clockwise order. More flexible than rect but
-- | requires 4 points. Used for skewed/transformed shapes.
type QuadParams msg =
  { v0 :: Point2D               -- Top-left
  , v1 :: Point2D               -- Top-right
  , v2 :: Point2D               -- Bottom-right
  , v3 :: Point2D               -- Bottom-left
  , fill :: RGB.RGBA
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Create quad parameters.
quadParams
  :: forall msg
   . Point2D -> Point2D -> Point2D -> Point2D
  -> RGB.RGBA
  -> QuadParams msg
quadParams v0 v1 v2 v3 fill =
  { v0, v1, v2, v3
  , fill
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // glyph parameters
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a single glyph using SDF rendering.
-- |
-- | Text is rendered as a sequence of glyph quads. Each glyph references
-- | a position in the font atlas and has its own transform.
-- |
-- | The font atlas and SDF textures are managed by the interpreter.
type GlyphParams msg =
  { x :: Device.Pixel           -- Glyph origin X
  , y :: Device.Pixel           -- Glyph origin Y (baseline)
  , glyphIndex :: Int           -- Index into font atlas
  , fontId :: Int               -- Which font (interpreter manages font registry)
  , fontSize :: Device.Pixel    -- Rendered size
  , color :: RGB.RGBA           -- Text color
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Create glyph parameters.
glyphParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Int                -- glyphIndex
  -> Int                -- fontId
  -> Device.Pixel       -- fontSize
  -> RGB.RGBA           -- color
  -> GlyphParams msg
glyphParams x y glyphIndex fontId fontSize color =
  { x, y, glyphIndex, fontId, fontSize, color
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // path parameters
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Path segment types for vector graphics.
data PathSegment
  = MoveTo Point2D
  | LineTo Point2D
  | QuadraticTo Point2D Point2D           -- control, end
  | CubicTo Point2D Point2D Point2D       -- c1, c2, end
  | ClosePath

derive instance eqPathSegment :: Eq PathSegment

-- | Parameters for drawing a vector path.
-- |
-- | Paths are tessellated to triangles by the interpreter. Complex paths
-- | may have significant vertex counts.
type PathParams msg =
  { segments :: Array PathSegment
  , fill :: Maybe RGB.RGBA      -- Fill color (Nothing = no fill)
  , stroke :: Maybe RGB.RGBA    -- Stroke color (Nothing = no stroke)
  , strokeWidth :: Device.Pixel
  , depth :: Number
  , pickId :: Maybe PickId
  , onClick :: Maybe msg
  }

-- | Create path parameters.
pathParams
  :: forall msg
   . Array PathSegment
  -> PathParams msg
pathParams segments =
  { segments
  , fill: Nothing
  , stroke: Nothing
  , strokeWidth: Device.px 1.0
  , depth: 0.0
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // particle parameters
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parameters for drawing a particle.
-- |
-- | Particles are instanced — the GPU draws thousands with a single call.
-- | This is the primitive for billion-agent visualization.
-- |
-- | Each particle is a point sprite rendered as a quad facing the camera.
type ParticleParams msg =
  { x :: Device.Pixel
  , y :: Device.Pixel
  , z :: Number                 -- Depth (for 3D particle fields)
  , size :: Device.Pixel        -- Point size
  , color :: RGB.RGBA
  , pickId :: Maybe PickId      -- Can make individual particles interactive
  , onClick :: Maybe msg
  }

-- | Create particle parameters.
particleParams
  :: forall msg
   . Device.Pixel       -- x
  -> Device.Pixel       -- y
  -> Device.Pixel       -- size
  -> RGB.RGBA           -- color
  -> ParticleParams msg
particleParams x y size color =
  { x, y
  , z: 0.0
  , size
  , color
  , pickId: Nothing
  , onClick: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // clip operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Clip region for masking.
-- |
-- | Push a clip, draw commands, pop the clip. Uses stencil buffer.
data ClipRegion
  = ClipRect
      { x :: Device.Pixel
      , y :: Device.Pixel
      , width :: Device.Pixel
      , height :: Device.Pixel
      , cornerRadius :: Radius.Corners
      }
  | ClipPath (Array PathSegment)

derive instance eqClipRegion :: Eq ClipRegion

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // command constructors
-- ═══════════════════════════════════════════════════════════════════════════════

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

-- | Push a clipping region onto the clip stack.
pushClip :: forall msg. ClipRegion -> DrawCommand msg
pushClip = PushClip

-- | Pop the current clipping region.
popClip :: forall msg. DrawCommand msg
popClip = PopClip

-- | No operation. Useful as identity element.
noop :: forall msg. DrawCommand msg
noop = Noop

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                      // command buffer ops
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Empty command buffer.
emptyBuffer :: forall msg. CommandBuffer msg
emptyBuffer = []

-- | Single-command buffer.
singleton :: forall msg. DrawCommand msg -> CommandBuffer msg
singleton cmd = [cmd]

-- | Append a command to a buffer.
append :: forall msg. DrawCommand msg -> CommandBuffer msg -> CommandBuffer msg
append cmd buf = Array.snoc buf cmd

-- | Concatenate command buffers.
concat :: forall msg. Array (CommandBuffer msg) -> CommandBuffer msg
concat = Array.concat

-- | Add a pick ID to a command for hit testing.
withPickId :: forall msg. PickId -> DrawCommand msg -> DrawCommand msg
withPickId pid = case _ of
  DrawRect p -> DrawRect (p { pickId = Just pid })
  DrawQuad p -> DrawQuad (p { pickId = Just pid })
  DrawGlyph p -> DrawGlyph (p { pickId = Just pid })
  DrawPath p -> DrawPath (p { pickId = Just pid })
  DrawParticle p -> DrawParticle (p { pickId = Just pid })
  other -> other

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // sorting and batching
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extract depth from a command for sorting.
getDepth :: forall msg. DrawCommand msg -> Number
getDepth = case _ of
  DrawRect p -> p.depth
  DrawQuad p -> p.depth
  DrawGlyph p -> p.depth
  DrawPath p -> p.depth
  DrawParticle p -> p.z
  PushClip _ -> 0.0
  PopClip -> 0.0
  Noop -> 0.0

-- | Sort commands by depth (painter's algorithm for 2D).
-- |
-- | Lower depth draws first (is behind). For WebGPU with depth buffer,
-- | sorting is optional but helps reduce overdraw.
sortByDepth :: forall msg. CommandBuffer msg -> CommandBuffer msg
sortByDepth = Array.sortBy (comparing getDepth)

-- | Material key for batching.
-- |
-- | Commands with the same material can be drawn together.
-- | Currently simplified — real batching would consider texture atlas pages,
-- | blend modes, etc.
data MaterialKey
  = MaterialSolid
  | MaterialTextured Int  -- texture/atlas ID
  | MaterialClip

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
  PushClip _ -> MaterialClip
  PopClip -> MaterialClip
  Noop -> MaterialSolid

-- | Group commands by material for batched rendering.
-- |
-- | Returns array of batches, each batch can be drawn with a single
-- | state change. Order within batches preserves original depth order.
batchByMaterial :: forall msg. CommandBuffer msg -> Array (CommandBuffer msg)
batchByMaterial buf =
  let sorted = sortByDepth buf
      grouped = Array.groupBy (\a b -> getMaterial a == getMaterial b) sorted
  in map NEA.toArray grouped
