-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // flatten
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element.Core → DrawCommand Flattener
-- |
-- | Converts the pure-data Element type to GPU DrawCommands.
-- | This is the bridge between the correct Element (Schema atoms)
-- | and the GPU execution layer.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Element (pure data, Schema atoms)
-- |     ↓ flatten
-- | Array (DrawCommand msg)
-- |     ↓ interpret
-- | WebGPU execution
-- | ```
-- |
-- | ## Agent Identity
-- |
-- | Every Element can carry an AgentId. The flatten process preserves
-- | this identity through PickId assignment, enabling:
-- | - Click a pixel → PickId → AgentId → full agent state
-- | - Spatial index integration
-- | - Agent-level hit testing
-- |
-- | ## Coordinate System
-- |
-- | Element uses center-based coordinates (RectangleShape.center).
-- | DrawCommand uses top-left corner coordinates (RectParams.x, y).
-- | This module handles the conversion.
-- |
-- | ## Module Structure
-- |
-- | - Flatten.Types: Core types (FlattenState, FlattenResult)
-- | - Flatten.Helpers: Conversion utilities
-- | - Flatten.Shape: Rectangle, Ellipse, Path
-- | - Flatten.Text: Text and glyph rendering
-- | - Flatten.Media: Image, Video, Audio, Model3D
-- | - Flatten.Composition: Group, Transform
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Element.Core (the correct Element type)
-- | - Hydrogen.GPU.DrawCommand (GPU primitives)
-- | - Hydrogen.Schema.* (bounded atoms)

module Hydrogen.Element.Flatten
  ( -- * Types (re-exported from Flatten.Types)
    module Hydrogen.Element.Flatten.Types
  
  -- * Flattening
  , flatten
  , flattenWithState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- Element.Core: the correct Element type
import Hydrogen.Element.Core
  ( Element(Rectangle, Ellipse, Path, Polygon, Star, Ring, Spiral, Arrow, Cross, Gear, Line, Text, Image, Video, Audio, Model3D, Group, Transform, Empty)
  )

-- Submodules
import Hydrogen.Element.Flatten.Types
  ( FlattenState
  , FlattenResult
  , initialState
  )

import Hydrogen.Element.Flatten.Shape
  ( flattenRectangle
  , flattenEllipse
  , flattenPath
  , flattenPolygon
  , flattenStar
  , flattenRing
  , flattenSpiral
  , flattenArrow
  , flattenCross
  , flattenGear
  , flattenLine
  )

import Hydrogen.Element.Flatten.Text
  ( flattenText
  )

import Hydrogen.Element.Flatten.Media
  ( flattenImage
  , flattenVideo
  , flattenAudio
  , flattenModel3D
  )

import Hydrogen.Element.Flatten.Composition
  ( flattenGroup
  , flattenTransform
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Element to DrawCommands.
-- |
-- | Main entry point. Uses initial state and discards final state.
-- |
-- | ```purescript
-- | commands = flatten myElement
-- | -- commands.commands :: Array (DrawCommand msg)
-- | ```
flatten :: forall msg. Element -> FlattenResult msg
flatten element = flattenWithState initialState element

-- | Flatten with explicit state (for composing multiple elements).
-- |
-- | Use this when flattening multiple root elements in sequence,
-- | ensuring pickIds don't collide.
-- |
-- | ```purescript
-- | result1 = flattenWithState initialState element1
-- | result2 = flattenWithState result1.state element2
-- | allCommands = result1.commands <> result2.commands
-- | ```
flattenWithState :: forall msg. FlattenState -> Element -> FlattenResult msg
flattenWithState state element = case element of
  Empty -> 
    { commands: [], state: state }
  
  Rectangle spec ->
    flattenRectangle state spec
  
  Ellipse spec ->
    flattenEllipse state spec
  
  Path spec ->
    flattenPath state spec
  
  Polygon spec ->
    flattenPolygon state spec
  
  Star spec ->
    flattenStar state spec
  
  Ring spec ->
    flattenRing state spec
  
  Spiral spec ->
    flattenSpiral state spec
  
  Arrow spec ->
    flattenArrow state spec
  
  Cross spec ->
    flattenCross state spec
  
  Gear spec ->
    flattenGear state spec
  
  Line spec ->
    flattenLine state spec
  
  Text spec ->
    flattenText state spec
  
  Image spec ->
    flattenImage state spec
  
  Video spec ->
    flattenVideo state spec
  
  Audio spec ->
    flattenAudio state spec
  
  Model3D spec ->
    flattenModel3D state spec
  
  Group spec ->
    flattenGroup flattenWithState state spec
  
  Transform spec ->
    flattenTransform flattenWithState state spec
