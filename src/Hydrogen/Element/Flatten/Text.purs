-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // flatten // text
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text flattening: TextSpec → DrawPath commands.
-- |
-- | ## Purpose
-- |
-- | Converts text elements (composed of glyphs) to GPU path commands.
-- | Each glyph becomes one or more DrawPath commands for fill and stroke.
-- |
-- | ## Glyph Rendering
-- |
-- | Text is pre-laid-out into GlyphSpecs, each containing:
-- | - GlyphPath: 3D bezier contours (z-coordinate discarded for 2D)
-- | - Transform2D: Position and transformation
-- | - Fill/Stroke: Visual properties
-- | - Progress: Animation state (0-1 for reveal effects)
-- |
-- | ## Coordinate System
-- |
-- | Glyph coordinates are already in absolute position (from layout).
-- | The flatten process converts 3D contours to 2D path segments.

module Hydrogen.Element.Flatten.Text
  ( flattenText
  , flattenGlyph
  , flattenGlyphs
  , glyphPathToSegments
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (*)
  , (+)
  , (<>)
  )

import Data.Array (concatMap) as Array
import Data.Array as Data.Array
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Just, Nothing))

-- Element.Core specs
import Hydrogen.Element.Core
  ( TextSpec
  , GlyphSpec
  )

-- GPU primitives
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord

-- Schema atoms
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Typography.GlyphGeometry as Glyph
import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Geometry.Transform as Transform

-- Local helpers
import Hydrogen.Element.Flatten.Types (FlattenState, FlattenResult)
import Hydrogen.Element.Flatten.Helpers
  ( fillToRGBA
  , strokeWidthToPixel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // text // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Text element to DrawPath commands.
-- |
-- | Each glyph in the TextSpec becomes one or more DrawPath commands:
-- | - One for the fill
-- | - One for the stroke (if present)
-- |
-- | Glyph transforms are applied to the path commands.
-- | Progress value is used for opacity modulation (for reveal animations).
flattenText :: forall msg. FlattenState -> TextSpec -> FlattenResult msg
flattenText state spec =
  flattenGlyphs state spec.opacity spec.glyphs

-- | Flatten array of glyphs, threading state through
flattenGlyphs 
  :: forall msg
   . FlattenState 
  -> Opacity.Opacity  -- Overall text opacity
  -> Array GlyphSpec 
  -> FlattenResult msg
flattenGlyphs state _textOpacity glyphs =
  Data.Array.foldl flattenGlyphAccum { commands: [], state: state } glyphs
  where
    flattenGlyphAccum 
      :: FlattenResult msg 
      -> GlyphSpec 
      -> FlattenResult msg
    flattenGlyphAccum acc glyph =
      let result = flattenGlyph acc.state glyph
      in { commands: acc.commands <> result.commands
         , state: result.state
         }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // glyph // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a single glyph to DrawPath commands.
-- |
-- | Converts the GlyphPath (3D bezier contours) to 2D path segments,
-- | applies the glyph's transform, and creates fill/stroke commands.
flattenGlyph :: forall msg. FlattenState -> GlyphSpec -> FlattenResult msg
flattenGlyph state glyph =
  let
    -- Convert 3D glyph contours to 2D path segments
    segments = glyphPathToSegments glyph.glyph
    
    -- Apply progress to opacity (0 = invisible, 1 = full opacity)
    progressMod = Progress.unwrapProgress glyph.progress
    modifiedOpacity = Opacity.opacity 
      (floor (toNumber (Opacity.unwrap glyph.opacity) * progressMod))
    
    fillColor = fillToRGBA glyph.fill modifiedOpacity
    
    -- Base path params
    pathParams = DC.pathParams segments
    
    -- Apply glyph transform to path params
    -- Transform2D contains translate, rotate, scale, skew, origin
    transformedParams = applyTransformToPathParams glyph.transform pathParams
    
    pathParamsWithFill = transformedParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
    -- Add stroke if present
    strokeCmds = case glyph.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = transformedParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = Coord.depthValue (state.depth + 0.5)
            }
        in [DC.DrawPath strokeParams]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [DC.DrawPath pathParamsWithFill] <> strokeCmds
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // path // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert GlyphPath (3D contours) to flat array of PathSegments.
-- |
-- | Discards Z coordinate since DrawCommand is 2D.
-- | Multiple contours are flattened into a single path array.
glyphPathToSegments :: Glyph.GlyphPath -> Array DC.PathSegment
glyphPathToSegments glyphPath =
  Array.concatMap contourToSegments glyphPath.contours

-- | Convert a single Contour to PathSegments
contourToSegments :: Glyph.Contour -> Array DC.PathSegment
contourToSegments contour =
  Array.concatMap pathCommand3DToSegments contour.commands

-- | Convert a 3D PathCommand to 2D PathSegment(s)
-- |
-- | Z coordinates are discarded for 2D rendering.
pathCommand3DToSegments :: Glyph.PathCommand3D -> Array DC.PathSegment
pathCommand3DToSegments = case _ of
  Glyph.MoveTo3D pt ->
    [DC.MoveTo { x: pt.x, y: pt.y }]
  Glyph.LineTo3D pt ->
    [DC.LineTo { x: pt.x, y: pt.y }]
  Glyph.QuadraticTo3D ctrl end ->
    [DC.QuadraticTo { x: ctrl.x, y: ctrl.y } { x: end.x, y: end.y }]
  Glyph.CubicTo3D c1 c2 end ->
    [DC.CubicTo { x: c1.x, y: c1.y } { x: c2.x, y: c2.y } { x: end.x, y: end.y }]
  Glyph.ClosePath3D ->
    [DC.ClosePath]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // transform // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply Transform2D to PathParams
-- |
-- | Currently a no-op since PathParams doesn't have transform fields.
-- | The glyph transform should be baked into the path segments themselves
-- | via transformPathSegments (to be implemented) or applied at runtime.
-- |
-- | For now, glyph positions come from the transform's translate component
-- | which should be encoded in the GlyphPath geometry at layout time.
applyTransformToPathParams :: forall msg. Transform.Transform2D -> DC.PathParams msg -> DC.PathParams msg
applyTransformToPathParams _transform params = params
