-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // flatten // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape flattening: Rectangle, Ellipse, Path → DrawCommand.
-- |
-- | ## Purpose
-- |
-- | Converts geometric shape elements to GPU draw commands.
-- | Handles coordinate conversion from center-based to top-left-based.
-- |
-- | ## Shapes
-- |
-- | - Rectangle: Emits DrawRect + optional stroke DrawPath
-- | - Ellipse: Approximated as 4 cubic beziers (kappa = 0.5522847498)
-- | - Path: Direct conversion of PathCommands to PathSegments

module Hydrogen.Element.Flatten.Shape
  ( flattenRectangle
  , flattenEllipse
  , flattenPath
  , flattenStrokeAsRect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (<>)
  )

import Data.Array (concatMap) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- Element.Core specs
import Hydrogen.Element.Core
  ( RectangleSpec
  , EllipseSpec
  , PathSpec
  , StrokeSpec
  )

-- GPU primitives
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.GPU.Coordinates as Coord

-- Schema atoms
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Dimension.Device as Device

-- Local helpers
import Hydrogen.Element.Flatten.Types (FlattenState, FlattenResult)
import Hydrogen.Element.Flatten.Helpers
  ( centerToTopLeft
  , fillToRGBA
  , convertCorners
  , strokeWidthToPixel
  , convertPathCommand
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rectangle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Rectangle element to DrawRect command.
-- |
-- | Converts from center-based (Element) to top-left-based (DrawCommand).
-- | Handles fill and stroke separately (stroke becomes a second DrawRect).
flattenRectangle :: forall msg. FlattenState -> RectangleSpec -> FlattenResult msg
flattenRectangle state spec =
  let
    -- Convert center-based to top-left-based coordinates
    Tuple x y = centerToTopLeft spec.shape.center spec.shape.width spec.shape.height
    
    -- Convert fill to RGBA
    fillColor = fillToRGBA spec.fill spec.opacity
    
    -- Convert Radius.Corners to DC.Radius.Corners
    corners = convertCorners spec.shape.corners
    
    -- Build the rect params (convert to bounded coordinate types)
    rectParams =
      { x: Coord.screenXFromPixel x
      , y: Coord.screenYFromPixel y
      , width: Coord.pixelWidthFromPixel spec.shape.width
      , height: Coord.pixelHeightFromPixel spec.shape.height
      , fill: fillColor
      , cornerRadius: corners
      , depth: Coord.depthValue state.depth
      , pickId: Nothing  -- No interaction by default
      , onClick: Nothing
      }
    
    -- Main fill command
    fillCmd = DC.DrawRect rectParams
    
    -- Stroke command (if present)
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec -> flattenStrokeAsRect state spec strokeSpec
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [fillCmd] <> strokeCmds
    , state: newState
    }

-- | Flatten stroke as DrawPath (DrawRect doesn't support stroke directly).
flattenStrokeAsRect :: forall msg. FlattenState -> RectangleSpec -> StrokeSpec -> Array (DC.DrawCommand msg)
flattenStrokeAsRect state spec strokeSpec =
  let
    Tuple x y = centerToTopLeft spec.shape.center spec.shape.width spec.shape.height
    Pixel xVal = x
    Pixel yVal = y
    Pixel wVal = spec.shape.width
    Pixel hVal = spec.shape.height
    topLeft = { x: Device.px xVal, y: Device.px yVal }
    topRight = { x: Device.px (xVal + wVal), y: Device.px yVal }
    bottomRight = { x: Device.px (xVal + wVal), y: Device.px (yVal + hVal) }
    bottomLeft = { x: Device.px xVal, y: Device.px (yVal + hVal) }
    segments =
      [ DC.MoveTo topLeft
      , DC.LineTo topRight
      , DC.LineTo bottomRight
      , DC.LineTo bottomLeft
      , DC.ClosePath
      ]
    strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
    strokeWidth = strokeWidthToPixel strokeSpec.width
    pathParams = DC.pathParams segments
    pathParamsWithStroke = pathParams
      { stroke = Just strokeColor
      , strokeWidth = strokeWidth
      , depth = Coord.depthValue (state.depth + 0.5)
      }
  in
    [ DC.DrawPath pathParamsWithStroke ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // ellipse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten Ellipse to DrawPath (4 cubic beziers with kappa = 0.5522847498).
flattenEllipse :: forall msg. FlattenState -> EllipseSpec -> FlattenResult msg
flattenEllipse state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel rx = spec.shape.radiusX
    Pixel ry = spec.shape.radiusY
    kappa = 0.5522847498  -- (4/3) * tan(pi/8)
    ox = rx * kappa
    oy = ry * kappa
    
    top = { x: Device.px cx, y: Device.px (cy - ry) }
    right = { x: Device.px (cx + rx), y: Device.px cy }
    bottom = { x: Device.px cx, y: Device.px (cy + ry) }
    left = { x: Device.px (cx - rx), y: Device.px cy }
    
    topToRightC1 = { x: Device.px (cx + ox), y: Device.px (cy - ry) }
    topToRightC2 = { x: Device.px (cx + rx), y: Device.px (cy - oy) }
    rightToBottomC1 = { x: Device.px (cx + rx), y: Device.px (cy + oy) }
    rightToBottomC2 = { x: Device.px (cx + ox), y: Device.px (cy + ry) }
    bottomToLeftC1 = { x: Device.px (cx - ox), y: Device.px (cy + ry) }
    bottomToLeftC2 = { x: Device.px (cx - rx), y: Device.px (cy + oy) }
    leftToTopC1 = { x: Device.px (cx - rx), y: Device.px (cy - oy) }
    leftToTopC2 = { x: Device.px (cx - ox), y: Device.px (cy - ry) }
    
    segments =
      [ DC.MoveTo top
      , DC.CubicTo topToRightC1 topToRightC2 right
      , DC.CubicTo rightToBottomC1 rightToBottomC2 bottom
      , DC.CubicTo bottomToLeftC1 bottomToLeftC2 left
      , DC.CubicTo leftToTopC1 leftToTopC2 top
      , DC.ClosePath
      ]
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
    -- Add stroke if present
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = pathParams
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
--                                                                        // path
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Path element to DrawPath command.
-- |
-- | Converts Schema PathCommands to DrawCommand PathSegments.
flattenPath :: forall msg. FlattenState -> PathSpec -> FlattenResult msg
flattenPath state spec =
  let
    -- Convert PathCommand array to PathSegment array
    segments = Array.concatMap convertPathCommand spec.shape.commands
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
    -- Add stroke if present
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = pathParams
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
