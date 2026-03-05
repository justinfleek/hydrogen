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
  , flattenPolygon
  , flattenStar
  , flattenRing
  , flattenSpiral
  , flattenArrow
  , flattenCross
  , flattenGear
  , flattenLine
  , flattenStrokeAsRect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (>)
  , mod
  , map
  )

import Data.Array (concatMap, range, index, drop) as Array
import Data.Int (toNumber, floor, ceil)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- Element.Core specs
import Hydrogen.Element.Core
  ( RectangleSpec
  , EllipseSpec
  , PathSpec
  , PolygonSpec
  , StarSpec
  , RingSpec
  , SpiralSpec
  , ArrowSpec
  , CrossSpec
  , GearSpec
  , LineSpec
  , StrokeSpec
  )

-- Math primitives
import Hydrogen.Math.Core (cos, sin, pi, sqrt)

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

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // polygon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Polygon element to DrawPath command.
-- |
-- | Generates N vertices around center at equal angular intervals.
-- | Uses mapWithIndex to generate vertices in a single pass.
flattenPolygon :: forall msg. FlattenState -> PolygonSpec -> FlattenResult msg
flattenPolygon state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel r = spec.shape.radius
    n = spec.shape.sides
    rotRad = spec.shape.rotation * pi / 180.0
    nNum = toNumber n
    
    -- Generate vertex at index i
    vertex :: Int -> { x :: Pixel, y :: Pixel }
    vertex i =
      let
        iNum = toNumber i
        angle = rotRad + (2.0 * pi * iNum) / nNum
        vx = cx + r * cos angle
        vy = cy + r * sin angle
      in { x: Device.px vx, y: Device.px vy }
    
    -- Generate all vertices using range
    indices = Array.range 0 (n - 1)
    vertices = map vertex indices
    
    -- Build path segments: MoveTo first vertex, LineTo rest, ClosePath
    segments = case Array.index vertices 0 of
      Nothing -> []  -- Empty polygon (n < 1, shouldn't happen due to bounds)
      Just first ->
        let
          restVertices = Array.drop 1 vertices
          restSegments = map DC.LineTo restVertices
        in [DC.MoveTo first] <> restSegments <> [DC.ClosePath]
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
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
--                                                                       // star
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Star element to DrawPath command.
-- |
-- | Generates 2N vertices alternating between outer and inner radii.
flattenStar :: forall msg. FlattenState -> StarSpec -> FlattenResult msg
flattenStar state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel outerR = spec.shape.outerRadius
    Pixel innerR = spec.shape.innerRadius
    n = spec.shape.points
    rotRad = spec.shape.rotation * pi / 180.0
    nNum = toNumber n
    
    -- Generate vertex at index i (alternates outer/inner)
    vertex :: Int -> { x :: Pixel, y :: Pixel }
    vertex i =
      let
        iNum = toNumber i
        angle = rotRad + (pi * iNum) / nNum
        r = if i `mod` 2 == 0 then outerR else innerR
        vx = cx + r * cos angle
        vy = cy + r * sin angle
      in { x: Device.px vx, y: Device.px vy }
    
    -- 2N vertices total
    indices = Array.range 0 (2 * n - 1)
    vertices = map vertex indices
    
    segments = case Array.index vertices 0 of
      Nothing -> []
      Just first ->
        let
          restVertices = Array.drop 1 vertices
          restSegments = map DC.LineTo restVertices
        in [DC.MoveTo first] <> restSegments <> [DC.ClosePath]
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
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
--                                                                       // ring
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Ring element to DrawPath command.
-- |
-- | Creates a donut shape by combining outer and inner circles.
-- | Uses the even-odd fill rule (outer circle CW, inner circle CCW).
flattenRing :: forall msg. FlattenState -> RingSpec -> FlattenResult msg
flattenRing state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel outerR = spec.shape.outerRadius
    Pixel innerR = spec.shape.innerRadius
    kappa = 0.5522847498
    
    -- Outer circle (clockwise)
    outerSegments = circleSegments cx cy outerR kappa true
    
    -- Inner circle (counter-clockwise for hole)
    innerSegments = circleSegments cx cy innerR kappa false
    
    segments = outerSegments <> innerSegments
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
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

-- | Helper: generate circle path segments (CW or CCW).
circleSegments :: Number -> Number -> Number -> Number -> Boolean -> Array (DC.PathSegment)
circleSegments cx cy r kappa clockwise =
  let
    o = r * kappa
    top = { x: Device.px cx, y: Device.px (cy - r) }
    right = { x: Device.px (cx + r), y: Device.px cy }
    bottom = { x: Device.px cx, y: Device.px (cy + r) }
    left = { x: Device.px (cx - r), y: Device.px cy }
  in
    if clockwise then
      [ DC.MoveTo top
      , DC.CubicTo { x: Device.px (cx + o), y: Device.px (cy - r) }
                   { x: Device.px (cx + r), y: Device.px (cy - o) }
                   right
      , DC.CubicTo { x: Device.px (cx + r), y: Device.px (cy + o) }
                   { x: Device.px (cx + o), y: Device.px (cy + r) }
                   bottom
      , DC.CubicTo { x: Device.px (cx - o), y: Device.px (cy + r) }
                   { x: Device.px (cx - r), y: Device.px (cy + o) }
                   left
      , DC.CubicTo { x: Device.px (cx - r), y: Device.px (cy - o) }
                   { x: Device.px (cx - o), y: Device.px (cy - r) }
                   top
      , DC.ClosePath
      ]
    else
      [ DC.MoveTo top
      , DC.CubicTo { x: Device.px (cx - o), y: Device.px (cy - r) }
                   { x: Device.px (cx - r), y: Device.px (cy - o) }
                   left
      , DC.CubicTo { x: Device.px (cx - r), y: Device.px (cy + o) }
                   { x: Device.px (cx - o), y: Device.px (cy + r) }
                   bottom
      , DC.CubicTo { x: Device.px (cx + o), y: Device.px (cy + r) }
                   { x: Device.px (cx + r), y: Device.px (cy + o) }
                   right
      , DC.CubicTo { x: Device.px (cx + r), y: Device.px (cy - o) }
                   { x: Device.px (cx + o), y: Device.px (cy - r) }
                   top
      , DC.ClosePath
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // spiral
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Spiral element to DrawPath command.
-- |
-- | Archimedean spiral: r = a + b*theta
-- | Uses line segments to approximate the curve.
flattenSpiral :: forall msg. FlattenState -> SpiralSpec -> FlattenResult msg
flattenSpiral state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel startR = spec.shape.startRadius
    Pixel endR = spec.shape.endRadius
    turns = spec.shape.turns
    totalAngle = turns * 2.0 * pi
    
    -- Number of segments (more turns = more segments)
    numSegments = 64 * (if turns > 1.0 then ceil turns else 1)
    segNum = toNumber numSegments
    
    -- Generate spiral point at parameter t in [0, 1]
    spiralPoint :: Int -> { x :: Pixel, y :: Pixel }
    spiralPoint i =
      let
        t = toNumber i / segNum
        r = startR + (endR - startR) * t
        angle = t * totalAngle
        vx = cx + r * cos angle
        vy = cy + r * sin angle
      in { x: Device.px vx, y: Device.px vy }
    
    indices = Array.range 0 numSegments
    points = map spiralPoint indices
    
    segments = case Array.index points 0 of
      Nothing -> []
      Just first ->
        let
          restPoints = Array.drop 1 points
          restSegments = map DC.LineTo restPoints
        in [DC.MoveTo first] <> restSegments
    
    -- Spirals are typically stroked, not filled
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          pathParams = DC.pathParams segments
          strokeParams = pathParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = Coord.depthValue state.depth
            }
        in [DC.DrawPath strokeParams]
    
    -- Fill if requested (unusual for spirals)
    fillCmds = case spec.fill of
      _ ->
        let
          fillColor = fillToRGBA spec.fill spec.opacity
          pathParams = DC.pathParams segments
          pathParamsWithFill = pathParams
            { fill = Just fillColor
            , depth = Coord.depthValue (state.depth - 0.1)
            }
        in [DC.DrawPath pathParamsWithFill]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: fillCmds <> strokeCmds
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // arrow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Arrow element to DrawPath command.
flattenArrow :: forall msg. FlattenState -> ArrowSpec -> FlattenResult msg
flattenArrow state spec =
  let
    Pixel x1 = spec.shape.start.x
    Pixel y1 = spec.shape.start.y
    Pixel x2 = spec.shape.end.x
    Pixel y2 = spec.shape.end.y
    
    -- Arrow shaft as a line
    shaftSegments =
      [ DC.MoveTo { x: Device.px x1, y: Device.px y1 }
      , DC.LineTo { x: Device.px x2, y: Device.px y2 }
      ]
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams shaftSegments
    
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = pathParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = Coord.depthValue state.depth
            }
        in [DC.DrawPath strokeParams]
    
    -- Arrow head triangle at end point
    Pixel headSize = spec.shape.headSize
    dx = x2 - x1
    dy = y2 - y1
    len = sqrt (dx * dx + dy * dy)
    -- Normalized direction
    nx = if len > 0.0 then dx / len else 1.0
    ny = if len > 0.0 then dy / len else 0.0
    -- Perpendicular
    px = ny * headSize * 0.5
    py = (0.0 - nx) * headSize * 0.5
    -- Head tip at end, base points behind
    tipX = x2
    tipY = y2
    baseX = x2 - nx * headSize
    baseY = y2 - ny * headSize
    leftX = baseX + px
    leftY = baseY + py
    rightX = baseX - px
    rightY = baseY - py
    
    headSegments =
      [ DC.MoveTo { x: Device.px tipX, y: Device.px tipY }
      , DC.LineTo { x: Device.px leftX, y: Device.px leftY }
      , DC.LineTo { x: Device.px rightX, y: Device.px rightY }
      , DC.ClosePath
      ]
    
    headPathParams = DC.pathParams headSegments
    headCmds =
      let
        headFillParams = headPathParams
          { fill = Just fillColor
          , depth = Coord.depthValue (state.depth + 0.1)
          }
      in [DC.DrawPath headFillParams]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: strokeCmds <> headCmds
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // cross
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Cross element to DrawPath command.
-- |
-- | Creates a plus/cross shape from two overlapping rectangles.
flattenCross :: forall msg. FlattenState -> CrossSpec -> FlattenResult msg
flattenCross state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel armLen = spec.shape.armLength
    Pixel armWid = spec.shape.armWidth
    rotRad = spec.shape.rotation * pi / 180.0
    halfWid = armWid / 2.0
    
    -- Horizontal arm corners (before rotation)
    h1 = rotatePoint cx cy rotRad (cx - armLen) (cy - halfWid)
    h2 = rotatePoint cx cy rotRad (cx + armLen) (cy - halfWid)
    h3 = rotatePoint cx cy rotRad (cx + armLen) (cy + halfWid)
    h4 = rotatePoint cx cy rotRad (cx - armLen) (cy + halfWid)
    
    -- Vertical arm corners (before rotation)
    v1 = rotatePoint cx cy rotRad (cx - halfWid) (cy - armLen)
    v2 = rotatePoint cx cy rotRad (cx + halfWid) (cy - armLen)
    v3 = rotatePoint cx cy rotRad (cx + halfWid) (cy + armLen)
    v4 = rotatePoint cx cy rotRad (cx - halfWid) (cy + armLen)
    
    -- Build cross shape (two rectangles)
    segments =
      [ DC.MoveTo h1, DC.LineTo h2, DC.LineTo h3, DC.LineTo h4, DC.ClosePath
      , DC.MoveTo v1, DC.LineTo v2, DC.LineTo v3, DC.LineTo v4, DC.ClosePath
      ]
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
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

-- | Rotate a point around center
rotatePoint :: Number -> Number -> Number -> Number -> Number -> { x :: Pixel, y :: Pixel }
rotatePoint cx cy angle px py =
  let
    dx = px - cx
    dy = py - cy
    rx = dx * cos angle - dy * sin angle
    ry = dx * sin angle + dy * cos angle
  in { x: Device.px (cx + rx), y: Device.px (cy + ry) }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // gear
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Gear element to DrawPath command.
-- |
-- | Creates a gear shape with teeth around the perimeter.
flattenGear :: forall msg. FlattenState -> GearSpec -> FlattenResult msg
flattenGear state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel outerR = spec.shape.outerRadius
    Pixel innerR = spec.shape.innerRadius
    Pixel holeR = spec.shape.holeRadius
    n = spec.shape.teeth
    toothWidth = spec.shape.toothWidth
    nNum = toNumber n
    
    -- Angle per tooth
    anglePerTooth = 2.0 * pi / nNum
    toothAngle = anglePerTooth * toothWidth
    valleyAngle = anglePerTooth * (1.0 - toothWidth)
    
    -- Generate gear outline
    gearPoint :: Int -> Array { x :: Pixel, y :: Pixel }
    gearPoint i =
      let
        iNum = toNumber i
        baseAngle = iNum * anglePerTooth
        -- Tooth starts at outer radius
        p1 = { x: Device.px (cx + outerR * cos baseAngle)
             , y: Device.px (cy + outerR * sin baseAngle) }
        -- Tooth top
        p2 = { x: Device.px (cx + outerR * cos (baseAngle + toothAngle))
             , y: Device.px (cy + outerR * sin (baseAngle + toothAngle)) }
        -- Valley at inner radius
        p3 = { x: Device.px (cx + innerR * cos (baseAngle + toothAngle))
             , y: Device.px (cy + innerR * sin (baseAngle + toothAngle)) }
        p4 = { x: Device.px (cx + innerR * cos (baseAngle + anglePerTooth))
             , y: Device.px (cy + innerR * sin (baseAngle + anglePerTooth)) }
      in [p1, p2, p3, p4]
    
    indices = Array.range 0 (n - 1)
    allPoints = Array.concatMap gearPoint indices
    
    outerSegments = case Array.index allPoints 0 of
      Nothing -> []
      Just first ->
        let
          restPoints = Array.drop 1 allPoints
          restSegments = map DC.LineTo restPoints
        in [DC.MoveTo first] <> restSegments <> [DC.ClosePath]
    
    -- Center hole (counter-clockwise)
    holeSegments = if holeR > 0.0
      then circleSegments cx cy holeR 0.5522847498 false
      else []
    
    segments = outerSegments <> holeSegments
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = Coord.depthValue state.depth
      }
    
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
--                                                                       // line
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Line element to DrawPath command.
-- |
-- | Simple line segment from start to end. Lines have no fill.
flattenLine :: forall msg. FlattenState -> LineSpec -> FlattenResult msg
flattenLine state spec =
  let
    Pixel x1 = spec.shape.start.x
    Pixel y1 = spec.shape.start.y
    Pixel x2 = spec.shape.end.x
    Pixel y2 = spec.shape.end.y
    
    segments =
      [ DC.MoveTo { x: Device.px x1, y: Device.px y1 }
      , DC.LineTo { x: Device.px x2, y: Device.px y2 }
      ]
    
    pathParams = DC.pathParams segments
    
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = pathParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = Coord.depthValue state.depth
            }
        in [DC.DrawPath strokeParams]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: strokeCmds
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // stroke // as // rect
-- ═════════════════════════════════════════════════════════════════════════════

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
