-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // compositor // shapelayer
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ShapeLayer — Pure Math, Pixel-Perfect Clipping
-- |
-- | ## Design Philosophy
-- |
-- | The shape layer sits above the material layer and provides:
-- | - Vector strokes, fills, and effects
-- | - Elevation/shadow casting
-- | - Haptic feedback regions
-- | - Glow and animated strokes
-- |
-- | Unlike the material layer, the shape layer is **pure math** and clips
-- | at exact pixels during scale operations. No grid alignment constraint.

module Hydrogen.Compositor.ShapeLayer
  ( -- * ShapeLayer Type
    ShapeLayer(ShapeLayer)
  , defaultShapeLayer
  
  -- * ShapeLayer Queries
  , getShapes
  , getStroke
  , getFill
  , getShadow
  , getGlowRadius
  , getGlowColor
  , isShapeVisible
  , shapeCount
  , unwrapShapeLayer
  
  -- * ShapeLayer Operations
  , addShape
  , addShapes
  , removeShapeAt
  , clearShapes
  , setStroke
  , setFill
  , setShadow
  , setGlow
  , setGlowRadius
  , setGlowColor
  , setShapeVisible
  , toggleShapeVisible
  
  -- * Shape Primitive Constructors
  , rectangle
  , ellipse
  , path
  , roundedRect
  , regularPolygon
  , triangle
  , pentagon
  , hexagon
  , star
  , line
  , polyline
  , polygon
  
  -- * Shape Primitives
  , ShapePrimitive
      ( Rectangle
      , Ellipse
      , Path
      , RoundedRect
      , RegularPolygon
      , Star
      , Line
      , Polyline
      , Polygon
      )
  , PathCommand(MoveTo, LineTo, QuadTo, CubicTo, ClosePath)
  
  -- * Stroke Configuration  
  , StrokeConfig(StrokeConfig)
  , defaultStrokeConfig
  
  -- * Stroke Enums (re-exported from Schema for convenience)
  , module ReExportLineCap
  , module ReExportLineJoin
  
  -- * Shadow (uses Schema LayeredShadow)
  , noShadow
  , elevationShadow
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude 
  ( class Eq
  , class Show
  , show
  , max
  , (<>)
  , ($)
  , (<)
  , (*)
  , (-)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))

-- RGBA color type from Schema (bounded Channel atoms, Opacity atom)
import Hydrogen.Schema.Color.RGB (RGBA, rgba)

-- LineCap re-export for stroke endpoints
import Hydrogen.Schema.Geometry.Stroke 
  ( LineCap(CapButt, CapRound, CapSquare)
  ) as ReExportLineCap

-- LineJoin re-export for stroke corners
import Hydrogen.Schema.Geometry.Stroke 
  ( LineJoin(JoinMiter, JoinRound, JoinBevel)
  ) as ReExportLineJoin

import Hydrogen.Schema.Geometry.Stroke as GeomStroke

-- Shadow from Schema (replaces stub Elevation)
import Hydrogen.Schema.Elevation.Shadow as Shadow



-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // shadow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow uses Schema's LayeredShadow for Material Design style elevation.
-- |
-- | The Schema provides:
-- | - BoxShadow: Single shadow (offsetX, offsetY, blur, spread, color, inset)
-- | - LayeredShadow: Multiple shadows for realistic depth
-- | - DropShadow: Filter-based shadow (no spread/inset)
-- |
-- | Higher elevation = more/larger shadows. Shadows cast onto layers below,
-- | ultimately landing on the canvas.
-- |
-- | Use qualified import: `import Hydrogen.Schema.Elevation.Shadow as Shadow`
-- |
-- | ```purescript
-- | cardShadow = Shadow.layered
-- |   [ Shadow.boxShadow { offsetX: 0.0, offsetY: 1.0, blur: 3.0, spread: 0.0
-- |                      , color: rgba 0 0 0 10, inset: false }
-- |   , Shadow.boxShadow { offsetX: 0.0, offsetY: 4.0, blur: 6.0, spread: -1.0
-- |                      , color: rgba 0 0 0 10, inset: false }
-- |   ]
-- | ```

-- | No shadow (empty layered shadow)
noShadow :: Shadow.LayeredShadow
noShadow = Shadow.noShadow

-- | Quick elevation helper: creates a simple drop shadow at given depth
-- |
-- | Level 0 = no shadow, higher = more prominent shadow
-- | This is a convenience function; for precise control use Shadow.layered
elevationShadow :: Int -> Shadow.LayeredShadow
elevationShadow level = 
  if level < 1 
    then Shadow.noShadow
    else Shadow.layered
      [ Shadow.boxShadow
          { offsetX: 0.0
          , offsetY: toNumber level
          , blur: toNumber (level * 2)
          , spread: 0.0
          , color: rgba 0 0 0 (max 5 (25 - level))  -- Fades as elevation increases
          , inset: false
          }
      ]
  where
  toNumber n = if n < 0 then 0.0 else intToNumber n
  intToNumber 0 = 0.0
  intToNumber 1 = 1.0
  intToNumber 2 = 2.0
  intToNumber 3 = 3.0
  intToNumber 4 = 4.0
  intToNumber 5 = 5.0
  intToNumber 6 = 6.0
  intToNumber 7 = 7.0
  intToNumber 8 = 8.0
  intToNumber 9 = 9.0
  intToNumber 10 = 10.0
  intToNumber 11 = 11.0
  intToNumber 12 = 12.0
  intToNumber 13 = 13.0
  intToNumber 14 = 14.0
  intToNumber 15 = 15.0
  intToNumber 16 = 16.0
  intToNumber 17 = 17.0
  intToNumber 18 = 18.0
  intToNumber 19 = 19.0
  intToNumber 20 = 20.0
  intToNumber 21 = 21.0
  intToNumber 22 = 22.0
  intToNumber 23 = 23.0
  intToNumber 24 = 24.0
  intToNumber _ = 24.0  -- Clamp at Material Design max

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // stroke configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke configuration — how shape outlines are rendered.
-- |
-- | Strokes are pure vector math and render at exact pixels regardless
-- | of zoom level.
-- |
-- | Uses Schema types:
-- | - RGBA for colors (bounded Channel atoms, Opacity atom)
-- | - LineCap/LineJoin for line style (bounded enums)
newtype StrokeConfig = StrokeConfig
  { -- | Stroke width in pixels
    width :: Number
    
    -- | Stroke color (Schema RGBA: r/g/b 0-255, alpha 0-100%)
  , color :: RGBA
  
    -- | Dash pattern (empty = solid line)
  , dashPattern :: Array Number
  
    -- | Dash offset for animation
  , dashOffset :: Number
  
    -- | Line cap style (CapButt, CapRound, CapSquare)
  , lineCap :: GeomStroke.LineCap
  
    -- | Line join style (JoinMiter, JoinRound, JoinBevel)
  , lineJoin :: GeomStroke.LineJoin
  }

derive instance eqStrokeConfig :: Eq StrokeConfig

instance showStrokeConfig :: Show StrokeConfig where
  show (StrokeConfig s) = "StrokeConfig { width: " <> show s.width <> "px }"

-- | Default stroke — 1px solid black with round caps and joins
defaultStrokeConfig :: StrokeConfig
defaultStrokeConfig = StrokeConfig
  { width: 1.0
  , color: rgba 0 0 0 100  -- Black, fully opaque (alpha is 0-100%)
  , dashPattern: []
  , dashOffset: 0.0
  , lineCap: GeomStroke.CapRound
  , lineJoin: GeomStroke.JoinRound
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shape primitives
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape primitives — basic geometric forms for the shape layer.
-- |
-- | All primitives are pure math and scale/clip at exact pixels.
-- |
-- | Regular polygons use vertex count:
-- | - 3 = triangle
-- | - 4 = square (use Rectangle for axis-aligned)
-- | - 5 = pentagon
-- | - 6 = hexagon
-- | - etc.
-- |
-- | Stars use point count and inner radius ratio.
data ShapePrimitive
  = Rectangle 
      { x :: Number, y :: Number, width :: Number, height :: Number }
      { cornerRadius :: Number }
  | Ellipse 
      { cx :: Number, cy :: Number, rx :: Number, ry :: Number }
  | Path (Array PathCommand)
  | RoundedRect 
      { x :: Number, y :: Number, width :: Number, height :: Number }
      { topLeft :: Number, topRight :: Number
      , bottomLeft :: Number, bottomRight :: Number }
  | RegularPolygon
      { cx :: Number, cy :: Number, radius :: Number }
      { sides :: Int, rotation :: Number }
      -- ^ Regular polygon: center, radius, number of sides (3+), rotation in radians
  | Star
      { cx :: Number, cy :: Number, outerRadius :: Number, innerRadius :: Number }
      { points :: Int, rotation :: Number }
      -- ^ Star: center, outer/inner radius, number of points (3+), rotation in radians
  | Line
      { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
      -- ^ Simple line segment
  | Polyline (Array { x :: Number, y :: Number })
      -- ^ Open polyline (connected line segments, not closed)
  | Polygon (Array { x :: Number, y :: Number })
      -- ^ Closed polygon from arbitrary vertices

derive instance eqShapePrimitive :: Eq ShapePrimitive

instance showShapePrimitive :: Show ShapePrimitive where
  show (Rectangle bounds _) = 
    "Rectangle(" <> show bounds.width <> "×" <> show bounds.height <> ")"
  show (Ellipse e) = "Ellipse(" <> show e.rx <> "×" <> show e.ry <> ")"
  show (Path cmds) = "Path(" <> show (Array.length cmds) <> " commands)"
  show (RoundedRect bounds _) = 
    "RoundedRect(" <> show bounds.width <> "×" <> show bounds.height <> ")"
  show (RegularPolygon _ cfg) = 
    "RegularPolygon(" <> show cfg.sides <> " sides)"
  show (Star _ cfg) = 
    "Star(" <> show cfg.points <> " points)"
  show (Line _) = "Line"
  show (Polyline pts) = "Polyline(" <> show (Array.length pts) <> " points)"
  show (Polygon pts) = "Polygon(" <> show (Array.length pts) <> " vertices)"

-- | Path commands for vector shapes
data PathCommand
  = MoveTo Number Number
  | LineTo Number Number
  | QuadTo Number Number Number Number
  | CubicTo Number Number Number Number Number Number
  | ClosePath

derive instance eqPathCommand :: Eq PathCommand

instance showPathCommand :: Show PathCommand where
  show (MoveTo x y) = "M " <> show x <> " " <> show y
  show (LineTo x y) = "L " <> show x <> " " <> show y
  show (QuadTo cx cy x y) = "Q " <> show cx <> " " <> show cy <> " " <> show x <> " " <> show y
  show (CubicTo c1x c1y c2x c2y x y) = 
    "C " <> show c1x <> " " <> show c1y <> " " <> show c2x <> " " <> show c2y <> " " <> show x <> " " <> show y
  show ClosePath = "Z"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // shape layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | The shape layer — vector graphics above the material layer.
-- |
-- | This layer clips at exact pixels during scale operations.
-- | It contains strokes, fills, shadows, and effects.
-- |
-- | Uses Schema types:
-- | - RGBA for colors (bounded Channel atoms, Opacity atom)
-- | - LayeredShadow for elevation (multiple box shadows for depth)
newtype ShapeLayer = ShapeLayer
  { -- | The shape primitives in this layer
    shapes :: Array ShapePrimitive
    
    -- | Stroke configuration
  , stroke :: StrokeConfig
  
    -- | Fill color (Schema RGBA: r/g/b 0-255, alpha 0-100%)
  , fill :: RGBA
  
    -- | Shadow for elevation (Schema LayeredShadow)
  , shadow :: Shadow.LayeredShadow
  
    -- | Glow effect radius (0 = no glow)
  , glowRadius :: Number
  
    -- | Glow color (Schema RGBA)
  , glowColor :: RGBA
  
    -- | Whether this layer is visible
  , visible :: Boolean
  }

derive instance eqShapeLayer :: Eq ShapeLayer

instance showShapeLayer :: Show ShapeLayer where
  show (ShapeLayer s) = 
    "ShapeLayer { shapes: " <> show s.shapes <> ", shadow: " <> show s.shadow <> " }"

-- | Default shape layer — no shapes, no shadow, no glow
defaultShapeLayer :: ShapeLayer
defaultShapeLayer = ShapeLayer
  { shapes: []
  , stroke: defaultStrokeConfig
  , fill: rgba 0 0 0 0  -- Transparent (alpha 0%)
  , shadow: noShadow
  , glowRadius: 0.0
  , glowColor: rgba 0 0 0 0  -- Transparent (alpha 0%)
  , visible: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // shape primitive constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a rectangle primitive
-- |
-- | ```purescript
-- | rect = rectangle 10.0 20.0 100.0 50.0 8.0  -- x, y, width, height, cornerRadius
-- | ```
rectangle :: Number -> Number -> Number -> Number -> Number -> ShapePrimitive
rectangle x y width height cornerRadius =
  Rectangle 
    { x: x, y: y, width: max 0.0 width, height: max 0.0 height }
    { cornerRadius: max 0.0 cornerRadius }

-- | Create an ellipse primitive
-- |
-- | ```purescript
-- | circ = ellipse 50.0 50.0 25.0 25.0  -- centerX, centerY, radiusX, radiusY
-- | ```
ellipse :: Number -> Number -> Number -> Number -> ShapePrimitive
ellipse cx cy rx ry =
  Ellipse { cx: cx, cy: cy, rx: max 0.0 rx, ry: max 0.0 ry }

-- | Create a path primitive from commands
path :: Array PathCommand -> ShapePrimitive
path commands = Path commands

-- | Create a rounded rectangle with individual corner radii
roundedRect 
  :: Number -> Number -> Number -> Number 
  -> { topLeft :: Number, topRight :: Number, bottomLeft :: Number, bottomRight :: Number }
  -> ShapePrimitive
roundedRect x y width height corners =
  RoundedRect
    { x: x, y: y, width: max 0.0 width, height: max 0.0 height }
    { topLeft: max 0.0 corners.topLeft
    , topRight: max 0.0 corners.topRight
    , bottomLeft: max 0.0 corners.bottomLeft
    , bottomRight: max 0.0 corners.bottomRight
    }

-- | Create a regular polygon (triangle, pentagon, hexagon, etc.)
-- |
-- | ```purescript
-- | triangle = regularPolygon 50.0 50.0 30.0 3 0.0  -- center, radius, 3 sides, no rotation
-- | pentagon = regularPolygon 50.0 50.0 30.0 5 0.0  -- 5 sides
-- | hexagon = regularPolygon 50.0 50.0 30.0 6 0.0   -- 6 sides
-- | ```
-- |
-- | Sides are clamped to minimum 3 (triangle).
regularPolygon :: Number -> Number -> Number -> Int -> Number -> ShapePrimitive
regularPolygon cx cy radius sides rotation =
  RegularPolygon
    { cx: cx, cy: cy, radius: max 0.0 radius }
    { sides: max 3 sides, rotation: rotation }

-- | Convenience: create a triangle
triangle :: Number -> Number -> Number -> Number -> ShapePrimitive
triangle cx cy radius rotation = regularPolygon cx cy radius 3 rotation

-- | Convenience: create a pentagon
pentagon :: Number -> Number -> Number -> Number -> ShapePrimitive
pentagon cx cy radius rotation = regularPolygon cx cy radius 5 rotation

-- | Convenience: create a hexagon
hexagon :: Number -> Number -> Number -> Number -> ShapePrimitive
hexagon cx cy radius rotation = regularPolygon cx cy radius 6 rotation

-- | Create a star shape
-- |
-- | ```purescript
-- | fiveStar = star 50.0 50.0 30.0 15.0 5 0.0  -- outer/inner radius, 5 points
-- | ```
-- |
-- | Points are clamped to minimum 3.
star :: Number -> Number -> Number -> Number -> Int -> Number -> ShapePrimitive
star cx cy outerRadius innerRadius points rotation =
  Star
    { cx: cx, cy: cy, outerRadius: max 0.0 outerRadius, innerRadius: max 0.0 innerRadius }
    { points: max 3 points, rotation: rotation }

-- | Create a line segment
line :: Number -> Number -> Number -> Number -> ShapePrimitive
line x1 y1 x2 y2 = Line { x1: x1, y1: y1, x2: x2, y2: y2 }

-- | Create an open polyline from points
polyline :: Array { x :: Number, y :: Number } -> ShapePrimitive
polyline points = Polyline points

-- | Create a closed polygon from vertices
polygon :: Array { x :: Number, y :: Number } -> ShapePrimitive
polygon vertices = Polygon vertices

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // shapelayer queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all shapes in the layer
getShapes :: ShapeLayer -> Array ShapePrimitive
getShapes (ShapeLayer s) = s.shapes

-- | Get the stroke configuration
getStroke :: ShapeLayer -> StrokeConfig
getStroke (ShapeLayer s) = s.stroke

-- | Get the fill color
getFill :: ShapeLayer -> RGBA
getFill (ShapeLayer s) = s.fill

-- | Get the shadow (Schema LayeredShadow)
getShadow :: ShapeLayer -> Shadow.LayeredShadow
getShadow (ShapeLayer s) = s.shadow

-- | Get the glow radius
getGlowRadius :: ShapeLayer -> Number
getGlowRadius (ShapeLayer s) = s.glowRadius

-- | Get the glow color
getGlowColor :: ShapeLayer -> RGBA
getGlowColor (ShapeLayer s) = s.glowColor

-- | Check if the shape layer is visible
isShapeVisible :: ShapeLayer -> Boolean
isShapeVisible (ShapeLayer s) = s.visible

-- | Count the number of shapes
shapeCount :: ShapeLayer -> Int
shapeCount (ShapeLayer s) = Array.length s.shapes

-- | Unwrap to access the full record
unwrapShapeLayer 
  :: ShapeLayer 
  -> { shapes :: Array ShapePrimitive
     , stroke :: StrokeConfig
     , fill :: RGBA
     , shadow :: Shadow.LayeredShadow
     , glowRadius :: Number
     , glowColor :: RGBA
     , visible :: Boolean
     }
unwrapShapeLayer (ShapeLayer s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // shapelayer operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a shape to the layer
addShape :: ShapePrimitive -> ShapeLayer -> ShapeLayer
addShape shape (ShapeLayer s) = 
  ShapeLayer (s { shapes = Array.snoc s.shapes shape })

-- | Add multiple shapes to the layer
addShapes :: Array ShapePrimitive -> ShapeLayer -> ShapeLayer
addShapes newShapes (ShapeLayer s) = 
  ShapeLayer (s { shapes = s.shapes <> newShapes })

-- | Remove a shape at a specific index
-- |
-- | Returns Nothing if the index is out of bounds.
removeShapeAt :: Int -> ShapeLayer -> Maybe ShapeLayer
removeShapeAt idx (ShapeLayer s) =
  case Array.deleteAt idx s.shapes of
    Just newShapes -> Just $ ShapeLayer (s { shapes = newShapes })
    Nothing -> Nothing

-- | Remove all shapes from the layer
clearShapes :: ShapeLayer -> ShapeLayer
clearShapes (ShapeLayer s) = ShapeLayer (s { shapes = [] })

-- | Set the stroke configuration
setStroke :: StrokeConfig -> ShapeLayer -> ShapeLayer
setStroke stroke (ShapeLayer s) = ShapeLayer (s { stroke = stroke })

-- | Set the fill color
setFill :: RGBA -> ShapeLayer -> ShapeLayer
setFill fill (ShapeLayer s) = ShapeLayer (s { fill = fill })

-- | Set the shadow (Schema LayeredShadow)
setShadow :: Shadow.LayeredShadow -> ShapeLayer -> ShapeLayer
setShadow sh (ShapeLayer s) = ShapeLayer (s { shadow = sh })

-- | Set both glow radius and color at once
setGlow :: Number -> RGBA -> ShapeLayer -> ShapeLayer
setGlow radius color (ShapeLayer s) = 
  ShapeLayer (s { glowRadius = max 0.0 radius, glowColor = color })

-- | Set the glow radius (clamped to non-negative)
setGlowRadius :: Number -> ShapeLayer -> ShapeLayer
setGlowRadius radius (ShapeLayer s) = 
  ShapeLayer (s { glowRadius = max 0.0 radius })

-- | Set the glow color
setGlowColor :: RGBA -> ShapeLayer -> ShapeLayer
setGlowColor color (ShapeLayer s) = ShapeLayer (s { glowColor = color })

-- | Set shape layer visibility
setShapeVisible :: Boolean -> ShapeLayer -> ShapeLayer
setShapeVisible v (ShapeLayer s) = ShapeLayer (s { visible = v })

-- | Toggle shape layer visibility
toggleShapeVisible :: ShapeLayer -> ShapeLayer
toggleShapeVisible (ShapeLayer s) = ShapeLayer (s { visible = not s.visible })
  where
  not true = false
  not false = true
