-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // shape
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shape — Foundational geometric primitives for vector graphics.
-- |
-- | ## Design Philosophy
-- |
-- | Shapes are pure data descriptions of geometry. They compose algebraically
-- | via boolean operations and path combinations. This is the vocabulary for
-- | "Illustrator on steroids" — everything from simple rectangles to complex
-- | compound paths with boolean operations.
-- |
-- | ## Shape Categories
-- |
-- | **Primitives**: Rectangle, Circle, Ellipse, Line, Polygon, Polyline
-- | **Curves**: Bezier (cubic/quadratic), Arc, Spline, NURBS
-- | **Complex**: Star, Ring, Spiral, Arrow, Cross, Heart, Gear
-- | **Paths**: Open paths, Closed paths, Compound paths
-- | **Operations**: Union, Subtract, Intersect, Exclude, Divide
-- | **3D Extrusion**: Extrude, Revolve, Sweep, Loft
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Bounded)
-- | - Schema.Dimension.Device (Pixel for measurements)
-- | - Schema.Geometry.Radius (corner treatments)

module Hydrogen.Schema.Geometry.Shape
  ( -- * Primitive Shapes
    ShapePrimitive(..)
  
  -- * Path Primitives
  , PathCommand(..)
  , WindingRule(..)
  , ArcParams
  
  -- * Point Types
  , Point2D
  , point2D
  , origin
  
  -- * Anchor Points (for Bezier)
  , AnchorPoint
  , anchorPoint
  , smoothAnchor
  , cornerAnchor
  , symmetricAnchor
  , AnchorType(..)
  
  -- * Rectangle
  , RectangleShape
  , rectangleShape
  , squareShape
  
  -- * Circle/Ellipse
  , EllipseShape
  , ellipseShape
  , circleShape
  
  -- * Line
  , LineShape
  , lineShape
  
  -- * Polygon
  , PolygonShape
  , polygonShape
  , triangleShape
  , pentagonShape
  , hexagonShape
  
  -- * Star
  , StarShape
  , starShape
  
  -- * Ring/Donut
  , RingShape
  , ringShape
  
  -- * Spiral
  , SpiralShape
  , spiralShape
  , SpiralDirection(..)
  
  -- * Arrow
  , ArrowShape
  , arrowShape
  , ArrowHeadStyle(..)
  
  -- * Cross
  , CrossShape
  , crossShape
  
  -- * Gear
  , GearShape
  , gearShape
  
  -- * Path
  , PathShape
  , pathShape
  , closedPath
  , openPath
  
  -- * Boolean Operations
  , BooleanOp(..)
  , CompoundShape
  , compoundShape
  , unionShapes
  , subtractShapes
  , intersectShapes
  , excludeShapes
  
  -- * 3D Operations
  , ExtrudeOp
  , extrudeOp
  , RevolveOp
  , revolveOp
  , SweepOp
  , sweepOp
  
  -- * Shape Wrapper
  , Shape(..)
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , class Ring
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (>)
  , (<)
  , negate
  , map
  )

import Data.Array (length) as Array
import Data.Int (toNumber) as Int
import Data.Newtype (class Newtype)

import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Geometry.Radius (Corners) as Radius

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // point2d
-- ═══════════════════════════════════════════════════════════════════════════════

-- | A 2D point in pixel space.
-- | Represents coordinates for shape vertices and control points.
type Point2D = { x :: Pixel, y :: Pixel }

-- | Smart constructor for Point2D
point2D :: Pixel -> Pixel -> Point2D
point2D x y = { x, y }

-- | The origin point (0, 0)
origin :: Point2D
origin = { x: Pixel 0.0, y: Pixel 0.0 }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // anchor point
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Anchor point type for Bezier curve vertices.
-- | Determines how control handles behave at this vertex.
data AnchorType
  = AnchorSmooth      -- ^ Handles are colinear (C1 continuity)
  | AnchorCorner      -- ^ Handles are independent (no continuity)
  | AnchorSymmetric   -- ^ Handles are colinear and equal length

derive instance eqAnchorType :: Eq AnchorType
derive instance ordAnchorType :: Ord AnchorType

instance showAnchorType :: Show AnchorType where
  show AnchorSmooth = "smooth"
  show AnchorCorner = "corner"
  show AnchorSymmetric = "symmetric"

-- | A bezier anchor point with position and control handles.
-- | Control handles are relative to the anchor position.
type AnchorPoint =
  { position :: Point2D
  , handleIn :: Point2D    -- ^ Incoming control handle (relative)
  , handleOut :: Point2D   -- ^ Outgoing control handle (relative)
  , anchorType :: AnchorType
  }

-- | Create an anchor point with explicit handles
anchorPoint :: Point2D -> Point2D -> Point2D -> AnchorType -> AnchorPoint
anchorPoint position handleIn handleOut anchorType =
  { position, handleIn, handleOut, anchorType }

-- | Create a smooth anchor with colinear handles
smoothAnchor :: Point2D -> Point2D -> Point2D -> AnchorPoint
smoothAnchor position handleIn handleOut =
  anchorPoint position handleIn handleOut AnchorSmooth

-- | Create a corner anchor (sharp, independent handles)
cornerAnchor :: Point2D -> AnchorPoint
cornerAnchor position =
  anchorPoint position origin origin AnchorCorner

-- | Create a symmetric anchor (handles mirror each other)
symmetricAnchor :: Point2D -> Point2D -> AnchorPoint
symmetricAnchor position handle =
  anchorPoint position (negatePoint handle) handle AnchorSymmetric
  where
    negatePoint :: Point2D -> Point2D
    negatePoint { x: Pixel px, y: Pixel py } = 
      { x: Pixel (negate px), y: Pixel (negate py) }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // path commands
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Winding rule for determining inside/outside of paths.
-- | Critical for boolean operations and fill rendering.
data WindingRule
  = WindingNonZero   -- ^ Non-zero winding rule (SVG default)
  | WindingEvenOdd   -- ^ Even-odd (alternate) rule

derive instance eqWindingRule :: Eq WindingRule
derive instance ordWindingRule :: Ord WindingRule

instance showWindingRule :: Show WindingRule where
  show WindingNonZero = "nonzero"
  show WindingEvenOdd = "evenodd"

-- | Path commands following SVG path semantics.
-- | These are the atomic operations for constructing paths.
data PathCommand
  = MoveTo Point2D              -- ^ Move to point (starts new subpath)
  | LineTo Point2D              -- ^ Draw line to point
  | HorizontalTo Pixel          -- ^ Draw horizontal line to X
  | VerticalTo Pixel            -- ^ Draw vertical line to Y
  | CubicTo Point2D Point2D Point2D  -- ^ Cubic bezier (c1, c2, end)
  | QuadraticTo Point2D Point2D      -- ^ Quadratic bezier (control, end)
  | ArcTo ArcParams Point2D          -- ^ Elliptical arc to point
  | ClosePath                        -- ^ Close current subpath

derive instance eqPathCommand :: Eq PathCommand

instance showPathCommand :: Show PathCommand where
  show (MoveTo _) = "M"
  show (LineTo _) = "L"
  show (HorizontalTo _) = "H"
  show (VerticalTo _) = "V"
  show (CubicTo _ _ _) = "C"
  show (QuadraticTo _ _) = "Q"
  show (ArcTo _ _) = "A"
  show ClosePath = "Z"

-- | Parameters for elliptical arc commands
type ArcParams =
  { radiusX :: Pixel
  , radiusY :: Pixel
  , rotation :: Number       -- ^ X-axis rotation in degrees
  , largeArc :: Boolean      -- ^ Use large arc sweep
  , sweep :: Boolean         -- ^ Clockwise sweep direction
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // primitive shapes
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Enumeration of all primitive shape types.
-- | Used for type-level discrimination and pattern matching.
data ShapePrimitive
  = PrimitiveRectangle
  | PrimitiveEllipse
  | PrimitiveLine
  | PrimitivePolygon
  | PrimitiveStar
  | PrimitiveRing
  | PrimitiveSpiral
  | PrimitiveArrow
  | PrimitiveCross
  | PrimitiveGear
  | PrimitivePath

derive instance eqShapePrimitive :: Eq ShapePrimitive
derive instance ordShapePrimitive :: Ord ShapePrimitive

instance showShapePrimitive :: Show ShapePrimitive where
  show PrimitiveRectangle = "rectangle"
  show PrimitiveEllipse = "ellipse"
  show PrimitiveLine = "line"
  show PrimitivePolygon = "polygon"
  show PrimitiveStar = "star"
  show PrimitiveRing = "ring"
  show PrimitiveSpiral = "spiral"
  show PrimitiveArrow = "arrow"
  show PrimitiveCross = "cross"
  show PrimitiveGear = "gear"
  show PrimitivePath = "path"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // rectangle
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Rectangle shape with position, dimensions, and optional corner radii.
type RectangleShape =
  { center :: Point2D
  , width :: Pixel
  , height :: Pixel
  , corners :: Radius.Corners
  }

-- | Create a rectangle shape
rectangleShape :: Point2D -> Pixel -> Pixel -> Radius.Corners -> RectangleShape
rectangleShape center width height corners =
  { center, width, height, corners }

-- | Create a square shape (equal width and height)
squareShape :: Point2D -> Pixel -> Radius.Corners -> RectangleShape
squareShape center size corners =
  rectangleShape center size size corners

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // ellipse
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Ellipse shape with center and radii.
-- | When radiusX == radiusY, this is a circle.
type EllipseShape =
  { center :: Point2D
  , radiusX :: Pixel
  , radiusY :: Pixel
  }

-- | Create an ellipse shape
ellipseShape :: Point2D -> Pixel -> Pixel -> EllipseShape
ellipseShape center radiusX radiusY =
  { center, radiusX, radiusY }

-- | Create a circle shape (equal radii)
circleShape :: Point2D -> Pixel -> EllipseShape
circleShape center radius =
  ellipseShape center radius radius

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // line
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Line segment from start to end point.
type LineShape =
  { start :: Point2D
  , end :: Point2D
  }

-- | Create a line shape
lineShape :: Point2D -> Point2D -> LineShape
lineShape start end = { start, end }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // polygon
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Regular polygon with N sides inscribed in a circle.
type PolygonShape =
  { center :: Point2D
  , radius :: Pixel        -- ^ Distance from center to vertices
  , sides :: Int           -- ^ Number of sides (minimum 3)
  , rotation :: Number     -- ^ Rotation in degrees
  }

-- | Create a polygon shape
polygonShape :: Point2D -> Pixel -> Int -> Number -> PolygonShape
polygonShape center radius sides rotation =
  { center, radius, sides: max 3 sides, rotation }
  where
    max a b = if a > b then a else b

-- | Create an equilateral triangle
triangleShape :: Point2D -> Pixel -> PolygonShape
triangleShape center radius = polygonShape center radius 3 0.0

-- | Create a regular pentagon
pentagonShape :: Point2D -> Pixel -> PolygonShape
pentagonShape center radius = polygonShape center radius 5 0.0

-- | Create a regular hexagon
hexagonShape :: Point2D -> Pixel -> PolygonShape
hexagonShape center radius = polygonShape center radius 6 0.0

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // star
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Star shape with configurable points and inner/outer radii.
type StarShape =
  { center :: Point2D
  , outerRadius :: Pixel    -- ^ Distance to star points
  , innerRadius :: Pixel    -- ^ Distance to inner vertices
  , points :: Int           -- ^ Number of points (minimum 3)
  , rotation :: Number      -- ^ Rotation in degrees
  }

-- | Create a star shape
starShape :: Point2D -> Pixel -> Pixel -> Int -> Number -> StarShape
starShape center outerRadius innerRadius points rotation =
  { center
  , outerRadius
  , innerRadius
  , points: max 3 points
  , rotation
  }
  where
    max a b = if a > b then a else b

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // ring
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Ring (donut) shape with inner and outer radii.
type RingShape =
  { center :: Point2D
  , outerRadius :: Pixel    -- ^ Outer circle radius
  , innerRadius :: Pixel    -- ^ Inner hole radius
  }

-- | Create a ring shape
ringShape :: Point2D -> Pixel -> Pixel -> RingShape
ringShape center outerRadius innerRadius =
  { center, outerRadius, innerRadius }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // spiral
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Direction of spiral winding
data SpiralDirection
  = SpiralClockwise
  | SpiralCounterclockwise

derive instance eqSpiralDirection :: Eq SpiralDirection
derive instance ordSpiralDirection :: Ord SpiralDirection

instance showSpiralDirection :: Show SpiralDirection where
  show SpiralClockwise = "clockwise"
  show SpiralCounterclockwise = "counterclockwise"

-- | Spiral shape (Archimedean spiral)
type SpiralShape =
  { center :: Point2D
  , startRadius :: Pixel    -- ^ Starting radius
  , endRadius :: Pixel      -- ^ Ending radius
  , turns :: Number         -- ^ Number of full rotations
  , direction :: SpiralDirection
  }

-- | Create a spiral shape
spiralShape :: Point2D -> Pixel -> Pixel -> Number -> SpiralDirection -> SpiralShape
spiralShape center startRadius endRadius turns direction =
  { center, startRadius, endRadius, turns, direction }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // arrow
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Arrow head styles
data ArrowHeadStyle
  = ArrowTriangle       -- ^ Simple triangular head
  | ArrowStealth        -- ^ Stealth/sharp arrow head
  | ArrowDiamond        -- ^ Diamond-shaped head
  | ArrowCircle         -- ^ Circular head
  | ArrowSquare         -- ^ Square head
  | ArrowNone           -- ^ No arrow head

derive instance eqArrowHeadStyle :: Eq ArrowHeadStyle
derive instance ordArrowHeadStyle :: Ord ArrowHeadStyle

instance showArrowHeadStyle :: Show ArrowHeadStyle where
  show ArrowTriangle = "triangle"
  show ArrowStealth = "stealth"
  show ArrowDiamond = "diamond"
  show ArrowCircle = "circle"
  show ArrowSquare = "square"
  show ArrowNone = "none"

-- | Arrow shape with configurable head and tail styles
type ArrowShape =
  { start :: Point2D
  , end :: Point2D
  , headStyle :: ArrowHeadStyle
  , tailStyle :: ArrowHeadStyle
  , headSize :: Pixel       -- ^ Size of arrow head
  , shaftWidth :: Pixel     -- ^ Width of arrow shaft
  }

-- | Create an arrow shape
arrowShape :: Point2D -> Point2D -> ArrowHeadStyle -> Pixel -> Pixel -> ArrowShape
arrowShape start end headStyle headSize shaftWidth =
  { start
  , end
  , headStyle
  , tailStyle: ArrowNone
  , headSize
  , shaftWidth
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                       // cross
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cross/plus shape
type CrossShape =
  { center :: Point2D
  , armLength :: Pixel      -- ^ Length of each arm from center
  , armWidth :: Pixel       -- ^ Width/thickness of arms
  , rotation :: Number      -- ^ Rotation in degrees (0 = plus, 45 = X)
  }

-- | Create a cross shape
crossShape :: Point2D -> Pixel -> Pixel -> Number -> CrossShape
crossShape center armLength armWidth rotation =
  { center, armLength, armWidth, rotation }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // gear
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Gear/cog shape
type GearShape =
  { center :: Point2D
  , outerRadius :: Pixel    -- ^ Radius to tooth tips
  , innerRadius :: Pixel    -- ^ Radius to tooth valleys
  , holeRadius :: Pixel     -- ^ Center hole radius
  , teeth :: Int            -- ^ Number of teeth (minimum 3)
  , toothWidth :: Number    -- ^ Tooth width ratio (0.0-1.0)
  }

-- | Create a gear shape
gearShape :: Point2D -> Pixel -> Pixel -> Pixel -> Int -> Number -> GearShape
gearShape center outerRadius innerRadius holeRadius teeth toothWidth =
  { center
  , outerRadius
  , innerRadius
  , holeRadius
  , teeth: max 3 teeth
  , toothWidth: clamp01 toothWidth
  }
  where
    max a b = if a > b then a else b
    clamp01 n = if n < 0.0 then 0.0 else if n > 1.0 then 1.0 else n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                        // path
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generic path shape defined by commands
type PathShape =
  { commands :: Array PathCommand
  , windingRule :: WindingRule
  , closed :: Boolean
  }

-- | Create a path shape from commands
pathShape :: Array PathCommand -> WindingRule -> PathShape
pathShape commands windingRule =
  { commands
  , windingRule
  , closed: Array.length commands > 0
  }

-- | Create a closed path
closedPath :: Array PathCommand -> PathShape
closedPath commands =
  { commands
  , windingRule: WindingNonZero
  , closed: true
  }

-- | Create an open path
openPath :: Array PathCommand -> PathShape
openPath commands =
  { commands
  , windingRule: WindingNonZero
  , closed: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // boolean operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Boolean operations for combining shapes
data BooleanOp
  = BoolUnion           -- ^ Combine shapes (OR)
  | BoolSubtract        -- ^ Remove second from first
  | BoolIntersect       -- ^ Keep only overlap (AND)
  | BoolExclude         -- ^ Keep non-overlapping parts (XOR)
  | BoolDivide          -- ^ Split into separate pieces

derive instance eqBooleanOp :: Eq BooleanOp
derive instance ordBooleanOp :: Ord BooleanOp

instance showBooleanOp :: Show BooleanOp where
  show BoolUnion = "union"
  show BoolSubtract = "subtract"
  show BoolIntersect = "intersect"
  show BoolExclude = "exclude"
  show BoolDivide = "divide"

-- | Compound shape from boolean operations
type CompoundShape =
  { operation :: BooleanOp
  , shapes :: Array Shape
  }

-- | Create a compound shape from boolean operation
compoundShape :: BooleanOp -> Array Shape -> CompoundShape
compoundShape operation shapes = { operation, shapes }

-- | Union multiple shapes
unionShapes :: Array Shape -> CompoundShape
unionShapes = compoundShape BoolUnion

-- | Subtract shapes from first shape
subtractShapes :: Array Shape -> CompoundShape
subtractShapes = compoundShape BoolSubtract

-- | Intersect shapes
intersectShapes :: Array Shape -> CompoundShape
intersectShapes = compoundShape BoolIntersect

-- | Exclude overlapping regions
excludeShapes :: Array Shape -> CompoundShape
excludeShapes = compoundShape BoolExclude

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // 3d operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Extrude operation - extend 2D shape into 3D along Z axis
type ExtrudeOp =
  { depth :: Pixel          -- ^ Extrusion depth
  , bevel :: Pixel          -- ^ Bevel amount at edges
  , bevelSegments :: Int    -- ^ Smoothness of bevel
  }

-- | Create an extrude operation
extrudeOp :: Pixel -> Pixel -> Int -> ExtrudeOp
extrudeOp depth bevel bevelSegments =
  { depth, bevel, bevelSegments }

-- | Revolve operation - rotate 2D shape around axis to create 3D
type RevolveOp =
  { angle :: Number         -- ^ Rotation angle in degrees (360 = full revolution)
  , segments :: Int         -- ^ Number of segments for smoothness
  , axisOffset :: Pixel     -- ^ Distance of axis from shape
  }

-- | Create a revolve operation
revolveOp :: Number -> Int -> Pixel -> RevolveOp
revolveOp angle segments axisOffset =
  { angle, segments, axisOffset }

-- | Sweep operation - extrude shape along a path
type SweepOp =
  { path :: PathShape       -- ^ Path to sweep along
  , twist :: Number         -- ^ Rotation along path in degrees
  , scale :: Number         -- ^ Scale factor at end (1.0 = no change)
  }

-- | Create a sweep operation
sweepOp :: PathShape -> Number -> Number -> SweepOp
sweepOp path twist scale =
  { path, twist, scale }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // shape wrapper
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unified shape type that can hold any shape primitive
data Shape
  = ShapeRectangle RectangleShape
  | ShapeEllipse EllipseShape
  | ShapeLine LineShape
  | ShapePolygon PolygonShape
  | ShapeStar StarShape
  | ShapeRing RingShape
  | ShapeSpiral SpiralShape
  | ShapeArrow ArrowShape
  | ShapeCross CrossShape
  | ShapeGear GearShape
  | ShapePath PathShape
  | ShapeCompound CompoundShape

derive instance eqShape :: Eq Shape

instance showShape :: Show Shape where
  show (ShapeRectangle _) = "Rectangle"
  show (ShapeEllipse _) = "Ellipse"
  show (ShapeLine _) = "Line"
  show (ShapePolygon _) = "Polygon"
  show (ShapeStar _) = "Star"
  show (ShapeRing _) = "Ring"
  show (ShapeSpiral _) = "Spiral"
  show (ShapeArrow _) = "Arrow"
  show (ShapeCross _) = "Cross"
  show (ShapeGear _) = "Gear"
  show (ShapePath _) = "Path"
  show (ShapeCompound _) = "Compound"
