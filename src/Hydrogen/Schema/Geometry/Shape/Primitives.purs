-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // geometry // shape // primitives
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Primitives — Basic geometric shape definitions.
-- |
-- | This module contains all the primitive shape types: Rectangle, Ellipse,
-- | Line, Polygon, Star, Ring, Spiral, Arrow, Cross, and Gear. Each shape
-- | is a record type with a smart constructor.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, comparison operators)
-- | - Schema.Dimension.Device (Pixel for measurements)
-- | - Schema.Geometry.Radius (corner treatments)
-- | - Shape.Types (PixelPoint2D)

module Hydrogen.Schema.Geometry.Shape.Primitives
  ( -- * Rectangle
    RectangleShape
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
  , SpiralDirection(SpiralClockwise, SpiralCounterclockwise)
  
  -- * Arrow
  , ArrowShape
  , arrowShape
  , ArrowHeadStyle(ArrowTriangle, ArrowStealth, ArrowDiamond, ArrowCircle, ArrowSquare, ArrowNone)
  
  -- * Cross
  , CrossShape
  , crossShape
  
  -- * Gear
  , GearShape
  , gearShape
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (>)
  , (<)
  )

import Hydrogen.Schema.Dimension.Device (Pixel)
import Hydrogen.Schema.Geometry.Radius (Corners) as Radius
import Hydrogen.Schema.Geometry.Shape.Types (PixelPoint2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // rectangle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangle shape with position, dimensions, and optional corner radii.
type RectangleShape =
  { center :: PixelPoint2D
  , width :: Pixel
  , height :: Pixel
  , corners :: Radius.Corners
  }

-- | Create a rectangle shape
rectangleShape :: PixelPoint2D -> Pixel -> Pixel -> Radius.Corners -> RectangleShape
rectangleShape center width height corners =
  { center, width, height, corners }

-- | Create a square shape (equal width and height)
squareShape :: PixelPoint2D -> Pixel -> Radius.Corners -> RectangleShape
squareShape center size corners =
  rectangleShape center size size corners

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // ellipse
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ellipse shape with center and radii.
-- | When radiusX == radiusY, this is a circle.
type EllipseShape =
  { center :: PixelPoint2D
  , radiusX :: Pixel
  , radiusY :: Pixel
  }

-- | Create an ellipse shape
ellipseShape :: PixelPoint2D -> Pixel -> Pixel -> EllipseShape
ellipseShape center radiusX radiusY =
  { center, radiusX, radiusY }

-- | Create a circle shape (equal radii)
circleShape :: PixelPoint2D -> Pixel -> EllipseShape
circleShape center radius =
  ellipseShape center radius radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // line
-- ═════════════════════════════════════════════════════════════════════════════

-- | Line segment from start to end point.
type LineShape =
  { start :: PixelPoint2D
  , end :: PixelPoint2D
  }

-- | Create a line shape
lineShape :: PixelPoint2D -> PixelPoint2D -> LineShape
lineShape start end = { start, end }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // polygon
-- ═════════════════════════════════════════════════════════════════════════════

-- | Regular polygon with N sides inscribed in a circle.
type PolygonShape =
  { center :: PixelPoint2D
  , radius :: Pixel        -- ^ Distance from center to vertices
  , sides :: Int           -- ^ Number of sides (minimum 3)
  , rotation :: Number     -- ^ Rotation in degrees
  }

-- | Create a polygon shape
polygonShape :: PixelPoint2D -> Pixel -> Int -> Number -> PolygonShape
polygonShape center radius sides rotation =
  { center, radius, sides: max 3 sides, rotation }
  where
    max a b = if a > b then a else b

-- | Create an equilateral triangle
triangleShape :: PixelPoint2D -> Pixel -> PolygonShape
triangleShape center radius = polygonShape center radius 3 0.0

-- | Create a regular pentagon
pentagonShape :: PixelPoint2D -> Pixel -> PolygonShape
pentagonShape center radius = polygonShape center radius 5 0.0

-- | Create a regular hexagon
hexagonShape :: PixelPoint2D -> Pixel -> PolygonShape
hexagonShape center radius = polygonShape center radius 6 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // star
-- ═════════════════════════════════════════════════════════════════════════════

-- | Star shape with configurable points and inner/outer radii.
type StarShape =
  { center :: PixelPoint2D
  , outerRadius :: Pixel    -- ^ Distance to star points
  , innerRadius :: Pixel    -- ^ Distance to inner vertices
  , points :: Int           -- ^ Number of points (minimum 3)
  , rotation :: Number      -- ^ Rotation in degrees
  }

-- | Create a star shape
starShape :: PixelPoint2D -> Pixel -> Pixel -> Int -> Number -> StarShape
starShape center outerRadius innerRadius points rotation =
  { center
  , outerRadius
  , innerRadius
  , points: max 3 points
  , rotation
  }
  where
    max a b = if a > b then a else b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // ring
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ring (donut) shape with inner and outer radii.
type RingShape =
  { center :: PixelPoint2D
  , outerRadius :: Pixel    -- ^ Outer circle radius
  , innerRadius :: Pixel    -- ^ Inner hole radius
  }

-- | Create a ring shape
ringShape :: PixelPoint2D -> Pixel -> Pixel -> RingShape
ringShape center outerRadius innerRadius =
  { center, outerRadius, innerRadius }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // spiral
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of spiral winding
data SpiralDirection
  = SpiralClockwise
  | SpiralCounterclockwise

derive instance eqSpiralDirection :: Eq SpiralDirection
derive instance ordSpiralDirection :: Ord SpiralDirection

instance showSpiralDirection :: Show SpiralDirection where
  show SpiralClockwise = "(SpiralDirection Clockwise)"
  show SpiralCounterclockwise = "(SpiralDirection Counterclockwise)"

-- | Spiral shape (Archimedean spiral)
type SpiralShape =
  { center :: PixelPoint2D
  , startRadius :: Pixel    -- ^ Starting radius
  , endRadius :: Pixel      -- ^ Ending radius
  , turns :: Number         -- ^ Number of full rotations
  , direction :: SpiralDirection
  }

-- | Create a spiral shape
spiralShape :: PixelPoint2D -> Pixel -> Pixel -> Number -> SpiralDirection -> SpiralShape
spiralShape center startRadius endRadius turns direction =
  { center, startRadius, endRadius, turns, direction }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // arrow
-- ═════════════════════════════════════════════════════════════════════════════

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
  show ArrowTriangle = "(ArrowHeadStyle Triangle)"
  show ArrowStealth = "(ArrowHeadStyle Stealth)"
  show ArrowDiamond = "(ArrowHeadStyle Diamond)"
  show ArrowCircle = "(ArrowHeadStyle Circle)"
  show ArrowSquare = "(ArrowHeadStyle Square)"
  show ArrowNone = "(ArrowHeadStyle None)"

-- | Arrow shape with configurable head and tail styles
type ArrowShape =
  { start :: PixelPoint2D
  , end :: PixelPoint2D
  , headStyle :: ArrowHeadStyle
  , tailStyle :: ArrowHeadStyle
  , headSize :: Pixel       -- ^ Size of arrow head
  , shaftWidth :: Pixel     -- ^ Width of arrow shaft
  }

-- | Create an arrow shape
arrowShape :: PixelPoint2D -> PixelPoint2D -> ArrowHeadStyle -> Pixel -> Pixel -> ArrowShape
arrowShape start end headStyle headSize shaftWidth =
  { start
  , end
  , headStyle
  , tailStyle: ArrowNone
  , headSize
  , shaftWidth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // cross
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cross/plus shape
type CrossShape =
  { center :: PixelPoint2D
  , armLength :: Pixel      -- ^ Length of each arm from center
  , armWidth :: Pixel       -- ^ Width/thickness of arms
  , rotation :: Number      -- ^ Rotation in degrees (0 = plus, 45 = X)
  }

-- | Create a cross shape
crossShape :: PixelPoint2D -> Pixel -> Pixel -> Number -> CrossShape
crossShape center armLength armWidth rotation =
  { center, armLength, armWidth, rotation }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // gear
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gear/cog shape
type GearShape =
  { center :: PixelPoint2D
  , outerRadius :: Pixel    -- ^ Radius to tooth tips
  , innerRadius :: Pixel    -- ^ Radius to tooth valleys
  , holeRadius :: Pixel     -- ^ Center hole radius
  , teeth :: Int            -- ^ Number of teeth (minimum 3)
  , toothWidth :: Number    -- ^ Tooth width ratio (0.0-1.0)
  }

-- | Create a gear shape
gearShape :: PixelPoint2D -> Pixel -> Pixel -> Pixel -> Int -> Number -> GearShape
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
