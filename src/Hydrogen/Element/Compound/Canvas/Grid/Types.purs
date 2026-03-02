-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // compound // canvas // grid // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core Grid Types — Bounded primitives for grid rendering.
-- |
-- | ## Bounded Parameters
-- |
-- | - **GridSpacing**: 1 to 10000 canvas units
-- | - **Subdivisions**: 1 to 10
-- | - **ZoomLevel**: 0.1 to 10.0 (10% to 1000%)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (basic operations)
-- | - Data.Array (filter, length)
-- | - Data.Int (toNumber, floor)

module Hydrogen.Element.Compound.Canvas.Grid.Types
  ( -- * Bounded Grid Spacing
    GridSpacing(GridSpacing)
  , gridSpacing
  , spacingValue
  , minSpacing
  , maxSpacing
  , defaultSpacing
  , doubleSpacing
  , halveSpacing
  , clampSpacing
  
  -- * Bounded Subdivisions
  , Subdivisions(Subdivisions)
  , subdivisions
  , subdivisionsValue
  , minSubdivisions
  , maxSubdivisions
  , noSubdivisions
  , decimalSubdivisions
  
  -- * Zoom Level
  , ZoomLevel
  , zoomLevel
  , visibleGridLevel
  , effectiveSpacing
  , shouldShowMajorLines
  , shouldShowMinorLines
  , shouldShowDots
  
  -- * Grid Lines
  , GridLine
  , gridLine
  , lineStart
  , lineEnd
  , lineIsMajor
  
  -- * Snap Point Types
  , SnapPointType(SnapMajorIntersection, SnapMinorIntersection, SnapHexCenter, SnapHexVertex, SnapPolarCenter, SnapPolarIntersection, SnapVanishingPoint, SnapCompositionPoint)
  , SnapPoint(SnapPoint)
  , snapPoint
  , snapPointPosition
  , snapPointType
  
  -- * Grid Geometry
  , GridGeometry
  , gridGeometry
  , geometryLines
  , geometrySnapPoints
  , geometryMajorLines
  , geometryMinorLines
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (>=)
  , (*)
  , (/)
  , max
  , min
  , not
  )

import Data.Array (filter, length)
import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bounded grid spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid spacing with bounds.
-- |
-- | **Bounds:**
-- | - Minimum: 1.0 canvas unit (any smaller is visual noise)
-- | - Maximum: 10000.0 canvas units (any larger is effectively no grid)
-- |
-- | At 100% zoom, 1 canvas unit = 1 pixel.
newtype GridSpacing = GridSpacing Number

derive instance eqGridSpacing :: Eq GridSpacing
derive instance ordGridSpacing :: Ord GridSpacing

instance showGridSpacing :: Show GridSpacing where
  show (GridSpacing s) = show s <> "px"

-- | Minimum allowed grid spacing.
minSpacing :: Number
minSpacing = 1.0

-- | Maximum allowed grid spacing.
maxSpacing :: Number
maxSpacing = 10000.0

-- | Create bounded grid spacing.
gridSpacing :: Number -> GridSpacing
gridSpacing n = GridSpacing (clampSpacing n)

-- | Clamp a number to valid spacing range.
clampSpacing :: Number -> Number
clampSpacing n = max minSpacing (min maxSpacing n)

-- | Extract spacing value.
spacingValue :: GridSpacing -> Number
spacingValue (GridSpacing s) = s

-- | Default grid spacing (10 pixels).
defaultSpacing :: GridSpacing
defaultSpacing = GridSpacing 10.0

-- | Double the grid spacing (zoom out grid).
doubleSpacing :: GridSpacing -> GridSpacing
doubleSpacing (GridSpacing s) = gridSpacing (s * 2.0)

-- | Halve the grid spacing (zoom in grid).
halveSpacing :: GridSpacing -> GridSpacing
halveSpacing (GridSpacing s) = gridSpacing (s / 2.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // bounded subdivisions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of subdivisions per grid cell.
-- |
-- | **Bounds:**
-- | - Minimum: 1 (no subdivision)
-- | - Maximum: 10 (decimal precision)
newtype Subdivisions = Subdivisions Int

derive instance eqSubdivisions :: Eq Subdivisions
derive instance ordSubdivisions :: Ord Subdivisions

instance showSubdivisions :: Show Subdivisions where
  show (Subdivisions n) = show n <> " subdivisions"

-- | Minimum subdivisions.
minSubdivisions :: Int
minSubdivisions = 1

-- | Maximum subdivisions.
maxSubdivisions :: Int
maxSubdivisions = 10

-- | Create bounded subdivisions.
subdivisions :: Int -> Subdivisions
subdivisions n = Subdivisions (max minSubdivisions (min maxSubdivisions n))

-- | Extract subdivision count.
subdivisionsValue :: Subdivisions -> Int
subdivisionsValue (Subdivisions n) = n

-- | No subdivisions (major lines only).
noSubdivisions :: Subdivisions
noSubdivisions = Subdivisions 1

-- | Decimal subdivisions (10ths).
decimalSubdivisions :: Subdivisions
decimalSubdivisions = Subdivisions 10

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // zoom level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom level wrapper.
-- |
-- | Bounded: 0.1 (10%) to 10.0 (1000%)
newtype ZoomLevel = ZoomLevel Number

derive instance eqZoomLevel :: Eq ZoomLevel
derive instance ordZoomLevel :: Ord ZoomLevel

instance showZoomLevel :: Show ZoomLevel where
  show (ZoomLevel z) = show (z * 100.0) <> "%"

-- | Create bounded zoom level.
zoomLevel :: Number -> ZoomLevel
zoomLevel z = ZoomLevel (max 0.1 (min 10.0 z))

-- | Determine which grid level should be visible at current zoom.
visibleGridLevel :: ZoomLevel -> Int
visibleGridLevel (ZoomLevel z)
  | z >= 2.0 = 1
  | z >= 1.0 = 2
  | z >= 0.5 = 4
  | z >= 0.25 = 8
  | otherwise = 16

-- | Calculate effective spacing at current zoom.
effectiveSpacing :: GridSpacing -> ZoomLevel -> Number
effectiveSpacing (GridSpacing spacing) zoom =
  let 
    level = visibleGridLevel zoom
    adjusted = spacing * Int.toNumber level
  in clampSpacing adjusted

-- | Should major grid lines be shown at this zoom?
shouldShowMajorLines :: ZoomLevel -> Boolean
shouldShowMajorLines (ZoomLevel z) = z >= 0.1

-- | Should minor grid lines be shown at this zoom?
shouldShowMinorLines :: ZoomLevel -> Boolean
shouldShowMinorLines (ZoomLevel z) = z >= 0.5

-- | Should dots be shown at this zoom?
shouldShowDots :: ZoomLevel -> Boolean
shouldShowDots (ZoomLevel z) = z >= 0.25

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // grid lines
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single grid line.
newtype GridLine = GridLine
  { x1 :: Number
  , y1 :: Number
  , x2 :: Number
  , y2 :: Number
  , isMajor :: Boolean
  }

derive instance eqGridLine :: Eq GridLine

instance showGridLine :: Show GridLine where
  show (GridLine l) = 
    "Line(" <> show l.x1 <> "," <> show l.y1 <> "->" <> 
    show l.x2 <> "," <> show l.y2 <> ")"

-- | Create a grid line.
gridLine :: Number -> Number -> Number -> Number -> Boolean -> GridLine
gridLine x1 y1 x2 y2 isMajor = GridLine { x1, y1, x2, y2, isMajor }

-- | Get line start point.
lineStart :: GridLine -> { x :: Number, y :: Number }
lineStart (GridLine l) = { x: l.x1, y: l.y1 }

-- | Get line end point.
lineEnd :: GridLine -> { x :: Number, y :: Number }
lineEnd (GridLine l) = { x: l.x2, y: l.y2 }

-- | Check if line is major (vs minor).
lineIsMajor :: GridLine -> Boolean
lineIsMajor (GridLine l) = l.isMajor

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // snap point types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of snap point.
data SnapPointType
  = SnapMajorIntersection   -- ^ Major grid line intersection
  | SnapMinorIntersection   -- ^ Minor grid line intersection
  | SnapHexCenter           -- ^ Center of hexagonal cell
  | SnapHexVertex           -- ^ Vertex of hexagonal cell
  | SnapPolarCenter         -- ^ Center of polar grid
  | SnapPolarIntersection   -- ^ Radial/arc intersection
  | SnapVanishingPoint      -- ^ Perspective vanishing point
  | SnapCompositionPoint    -- ^ Golden ratio / rule of thirds

derive instance eqSnapPointType :: Eq SnapPointType
derive instance ordSnapPointType :: Ord SnapPointType

instance showSnapPointType :: Show SnapPointType where
  show SnapMajorIntersection = "major"
  show SnapMinorIntersection = "minor"
  show SnapHexCenter = "hex-center"
  show SnapHexVertex = "hex-vertex"
  show SnapPolarCenter = "polar-center"
  show SnapPolarIntersection = "polar-intersection"
  show SnapVanishingPoint = "vanishing-point"
  show SnapCompositionPoint = "composition"

-- | A point that can be snapped to.
newtype SnapPoint = SnapPoint
  { x :: Number
  , y :: Number
  , pointType :: SnapPointType
  }

derive instance eqSnapPoint :: Eq SnapPoint

instance showSnapPoint :: Show SnapPoint where
  show (SnapPoint sp) = "SnapPoint(" <> show sp.x <> "," <> show sp.y <> ")"

-- | Create a snap point.
snapPoint :: Number -> Number -> SnapPointType -> SnapPoint
snapPoint x y pointType = SnapPoint { x, y, pointType }

-- | Get snap point position.
snapPointPosition :: SnapPoint -> { x :: Number, y :: Number }
snapPointPosition (SnapPoint sp) = { x: sp.x, y: sp.y }

-- | Get snap point type.
snapPointType :: SnapPoint -> SnapPointType
snapPointType (SnapPoint sp) = sp.pointType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // grid geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete grid geometry (lines + snap points).
newtype GridGeometry = GridGeometry
  { lines :: Array GridLine
  , snapPoints :: Array SnapPoint
  }

instance showGridGeometry :: Show GridGeometry where
  show (GridGeometry g) = 
    "GridGeometry(" <> show (length g.lines) <> " lines, " <>
    show (length g.snapPoints) <> " snap points)"

-- | Create grid geometry.
gridGeometry :: Array GridLine -> Array SnapPoint -> GridGeometry
gridGeometry lines snapPoints = GridGeometry { lines, snapPoints }

-- | Get all grid lines.
geometryLines :: GridGeometry -> Array GridLine
geometryLines (GridGeometry g) = g.lines

-- | Get all snap points.
geometrySnapPoints :: GridGeometry -> Array SnapPoint
geometrySnapPoints (GridGeometry g) = g.snapPoints

-- | Get only major grid lines.
geometryMajorLines :: GridGeometry -> Array GridLine
geometryMajorLines (GridGeometry g) = filter lineIsMajor g.lines

-- | Get only minor grid lines.
geometryMinorLines :: GridGeometry -> Array GridLine
geometryMinorLines (GridGeometry g) = filter isMinor g.lines
  where
    isMinor line = not (lineIsMajor line)
