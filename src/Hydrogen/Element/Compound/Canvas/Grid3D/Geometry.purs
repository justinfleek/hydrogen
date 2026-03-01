-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                          // hydrogen // grid3d // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D grid geometry generation.
-- |
-- | ## Design
-- |
-- | Generates complete 3D grid geometry including:
-- | - Grid lines for visible planes
-- | - Axis lines through origin
-- | - Snap points at intersections

module Hydrogen.Element.Compound.Canvas.Grid3D.Geometry
  ( -- * Geometry Type
    Grid3DGeometry
  , geometryLines
  , geometrySnapPoints
  , geometryAxisLines
  
  -- * Generation
  , generate3DGrid
  , generateFloorGrid
  , generateWallGrid
  , generateAxes
  
  -- * Utilities
  , mapGeo
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , (<)
  , (==)
  , (&&)
  , (||)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , negate
  )

import Data.Array (concat, snoc, length, index)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber, floor) as Int

import Hydrogen.Element.Compound.Canvas.Grid (spacingValue)

import Hydrogen.Element.Compound.Canvas.Grid3D.Types
  ( extentValue
  , WorldPlane(PlaneXY, PlaneXZ, PlaneYZ)
  , planeTangent
  , planeBitangent
  , Axis(AxisX, AxisY, AxisZ)
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Config
  ( Grid3DConfig
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Snap
  ( SnapPoint3D
  , SnapPoint3DType(Snap3DOrigin, Snap3DMajorIntersection, Snap3DMinorIntersection)
  , snapPoint3D
  )

import Hydrogen.Element.Compound.Canvas.Grid3D.Lines
  ( GridLine3D
  , gridLine3D
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // 3d grid geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D grid geometry.
newtype Grid3DGeometry = Grid3DGeometry
  { lines :: Array GridLine3D
  , snapPoints :: Array SnapPoint3D
  , axisLines :: Array GridLine3D  -- The X, Y, Z axis lines (always colored)
  }

instance showGrid3DGeometry :: Show Grid3DGeometry where
  show (Grid3DGeometry g) =
    "Grid3D(" <> show (length g.lines) <> " lines, " <>
    show (length g.snapPoints) <> " snaps)"

-- | Extract grid lines from geometry.
geometryLines :: Grid3DGeometry -> Array GridLine3D
geometryLines (Grid3DGeometry g) = g.lines

-- | Extract snap points from geometry.
geometrySnapPoints :: Grid3DGeometry -> Array SnapPoint3D
geometrySnapPoints (Grid3DGeometry g) = g.snapPoints

-- | Extract axis lines from geometry.
geometryAxisLines :: Grid3DGeometry -> Array GridLine3D
geometryAxisLines (Grid3DGeometry g) = g.axisLines

-- | Generate complete 3D grid.
generate3DGrid :: Grid3DConfig -> Grid3DGeometry
generate3DGrid config =
  let
    spacing' = spacingValue config.spacing
    extent' = extentValue config.extent
    
    -- Generate grid lines for each visible plane
    xyLines = if config.showXY 
              then generatePlaneGrid PlaneXY spacing' extent' 
              else []
    xzLines = if config.showXZ 
              then generatePlaneGrid PlaneXZ spacing' extent' 
              else []
    yzLines = if config.showYZ 
              then generatePlaneGrid PlaneYZ spacing' extent' 
              else []
    
    -- Generate axis lines
    axes = if config.showAxes 
           then generateAxes (extentValue config.axisLength)
           else []
    
    -- Origin snap point (always present)
    originSnap = snapPoint3D 0.0 0.0 0.0 Snap3DOrigin Nothing
    
    -- Generate snap points at grid intersections for each visible plane
    xySnaps = if config.showXY 
              then generate3DPlaneSnapPoints PlaneXY spacing' extent'
              else []
    xzSnaps = if config.showXZ 
              then generate3DPlaneSnapPoints PlaneXZ spacing' extent'
              else []
    yzSnaps = if config.showYZ 
              then generate3DPlaneSnapPoints PlaneYZ spacing' extent'
              else []
    
    allSnaps = concat [xySnaps, xzSnaps, yzSnaps, [originSnap]]
    
  in Grid3DGeometry
    { lines: concat [xyLines, xzLines, yzLines]
    , snapPoints: allSnaps
    , axisLines: axes
    }

-- | Generate floor (XY plane) grid centered at origin.
generateFloorGrid :: Number -> Number -> Array GridLine3D
generateFloorGrid = generatePlaneGrid PlaneXY

-- | Generate wall (XZ or YZ plane) grid.
generateWallGrid :: WorldPlane -> Number -> Number -> Array GridLine3D
generateWallGrid plane spacing extent' =
  if plane == PlaneXY 
    then []  -- XY is floor, not wall
    else generatePlaneGrid plane spacing extent'

-- | Generate the three axis lines through origin.
-- |
-- | Each axis extends from -length to +length through origin.
generateAxes :: Number -> Array GridLine3D
generateAxes length' =
  [ -- X axis (Red)
    gridLine3D (negate length') 0.0 0.0 length' 0.0 0.0 true (Just AxisX)
  , -- Y axis (Green)
    gridLine3D 0.0 (negate length') 0.0 0.0 length' 0.0 true (Just AxisY)
  , -- Z axis (Blue)
    gridLine3D 0.0 0.0 (negate length') 0.0 0.0 length' true (Just AxisZ)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // internal generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate grid lines for a world plane.
generatePlaneGrid :: WorldPlane -> Number -> Number -> Array GridLine3D
generatePlaneGrid plane spacing extent' =
  let
    -- Number of lines in each direction
    count = Int.floor (extent' / spacing)
    
    tangent = planeTangent plane
    bitangent = planeBitangent plane
  in concat 
    [ generateParallelLines plane spacing extent' tangent bitangent count
    , generateParallelLines plane spacing extent' bitangent tangent count
    ]

-- | Generate parallel lines along one direction.
generateParallelLines :: WorldPlane 
                      -> Number 
                      -> Number 
                      -> { x :: Number, y :: Number, z :: Number }  -- Direction of lines
                      -> { x :: Number, y :: Number, z :: Number }  -- Perpendicular direction
                      -> Int 
                      -> Array GridLine3D
generateParallelLines plane spacing extent' lineDir perpDir count =
  generateLinesHelper plane spacing extent' lineDir perpDir (negate count) count []

generateLinesHelper :: WorldPlane 
                    -> Number 
                    -> Number 
                    -> { x :: Number, y :: Number, z :: Number }
                    -> { x :: Number, y :: Number, z :: Number }
                    -> Int 
                    -> Int 
                    -> Array GridLine3D 
                    -> Array GridLine3D
generateLinesHelper plane spacing extent' lineDir perpDir current maxCount acc =
  if current > maxCount then acc
  else
    let
      offset = Int.toNumber current * spacing
      -- Start and end points
      startX = lineDir.x * (negate extent') + perpDir.x * offset
      startY = lineDir.y * (negate extent') + perpDir.y * offset
      startZ = lineDir.z * (negate extent') + perpDir.z * offset
      endX = lineDir.x * extent' + perpDir.x * offset
      endY = lineDir.y * extent' + perpDir.y * offset
      endZ = lineDir.z * extent' + perpDir.z * offset
      
      isMajor = current == 0 || modInt current 5 == 0  -- Every 5th line is major
      
      line = gridLine3D startX startY startZ endX endY endZ isMajor Nothing
      newAcc = snoc acc line
    in generateLinesHelper plane spacing extent' lineDir perpDir (current + 1) maxCount newAcc

-- | Integer modulo.
modInt :: Int -> Int -> Int
modInt a b = a - (Int.floor (Int.toNumber a / Int.toNumber b) * b)

-- | Generate snap points for a 3D grid plane.
-- |
-- | Creates snap points at grid intersections on the specified plane.
-- | Points are generated at (spacing) intervals from -extent to +extent.
generate3DPlaneSnapPoints :: WorldPlane -> Number -> Number -> Array SnapPoint3D
generate3DPlaneSnapPoints plane spacing extent' =
  let
    -- Number of steps from -extent to +extent
    numSteps = Int.floor (extent' * 2.0 / spacing) + 1
    startVal = negate extent'
  in generate3DPlaneHelper plane spacing startVal extent' startVal numSteps []

-- | Helper for 3D plane snap point generation.
generate3DPlaneHelper :: WorldPlane -> Number -> Number -> Number -> Number -> Int -> Array SnapPoint3D -> Array SnapPoint3D
generate3DPlaneHelper plane spacing startVal endVal currentU _numSteps acc =
  if currentU > endVal then acc
  else
    let 
      rowPoints = generate3DPlaneRow plane spacing currentU startVal endVal []
      newAcc = concat [acc, rowPoints]
    in generate3DPlaneHelper plane spacing startVal endVal (currentU + spacing) _numSteps newAcc

-- | Generate snap points for a single row on a 3D plane.
generate3DPlaneRow :: WorldPlane -> Number -> Number -> Number -> Number -> Array SnapPoint3D -> Array SnapPoint3D
generate3DPlaneRow plane spacing u startVal endVal acc =
  generate3DPlaneRowHelper plane u startVal endVal spacing acc

generate3DPlaneRowHelper :: WorldPlane -> Number -> Number -> Number -> Number -> Array SnapPoint3D -> Array SnapPoint3D
generate3DPlaneRowHelper plane u currentV endVal spacing acc =
  if currentV > endVal then acc
  else
    let
      -- Determine if this is a major intersection (at integer multiples of major spacing)
      isMajor = isMajorIntersection u spacing && isMajorIntersection currentV spacing
      pointType = if isMajor then Snap3DMajorIntersection else Snap3DMinorIntersection
      
      -- Create point based on plane
      point = case plane of
        PlaneXY -> snapPoint3D u currentV 0.0 pointType (Just PlaneXY)
        PlaneXZ -> snapPoint3D u 0.0 currentV pointType (Just PlaneXZ)
        PlaneYZ -> snapPoint3D 0.0 u currentV pointType (Just PlaneYZ)
      
      newAcc = snoc acc point
    in generate3DPlaneRowHelper plane u (currentV + spacing) endVal spacing newAcc

-- | Check if a coordinate is at a major intersection.
isMajorIntersection :: Number -> Number -> Boolean
isMajorIntersection coord spacing =
  let
    majorSpacing = spacing * 5.0  -- Major lines every 5 minor lines
    ratio = coord / majorSpacing
    rounded = Int.toNumber (Int.floor (ratio + 0.5))
  in absGeo (ratio - rounded) < 0.01

-- | Absolute value.
absGeo :: Number -> Number
absGeo n = if n < 0.0 then negate n else n

-- | Map for geometry arrays (avoids Functor import).
mapGeo :: forall a b. (a -> b) -> Array a -> Array b
mapGeo f arr = mapGeoHelper f arr 0 []

mapGeoHelper :: forall a b. (a -> b) -> Array a -> Int -> Array b -> Array b
mapGeoHelper f arr idx acc =
  case index arr idx of
    Nothing -> acc
    Just x -> mapGeoHelper f arr (idx + 1) (snoc acc (f x))
