-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // canvas // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Grid — Cell-based spatial subdivision for simulation.
-- |
-- | ## Design Philosophy
-- |
-- | The canvas is divided into cells for efficient spatial queries and
-- | simulation. Paint particles, fluid dynamics, and physics all operate
-- | on this grid.
-- |
-- | ## Grid Types
-- |
-- | - **Uniform**: Equal-sized cells (fast lookup)
-- | - **Adaptive**: Variable cell sizes (octree-style, per neighborhood paper)
-- | - **Staggered**: MAC grid for fluid simulation
-- |
-- | ## Cell Indexing
-- |
-- | Cells are indexed by (x, y) integer coordinates.
-- | Linear index = y * width + x (row-major order).
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Int
-- | - Hydrogen.Schema.Canvas.Bounds

module Hydrogen.Schema.Canvas.Grid
  ( -- * Grid Configuration
    GridConfig
  , mkGridConfig
  , gridCellsX
  , gridCellsY
  , gridTotalCells
  
  -- * Cell Index
  , CellIndex
  , mkCellIndex
  , cellX
  , cellY
  , cellToLinear
  , linearToCell
  
  -- * Grid Creation
  , CanvasGrid
  , mkCanvasGrid
  , gridConfig
  , gridBounds
  , cellWidth
  , cellHeight
  
  -- * Cell Queries
  , cellAtPosition
  , cellCenterPosition
  , cellBoundsMin
  , cellBoundsMax
  , positionInCell
  
  -- * Neighbor Queries
  , cellNeighbors4
  , cellNeighbors8
  , cellsInRadius
  , isValidCell
  
  -- * Grid Traversal
  , allCellIndices
  , cellsInRow
  , cellsInColumn
  , cellsInRect
  
  -- * Display
  , displayCellIndex
  , displayGridConfig
  
  -- * Cell Utilities
  , cellsEqual
  , isOnBoundary
  , isInterior
  , isWithinBounds
  , buildCellPath
  , BoundaryType(Corner, Edge, Interior)
  , cellBoundaryType
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , max
  , min
  , mod
  , map
  , otherwise
  )

import Data.Int (floor, toNumber) as Int
import Data.Array (filter, concatMap, (..), (:)) as Array

import Hydrogen.Schema.Canvas.Bounds
  ( CanvasBounds
  , boundsWidth
  , boundsHeight
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // grid configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid configuration specifying cell counts.
type GridConfig =
  { cellsX :: Int       -- ^ Number of cells in X direction
  , cellsY :: Int       -- ^ Number of cells in Y direction
  }

-- | Create grid configuration with validation.
-- |
-- | Minimum 1 cell in each direction.
mkGridConfig :: Int -> Int -> GridConfig
mkGridConfig cx cy =
  { cellsX: max 1 cx
  , cellsY: max 1 cy
  }

-- | Get cells in X direction.
gridCellsX :: GridConfig -> Int
gridCellsX g = g.cellsX

-- | Get cells in Y direction.
gridCellsY :: GridConfig -> Int
gridCellsY g = g.cellsY

-- | Get total number of cells.
gridTotalCells :: GridConfig -> Int
gridTotalCells g = g.cellsX * g.cellsY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // cell index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index of a cell in the grid.
-- |
-- | Coordinates are 0-indexed from top-left.
newtype CellIndex = CellIndex { x :: Int, y :: Int }

derive instance eqCellIndex :: Eq CellIndex
derive instance ordCellIndex :: Ord CellIndex

instance showCellIndex :: Show CellIndex where
  show (CellIndex c) = "Cell(" <> show c.x <> "," <> show c.y <> ")"

-- | Create a cell index.
mkCellIndex :: Int -> Int -> CellIndex
mkCellIndex x y = CellIndex { x: x, y: y }

-- | Get X coordinate.
cellX :: CellIndex -> Int
cellX (CellIndex c) = c.x

-- | Get Y coordinate.
cellY :: CellIndex -> Int
cellY (CellIndex c) = c.y

-- | Convert 2D cell index to linear index.
-- |
-- | Row-major order: linear = y * width + x
cellToLinear :: GridConfig -> CellIndex -> Int
cellToLinear config (CellIndex c) = c.y * config.cellsX + c.x

-- | Convert linear index to 2D cell index.
linearToCell :: GridConfig -> Int -> CellIndex
linearToCell config linear =
  let
    x = linear `mod` config.cellsX
    y = linear / config.cellsX
  in
    CellIndex { x: x, y: y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid creation
-- ═════════════════════════════════════════════════════════════════════════════

-- | A grid overlaying canvas bounds.
type CanvasGrid =
  { config :: GridConfig
  , bounds :: CanvasBounds
  , cellW :: Number        -- ^ Cached cell width
  , cellH :: Number        -- ^ Cached cell height
  }

-- | Create a canvas grid.
mkCanvasGrid :: GridConfig -> CanvasBounds -> CanvasGrid
mkCanvasGrid config bounds =
  { config: config
  , bounds: bounds
  , cellW: boundsWidth bounds / Int.toNumber config.cellsX
  , cellH: boundsHeight bounds / Int.toNumber config.cellsY
  }

-- | Get grid configuration.
gridConfig :: CanvasGrid -> GridConfig
gridConfig g = g.config

-- | Get canvas bounds.
gridBounds :: CanvasGrid -> CanvasBounds
gridBounds g = g.bounds

-- | Get cell width in pixels.
cellWidth :: CanvasGrid -> Number
cellWidth g = g.cellW

-- | Get cell height in pixels.
cellHeight :: CanvasGrid -> Number
cellHeight g = g.cellH

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cell queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get cell at a canvas position.
-- |
-- | Returns Nothing if position is outside bounds.
cellAtPosition :: CanvasGrid -> Number -> Number -> CellIndex
cellAtPosition grid px py =
  let
    -- Calculate cell coordinates
    rawX = Int.floor (px / grid.cellW)
    rawY = Int.floor (py / grid.cellH)
    -- Clamp to valid range
    cx = max 0 (min (grid.config.cellsX - 1) rawX)
    cy = max 0 (min (grid.config.cellsY - 1) rawY)
  in
    CellIndex { x: cx, y: cy }

-- | Get center position of a cell.
cellCenterPosition :: CanvasGrid -> CellIndex -> { x :: Number, y :: Number }
cellCenterPosition grid (CellIndex c) =
  { x: (Int.toNumber c.x + 0.5) * grid.cellW
  , y: (Int.toNumber c.y + 0.5) * grid.cellH
  }

-- | Get minimum corner of cell bounds.
cellBoundsMin :: CanvasGrid -> CellIndex -> { x :: Number, y :: Number }
cellBoundsMin grid (CellIndex c) =
  { x: Int.toNumber c.x * grid.cellW
  , y: Int.toNumber c.y * grid.cellH
  }

-- | Get maximum corner of cell bounds.
cellBoundsMax :: CanvasGrid -> CellIndex -> { x :: Number, y :: Number }
cellBoundsMax grid (CellIndex c) =
  { x: Int.toNumber (c.x + 1) * grid.cellW
  , y: Int.toNumber (c.y + 1) * grid.cellH
  }

-- | Get normalized position within a cell (0-1 in each axis).
positionInCell :: CanvasGrid -> Number -> Number -> { u :: Number, v :: Number }
positionInCell grid px py =
  let
    cellMinX = Int.toNumber (Int.floor (px / grid.cellW)) * grid.cellW
    cellMinY = Int.toNumber (Int.floor (py / grid.cellH)) * grid.cellH
  in
    { u: (px - cellMinX) / grid.cellW
    , v: (py - cellMinY) / grid.cellH
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // neighbor queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get 4-connected neighbors (up, down, left, right).
cellNeighbors4 :: GridConfig -> CellIndex -> Array CellIndex
cellNeighbors4 config (CellIndex c) =
  Array.filter (isValidCellRaw config)
    [ CellIndex { x: c.x - 1, y: c.y }     -- left
    , CellIndex { x: c.x + 1, y: c.y }     -- right
    , CellIndex { x: c.x, y: c.y - 1 }     -- up
    , CellIndex { x: c.x, y: c.y + 1 }     -- down
    ]

-- | Get 8-connected neighbors (including diagonals).
cellNeighbors8 :: GridConfig -> CellIndex -> Array CellIndex
cellNeighbors8 config (CellIndex c) =
  Array.filter (isValidCellRaw config)
    [ CellIndex { x: c.x - 1, y: c.y - 1 }  -- top-left
    , CellIndex { x: c.x, y: c.y - 1 }      -- top
    , CellIndex { x: c.x + 1, y: c.y - 1 }  -- top-right
    , CellIndex { x: c.x - 1, y: c.y }      -- left
    , CellIndex { x: c.x + 1, y: c.y }      -- right
    , CellIndex { x: c.x - 1, y: c.y + 1 }  -- bottom-left
    , CellIndex { x: c.x, y: c.y + 1 }      -- bottom
    , CellIndex { x: c.x + 1, y: c.y + 1 }  -- bottom-right
    ]

-- | Get all cells within a radius (in cell units).
-- |
-- | Uses Chebyshev distance (square radius).
cellsInRadius :: GridConfig -> CellIndex -> Int -> Array CellIndex
cellsInRadius config (CellIndex center) radius =
  let
    r = max 0 radius
    minX = max 0 (center.x - r)
    maxX = min (config.cellsX - 1) (center.x + r)
    minY = max 0 (center.y - r)
    maxY = min (config.cellsY - 1) (center.y + r)
  in
    Array.concatMap
      (\y -> map (\x -> CellIndex { x: x, y: y }) (Array.(..) minX maxX))
      (Array.(..) minY maxY)

-- | Check if a cell index is valid for this grid.
isValidCell :: GridConfig -> CellIndex -> Boolean
isValidCell config cell = isValidCellRaw config cell

-- | Internal validity check.
isValidCellRaw :: GridConfig -> CellIndex -> Boolean
isValidCellRaw config (CellIndex c) =
  c.x >= 0 && c.x < config.cellsX && c.y >= 0 && c.y < config.cellsY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // grid traversal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all cell indices in row-major order.
allCellIndices :: GridConfig -> Array CellIndex
allCellIndices config =
  Array.concatMap
    (\y -> map (\x -> CellIndex { x: x, y: y }) (Array.(..) 0 (config.cellsX - 1)))
    (Array.(..) 0 (config.cellsY - 1))

-- | Get all cells in a row.
cellsInRow :: GridConfig -> Int -> Array CellIndex
cellsInRow config row =
  if row >= 0 && row < config.cellsY
    then map (\x -> CellIndex { x: x, y: row }) (Array.(..) 0 (config.cellsX - 1))
    else []

-- | Get all cells in a column.
cellsInColumn :: GridConfig -> Int -> Array CellIndex
cellsInColumn config col =
  if col >= 0 && col < config.cellsX
    then map (\y -> CellIndex { x: col, y: y }) (Array.(..) 0 (config.cellsY - 1))
    else []

-- | Get all cells in a rectangular region.
cellsInRect :: GridConfig -> CellIndex -> CellIndex -> Array CellIndex
cellsInRect config (CellIndex minC) (CellIndex maxC) =
  let
    x1 = max 0 (min minC.x maxC.x)
    x2 = min (config.cellsX - 1) (max minC.x maxC.x)
    y1 = max 0 (min minC.y maxC.y)
    y2 = min (config.cellsY - 1) (max minC.y maxC.y)
  in
    Array.concatMap
      (\y -> map (\x -> CellIndex { x: x, y: y }) (Array.(..) x1 x2))
      (Array.(..) y1 y2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display cell index as string.
displayCellIndex :: CellIndex -> String
displayCellIndex (CellIndex c) = "(" <> show c.x <> "," <> show c.y <> ")"

-- | Display grid configuration as string.
displayGridConfig :: GridConfig -> String
displayGridConfig config =
  show config.cellsX <> "x" <> show config.cellsY <> " grid (" <> show (gridTotalCells config) <> " cells)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // additional cell utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two cell indices are equal.
cellsEqual :: CellIndex -> CellIndex -> Boolean
cellsEqual (CellIndex a) (CellIndex b) = a.x == b.x && a.y == b.y

-- | Check if a cell is on the grid boundary.
isOnBoundary :: GridConfig -> CellIndex -> Boolean
isOnBoundary config (CellIndex c) =
  c.x == 0 || c.x == config.cellsX - 1 || c.y == 0 || c.y == config.cellsY - 1

-- | Check if a cell is in the interior (not on boundary).
isInterior :: GridConfig -> CellIndex -> Boolean
isInterior config (CellIndex c) =
  c.x > 0 && c.x < config.cellsX - 1 && c.y > 0 && c.y < config.cellsY - 1

-- | Check if a value is within bounds.
isWithinBounds :: Number -> Number -> Number -> Boolean
isWithinBounds value minVal maxVal = value >= minVal && value <= maxVal

-- | Build a path of cells using cons.
-- |
-- | Used for raycasting or flood fill.
buildCellPath :: CellIndex -> Array CellIndex -> Array CellIndex
buildCellPath cell path = cell Array.: path

-- | Get boundary type of a cell.
data BoundaryType
  = Corner
  | Edge
  | Interior

derive instance eqBoundaryType :: Eq BoundaryType
derive instance ordBoundaryType :: Ord BoundaryType

instance showBoundaryType :: Show BoundaryType where
  show Corner = "corner"
  show Edge = "edge"
  show Interior = "interior"

-- | Determine boundary type of a cell.
cellBoundaryType :: GridConfig -> CellIndex -> BoundaryType
cellBoundaryType config (CellIndex c)
  | isCornerCell config c = Corner
  | c.x == 0 || c.x == config.cellsX - 1 || c.y == 0 || c.y == config.cellsY - 1 = Edge
  | otherwise = Interior

-- | Check if cell coordinates represent a corner.
isCornerCell :: GridConfig -> { x :: Int, y :: Int } -> Boolean
isCornerCell config c =
  (c.x == 0 || c.x == config.cellsX - 1) && (c.y == 0 || c.y == config.cellsY - 1)
