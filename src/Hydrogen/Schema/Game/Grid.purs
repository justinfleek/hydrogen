-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // game // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid — Foundational coordinate system for ALL board games.
-- |
-- | Every board game operates on a coordinate system. Chess squares, Go
-- | intersections, hex cells — they all derive from bounded grid coordinates.
-- |
-- | - Coordinates bounded 0-999 (sufficient for any practical board)
-- | - Dimensions bounded 1-999 (boards must have positive size)
-- | - Pure math with no side effects
-- | - Deterministic identity via UUID5

module Hydrogen.Schema.Game.Grid
  ( -- * Coordinate Types
    GridX(GridX), GridY(GridY), GridCoord
  -- * Dimension Types
  , GridWidth(GridWidth), GridHeight(GridHeight), GridSize
  -- * Coordinate Systems
  , CoordSystem(Cartesian, Screen, Chess, Go, Hex)
  -- * Smart Constructors
  , gridX, gridY, gridCoord, gridWidth, gridHeight, gridSize
  -- * Bounds
  , gridXBounds, gridYBounds, gridWidthBounds, gridHeightBounds
  -- * Accessors
  , unwrapGridX, unwrapGridY, unwrapGridWidth, unwrapGridHeight
  -- * Predicates
  , isValidCoord, isInBounds, isCorner, isEdge, isCenter
  -- * Arithmetic
  , addCoords, subtractCoords, scaleCoord
  -- * Distance
  , manhattanDistance, chebyshevDistance, euclideanDistance
  -- * Neighbors
  , orthogonalNeighbors, diagonalNeighbors, allNeighbors
  -- * Standard Sizes
  , chessBoard, goBoard19, goBoard13, goBoard9, checkerBoard
  -- * UUID5 Identity
  , gridCoordUUID5Namespace, gridCoordIdentity
  ) where

import Prelude
  ( class Eq, class Ord, class Show, show, max, map, div
  , (#), (+), (-), (*), (&&), (||), (<), (>), (<=), (>=), (==), (<>)
  )
import Data.Array (filter) as Array
import Data.Number (sqrt) as Num
import Data.Int (toNumber) as Int
import Data.Ord (abs) as Ord
import Hydrogen.Schema.Bounded
  ( IntBounds, BoundsBehavior(Clamps), clampInt, intBounds )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // coordinate // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid X coordinate, bounded 0-999. Zero is leftmost column.
newtype GridX = GridX Int

derive instance eqGridX :: Eq GridX
derive instance ordGridX :: Ord GridX

instance showGridX :: Show GridX where
  show (GridX n) = "GridX(" <> show n <> ")"

-- | Grid Y coordinate, bounded 0-999.
newtype GridY = GridY Int

derive instance eqGridY :: Eq GridY
derive instance ordGridY :: Ord GridY

instance showGridY :: Show GridY where
  show (GridY n) = "GridY(" <> show n <> ")"

-- | Combined grid coordinate with X and Y components.
type GridCoord = { x :: GridX, y :: GridY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // dimension // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid width, bounded 1-999. Number of columns on board.
newtype GridWidth = GridWidth Int

derive instance eqGridWidth :: Eq GridWidth
derive instance ordGridWidth :: Ord GridWidth

instance showGridWidth :: Show GridWidth where
  show (GridWidth n) = "GridWidth(" <> show n <> ")"

-- | Grid height, bounded 1-999. Number of rows on board.
newtype GridHeight = GridHeight Int

derive instance eqGridHeight :: Eq GridHeight
derive instance ordGridHeight :: Ord GridHeight

instance showGridHeight :: Show GridHeight where
  show (GridHeight n) = "GridHeight(" <> show n <> ")"

-- | Grid size combining width and height.
type GridSize = { width :: GridWidth, height :: GridHeight }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // coordinate // systems
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coordinate system conventions.
-- | - Cartesian: Origin bottom-left, Y increases upward
-- | - Screen: Origin top-left, Y increases downward  
-- | - Chess: Files a-h (X 0-7), Ranks 1-8 (Y 0-7)
-- | - Go: 19x19/13x13/9x9 intersections, 1-indexed
-- | - Hex: Axial coordinates for hexagonal grids
data CoordSystem = Cartesian | Screen | Chess | Go | Hex

derive instance eqCoordSystem :: Eq CoordSystem
derive instance ordCoordSystem :: Ord CoordSystem

instance showCoordSystem :: Show CoordSystem where
  show Cartesian = "Cartesian"
  show Screen = "Screen"
  show Chess = "Chess"
  show Go = "Go"
  show Hex = "Hex"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // smart // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create GridX, clamping to [0, 999].
gridX :: Int -> GridX
gridX n = GridX (clampInt 0 999 n)

-- | Create GridY, clamping to [0, 999].
gridY :: Int -> GridY
gridY n = GridY (clampInt 0 999 n)

-- | Create GridCoord from two Ints.
gridCoord :: Int -> Int -> GridCoord
gridCoord xVal yVal = { x: gridX xVal, y: gridY yVal }

-- | Create GridWidth, clamping to [1, 999].
gridWidth :: Int -> GridWidth
gridWidth n = GridWidth (clampInt 1 999 n)

-- | Create GridHeight, clamping to [1, 999].
gridHeight :: Int -> GridHeight
gridHeight n = GridHeight (clampInt 1 999 n)

-- | Create GridSize from two Ints.
gridSize :: Int -> Int -> GridSize
gridSize w h = { width: gridWidth w, height: gridHeight h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for GridX: [0, 999], Clamps.
gridXBounds :: IntBounds
gridXBounds = intBounds 0 999 Clamps "gridX" "Grid X coordinate from 0 to 999"

-- | Bounds for GridY: [0, 999], Clamps.
gridYBounds :: IntBounds
gridYBounds = intBounds 0 999 Clamps "gridY" "Grid Y coordinate from 0 to 999"

-- | Bounds for GridWidth: [1, 999], Clamps.
gridWidthBounds :: IntBounds
gridWidthBounds = intBounds 1 999 Clamps "gridWidth" "Grid width from 1 to 999"

-- | Bounds for GridHeight: [1, 999], Clamps.
gridHeightBounds :: IntBounds
gridHeightBounds = intBounds 1 999 Clamps "gridHeight" "Grid height from 1 to 999"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract Int from GridX. Result in [0, 999].
unwrapGridX :: GridX -> Int
unwrapGridX (GridX n) = n

-- | Extract Int from GridY. Result in [0, 999].
unwrapGridY :: GridY -> Int
unwrapGridY (GridY n) = n

-- | Extract Int from GridWidth. Result in [1, 999].
unwrapGridWidth :: GridWidth -> Int
unwrapGridWidth (GridWidth n) = n

-- | Extract Int from GridHeight. Result in [1, 999].
unwrapGridHeight :: GridHeight -> Int
unwrapGridHeight (GridHeight n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if raw integers are valid coordinates (within 0-999).
isValidCoord :: Int -> Int -> Boolean
isValidCoord xVal yVal = 
  xVal >= 0 && xVal <= 999 && yVal >= 0 && yVal <= 999

-- | Check if coordinate is within grid bounds.
isInBounds :: GridSize -> GridCoord -> Boolean
isInBounds size coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      w = unwrapGridWidth size.width
      h = unwrapGridHeight size.height
  in xVal >= 0 && xVal < w && yVal >= 0 && yVal < h

-- | Check if coordinate is a corner of the grid.
isCorner :: GridSize -> GridCoord -> Boolean
isCorner size coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      w = unwrapGridWidth size.width
      h = unwrapGridHeight size.height
      maxX = w - 1
      maxY = h - 1
      isXCorner = xVal == 0 || xVal == maxX
      isYCorner = yVal == 0 || yVal == maxY
  in isXCorner && isYCorner && isInBounds size coord

-- | Check if coordinate is on the edge of the grid.
isEdge :: GridSize -> GridCoord -> Boolean
isEdge size coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      w = unwrapGridWidth size.width
      h = unwrapGridHeight size.height
      maxX = w - 1
      maxY = h - 1
  in isInBounds size coord && 
     (xVal == 0 || xVal == maxX || yVal == 0 || yVal == maxY)

-- | Check if coordinate is at center of grid.
isCenter :: GridSize -> GridCoord -> Boolean
isCenter size coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      w = unwrapGridWidth size.width
      h = unwrapGridHeight size.height
      centerX = (w - 1) `div` 2
      centerY = (h - 1) `div` 2
  in xVal == centerX && yVal == centerY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arithmetic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two coordinates component-wise, clamping result.
addCoords :: GridCoord -> GridCoord -> GridCoord
addCoords c1 c2 =
  let xVal = unwrapGridX c1.x + unwrapGridX c2.x
      yVal = unwrapGridY c1.y + unwrapGridY c2.y
  in gridCoord xVal yVal

-- | Subtract second from first, clamping result. Negatives clamp to 0.
subtractCoords :: GridCoord -> GridCoord -> GridCoord
subtractCoords c1 c2 =
  let xVal = unwrapGridX c1.x - unwrapGridX c2.x
      yVal = unwrapGridY c1.y - unwrapGridY c2.y
  in gridCoord xVal yVal

-- | Scale coordinate by factor, clamping result. Negative factors become 0.
scaleCoord :: Int -> GridCoord -> GridCoord
scaleCoord factor coord =
  let f = if factor < 0 then 0 else factor
      xVal = unwrapGridX coord.x * f
      yVal = unwrapGridY coord.y * f
  in gridCoord xVal yVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Manhattan distance (L1). Sum of absolute differences.
manhattanDistance :: GridCoord -> GridCoord -> Int
manhattanDistance c1 c2 =
  let dx = Ord.abs (unwrapGridX c1.x - unwrapGridX c2.x)
      dy = Ord.abs (unwrapGridY c1.y - unwrapGridY c2.y)
  in dx + dy

-- | Chebyshev distance (L-infinity). Max of absolute differences.
chebyshevDistance :: GridCoord -> GridCoord -> Int
chebyshevDistance c1 c2 =
  let dx = Ord.abs (unwrapGridX c1.x - unwrapGridX c2.x)
      dy = Ord.abs (unwrapGridY c1.y - unwrapGridY c2.y)
  in max dx dy

-- | Euclidean distance (L2). Straight-line distance.
euclideanDistance :: GridCoord -> GridCoord -> Number
euclideanDistance c1 c2 =
  let dx = Int.toNumber (unwrapGridX c1.x - unwrapGridX c2.x)
      dy = Int.toNumber (unwrapGridY c1.y - unwrapGridY c2.y)
  in Num.sqrt (dx * dx + dy * dy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // neighbors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get orthogonal (N, E, S, W) neighbors. Up to 4, excludes out-of-bounds.
orthogonalNeighbors :: GridCoord -> Array GridCoord
orthogonalNeighbors coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      candidates =
        [ { x: xVal, y: yVal + 1 }      -- N
        , { x: xVal + 1, y: yVal }      -- E
        , { x: xVal, y: yVal - 1 }      -- S
        , { x: xVal - 1, y: yVal }      -- W
        ]
  in candidates # Array.filter isValidRaw # map rawToCoord

-- | Get diagonal (NE, SE, SW, NW) neighbors. Up to 4, excludes out-of-bounds.
diagonalNeighbors :: GridCoord -> Array GridCoord
diagonalNeighbors coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      candidates =
        [ { x: xVal + 1, y: yVal + 1 }  -- NE
        , { x: xVal + 1, y: yVal - 1 }  -- SE
        , { x: xVal - 1, y: yVal - 1 }  -- SW
        , { x: xVal - 1, y: yVal + 1 }  -- NW
        ]
  in candidates # Array.filter isValidRaw # map rawToCoord

-- | Get all 8 neighbors. Excludes out-of-bounds.
allNeighbors :: GridCoord -> Array GridCoord
allNeighbors coord =
  let xVal = unwrapGridX coord.x
      yVal = unwrapGridY coord.y
      candidates =
        [ { x: xVal, y: yVal + 1 }      -- N
        , { x: xVal + 1, y: yVal + 1 }  -- NE
        , { x: xVal + 1, y: yVal }      -- E
        , { x: xVal + 1, y: yVal - 1 }  -- SE
        , { x: xVal, y: yVal - 1 }      -- S
        , { x: xVal - 1, y: yVal - 1 }  -- SW
        , { x: xVal - 1, y: yVal }      -- W
        , { x: xVal - 1, y: yVal + 1 }  -- NW
        ]
  in candidates # Array.filter isValidRaw # map rawToCoord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // standard sizes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard 8x8 chess board. 64 squares.
chessBoard :: GridSize
chessBoard = gridSize 8 8

-- | Standard 19x19 Go board. 361 intersections. Tengen at (9,9).
goBoard19 :: GridSize
goBoard19 = gridSize 19 19

-- | Medium 13x13 Go board. 169 intersections.
goBoard13 :: GridSize
goBoard13 = gridSize 13 13

-- | Small 9x9 Go board. 81 intersections.
goBoard9 :: GridSize
goBoard9 = gridSize 9 9

-- | Standard 8x8 checker board. 32 playable dark squares.
checkerBoard :: GridSize
checkerBoard = gridSize 8 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // uuid5 identity
-- ═════════════════════════════════════════════════════════════════════════════

-- | UUID5 namespace for grid coordinates.
gridCoordUUID5Namespace :: String
gridCoordUUID5Namespace = "hydrogen.schema.game.grid.coord"

-- | Deterministic identity string for coordinate. Same coord = same string.
gridCoordIdentity :: GridCoord -> String
gridCoordIdentity coord =
  show (unwrapGridX coord.x) <> "," <> show (unwrapGridY coord.y)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if raw x,y values are valid coordinates.
isValidRaw :: { x :: Int, y :: Int } -> Boolean
isValidRaw { x: xVal, y: yVal } = 
  xVal >= 0 && xVal <= 999 && yVal >= 0 && yVal <= 999

-- | Convert raw coordinate record to GridCoord.
rawToCoord :: { x :: Int, y :: Int } -> GridCoord
rawToCoord { x: xVal, y: yVal } = gridCoord xVal yVal
