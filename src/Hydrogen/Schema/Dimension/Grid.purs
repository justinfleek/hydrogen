-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // dimension // grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grid — Column and row layout configuration.
-- |
-- | **WHY GRID?**
-- | Grid defines the structure of a 2D grid layout:
-- | - Number of columns
-- | - Number of rows (optional, often auto)
-- | - Gap between items
-- |
-- | **Use cases:**
-- | - CSS Grid layout
-- | - Design system column grids
-- | - Dashboard layouts
-- | - Photo galleries
-- | - Card grids
-- |
-- | **Related CSS:**
-- | - grid-template-columns
-- | - grid-template-rows
-- | - gap, column-gap, row-gap

module Hydrogen.Schema.Dimension.Grid
  ( -- * Types
    Grid(Grid)
  , GridTrack(Fixed, Fr, MinMax, Auto, FitContent)
  , GridGap
  
  -- * Constructors
  , grid
  , gridFromRecord
  , gridColumns
  , gridEqual
  
  -- * Common Grids
  , grid12Column
  , grid3Column
  , grid4Column
  , gridAuto
  
  -- * Accessors
  , columns
  , rows
  , columnGap
  , rowGap
  , toRecord
  
  -- * Track Constructors
  , trackFixed
  , trackFr
  , trackMinMax
  , trackAuto
  , trackFitContent
  
  -- * Operations
  , setColumns
  , setRows
  , setGap
  , setColumnGap
  , setRowGap
  
  -- * Calculations
  , columnWidth
  , totalGapWidth
  , contentWidth
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  , (<$>)
  )

import Data.Array (length, intercalate, replicate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // gridtrack
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single grid track definition.
-- |
-- | Tracks define column or row sizes.
data GridTrack
  = Fixed Number           -- ^ Fixed pixel width
  | Fr Number              -- ^ Fractional unit (flexible)
  | MinMax Number Number   -- ^ minmax(min, max)
  | Auto                   -- ^ auto (content-sized)
  | FitContent Number      -- ^ fit-content(max)

derive instance eqGridTrack :: Eq GridTrack

instance showGridTrack :: Show GridTrack where
  show (Fixed n) = "Fixed " <> show n
  show (Fr n) = "Fr " <> show n
  show (MinMax min' max') = "MinMax " <> show min' <> " " <> show max'
  show Auto = "Auto"
  show (FitContent n) = "FitContent " <> show n

-- | Gap configuration (column gap, row gap).
type GridGap = { column :: Number, row :: Number }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // grid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grid layout configuration.
data Grid = Grid
  { columns :: Array GridTrack
  , rows :: Array GridTrack
  , gap :: GridGap
  }

derive instance eqGrid :: Eq Grid

instance showGrid :: Show Grid where
  show g = "Grid(" <> show (length (columns g)) <> " cols × " 
    <> show (length (rows g)) <> " rows)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a grid with explicit columns, rows, and gap.
grid :: Array GridTrack -> Array GridTrack -> GridGap -> Grid
grid cols rws g = Grid { columns: cols, rows: rws, gap: g }

-- | Create from a record.
gridFromRecord :: { columns :: Array GridTrack, rows :: Array GridTrack, gap :: GridGap } -> Grid
gridFromRecord = Grid

-- | Create a grid with specified column tracks and auto rows.
gridColumns :: Array GridTrack -> Number -> Grid
gridColumns cols gapSize = Grid
  { columns: cols
  , rows: []
  , gap: { column: gapSize, row: gapSize }
  }

-- | Create a grid with equal-width columns.
-- |
-- | ```purescript
-- | gridEqual 3 16.0  -- 3 equal columns with 16px gap
-- | ```
gridEqual :: Int -> Number -> Grid
gridEqual count gapSize = Grid
  { columns: replicate count (Fr 1.0)
  , rows: []
  , gap: { column: gapSize, row: gapSize }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // common grids
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard 12-column grid.
-- |
-- | Common in Bootstrap, Foundation, and other frameworks.
grid12Column :: Number -> Grid
grid12Column gapSize = gridEqual 12 gapSize

-- | 3-column grid.
grid3Column :: Number -> Grid
grid3Column gapSize = gridEqual 3 gapSize

-- | 4-column grid.
grid4Column :: Number -> Grid
grid4Column gapSize = gridEqual 4 gapSize

-- | Auto-fill grid (responsive columns).
-- |
-- | Creates as many columns as fit with minimum width.
gridAuto :: Number -> Number -> Grid
gridAuto minColWidth gapSize = Grid
  { columns: [MinMax minColWidth 1.0]  -- Will need repeat(auto-fill, ...) in CSS
  , rows: []
  , gap: { column: gapSize, row: gapSize }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get column tracks.
columns :: Grid -> Array GridTrack
columns (Grid g) = g.columns

-- | Get row tracks.
rows :: Grid -> Array GridTrack
rows (Grid g) = g.rows

-- | Get column gap.
columnGap :: Grid -> Number
columnGap (Grid g) = g.gap.column

-- | Get row gap.
rowGap :: Grid -> Number
rowGap (Grid g) = g.gap.row

-- | Convert to record.
toRecord :: Grid -> { columns :: Array GridTrack, rows :: Array GridTrack, gap :: GridGap }
toRecord (Grid g) = g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // track constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a fixed-width track.
trackFixed :: Number -> GridTrack
trackFixed = Fixed

-- | Create a fractional track.
trackFr :: Number -> GridTrack
trackFr = Fr

-- | Create a minmax track.
trackMinMax :: Number -> Number -> GridTrack
trackMinMax = MinMax

-- | Create an auto track.
trackAuto :: GridTrack
trackAuto = Auto

-- | Create a fit-content track.
trackFitContent :: Number -> GridTrack
trackFitContent = FitContent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set column tracks.
setColumns :: Array GridTrack -> Grid -> Grid
setColumns cols (Grid g) = Grid (g { columns = cols })

-- | Set row tracks.
setRows :: Array GridTrack -> Grid -> Grid
setRows rws (Grid g) = Grid (g { rows = rws })

-- | Set both gaps to the same value.
setGap :: Number -> Grid -> Grid
setGap n (Grid g) = Grid (g { gap = { column: n, row: n } })

-- | Set column gap.
setColumnGap :: Number -> Grid -> Grid
setColumnGap n (Grid g) = Grid (g { gap = g.gap { column = n } })

-- | Set row gap.
setRowGap :: Number -> Grid -> Grid
setRowGap n (Grid g) = Grid (g { gap = g.gap { row = n } })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate width of each column given container width.
-- |
-- | Only works for equal-fr grids. Returns 0.0 for complex grids.
columnWidth :: Number -> Grid -> Number
columnWidth containerWidth (Grid g) =
  let numCols = length g.columns
      totalGap = intToNum (numCols - 1) * g.gap.column
      availableWidth = containerWidth - totalGap
  in if numCols == 0 then 0.0 else availableWidth / intToNum numCols

-- | Calculate total gap width between columns.
totalGapWidth :: Grid -> Number
totalGapWidth (Grid g) =
  let numCols = length g.columns
      numGaps = if numCols > 1 then numCols - 1 else 0
  in intToNum numGaps * g.gap.column

-- | Calculate content width (container width minus gaps).
contentWidth :: Number -> Grid -> Number
contentWidth containerWidth g = containerWidth - totalGapWidth g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number
intToNum :: Int -> Number
intToNum i = intToNumber i
  where
  intToNumber :: Int -> Number
  intToNumber n
    | n == 0 = 0.0
    | n > 0 = 1.0 + intToNumber (n - 1)
    | otherwise = intToNumber (n + 1) - 1.0
