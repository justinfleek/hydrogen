-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // element // table // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Types — Core data types for tabular data display.
-- |
-- | ## Overview
-- |
-- | This module defines the fundamental types used throughout the Table widget:
-- | - Column types and definitions
-- | - Cell values with rich content support
-- | - Sort direction
-- | - Pagination state
-- | - Complete table data payload

module Hydrogen.Element.Compound.Widget.Table.Types
  ( -- * Column Types
    ColumnType
      ( ColText
      , ColNumber
      , ColCurrency
      , ColPercent
      , ColDate
      , ColDatetime
      , ColBoolean
      , ColBadge
      , ColSparkline
      , ColProgress
      )
  , columnTypeToString
  
  -- * Sort Direction
  , SortDirection
      ( SortAsc
      , SortDesc
      )
  , sortDirectionToString
  , toggleSort
  
  -- * Cell Values
  , CellValue
      ( TextCell
      , NumberCell
      , CurrencyCell
      , PercentCell
      , DateCell
      , BoolCell
      , BadgeCell
      , SparklineCell
      , ProgressCell
      , EmptyCell
      )
  
  -- * Data Structures
  , ColumnDef
  , Pagination
  , TableData
  
  -- * Default Values
  , defaultColumn
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )


import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Element.Compound.Widget.Types (Percentage, unwrapPercentage)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // column types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Column data types.
-- |
-- | Determines how cell values are formatted and displayed.
data ColumnType
  = ColText
  | ColNumber
  | ColCurrency
  | ColPercent
  | ColDate
  | ColDatetime
  | ColBoolean
  | ColBadge
  | ColSparkline
  | ColProgress

derive instance eqColumnType :: Eq ColumnType

instance showColumnType :: Show ColumnType where
  show = columnTypeToString

-- | Convert column type to string.
columnTypeToString :: ColumnType -> String
columnTypeToString ct = case ct of
  ColText -> "text"
  ColNumber -> "number"
  ColCurrency -> "currency"
  ColPercent -> "percent"
  ColDate -> "date"
  ColDatetime -> "datetime"
  ColBoolean -> "boolean"
  ColBadge -> "badge"
  ColSparkline -> "sparkline"
  ColProgress -> "progress"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sort direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sort direction.
data SortDirection
  = SortAsc
  | SortDesc

derive instance eqSortDirection :: Eq SortDirection

instance showSortDirection :: Show SortDirection where
  show = sortDirectionToString

-- | Convert sort direction to string.
sortDirectionToString :: SortDirection -> String
sortDirectionToString sd = case sd of
  SortAsc -> "asc"
  SortDesc -> "desc"

-- | Toggle sort direction.
toggleSort :: SortDirection -> SortDirection
toggleSort SortAsc = SortDesc
toggleSort SortDesc = SortAsc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // cell values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cell value variants.
-- |
-- | Each variant corresponds to a column type and contains
-- | the appropriate data for rendering.
data CellValue
  = TextCell String
  | NumberCell Number
  | CurrencyCell Number String   -- ^ Value and currency code
  | PercentCell Number
  | DateCell String              -- ^ ISO date string
  | BoolCell Boolean
  | BadgeCell String String      -- ^ Text and variant (success, warning, error, etc.)
  | SparklineCell (Array Number)
  | ProgressCell Percentage
  | EmptyCell

derive instance eqCellValue :: Eq CellValue

instance showCellValue :: Show CellValue where
  show (TextCell s) = s
  show (NumberCell n) = show n
  show (CurrencyCell n code) = code <> " " <> show n
  show (PercentCell n) = show n <> "%"
  show (DateCell s) = s
  show (BoolCell b) = if b then "Yes" else "No"
  show (BadgeCell text _) = text
  show (SparklineCell _) = "[sparkline]"
  show (ProgressCell p) = show (unwrapPercentage p) <> "%"
  show EmptyCell = ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // data structures
-- ═════════════════════════════════════════════════════════════════════════════

-- | Column definition.
type ColumnDef =
  { key :: String
  , label :: String
  , colType :: ColumnType
  , width :: Maybe Int      -- ^ Width in pixels
  , align :: Maybe String   -- ^ "left", "center", "right"
  , sortable :: Boolean
  , format :: Maybe String  -- ^ Custom format string
  }

-- | Pagination state.
type Pagination =
  { page :: Int
  , pageSize :: Int
  , total :: Int
  , totalPages :: Int
  }

-- | Complete table data payload.
type TableData =
  { columns :: Array ColumnDef
  , rows :: Array (Array CellValue)
  , pagination :: Maybe Pagination
  , sortBy :: Maybe String       -- ^ Column key currently sorting by
  , sortDir :: Maybe SortDirection
  , selectable :: Boolean
  , searchable :: Boolean
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // default values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default column definition.
defaultColumn :: ColumnDef
defaultColumn =
  { key: ""
  , label: ""
  , colType: ColText
  , width: Nothing
  , align: Nothing
  , sortable: false
  , format: Nothing
  }
