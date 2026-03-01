-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // widget // table
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Widget — Tabular data display with sorting and pagination.
-- |
-- | ## Design Philosophy
-- |
-- | A Table widget displays data in rows and columns with:
-- | - Column definitions (type, label, alignment, width)
-- | - Row data as arrays of cell values
-- | - Pagination state and controls
-- | - Optional sorting by column
-- | - Optional row selection
-- | - Optional search filtering
-- |
-- | The widget accepts complete `TableData` — all data, column defs, and
-- | pagination state are provided upfront. Pure data in, Element out.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Widget.Table as Table
-- |
-- | Table.tableWidget []
-- |   { columns:
-- |       [ { key: "name", label: "Name", colType: Table.ColText, ... }
-- |       , { key: "amount", label: "Amount", colType: Table.ColCurrency, ... }
-- |       ]
-- |   , rows:
-- |       [ [ Table.TextCell "John Doe", Table.NumberCell 1234.56 ]
-- |       , [ Table.TextCell "Jane Smith", Table.NumberCell 5678.90 ]
-- |       ]
-- |   , pagination: Just { page: 1, pageSize: 10, total: 100, totalPages: 10 }
-- |   , ...
-- |   }
-- | ```
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - `Table.Types` — Core data types (ColumnType, CellValue, Pagination, etc.)
-- | - `Table.Props` — Property types and builders
-- | - `Table.Pagination` — Pagination helper functions
-- | - `Table.Render` — Rendering functions
-- | - `Table.Helpers` — Utility functions

module Hydrogen.Element.Compound.Widget.Table
  ( module Types
  , module Props
  , module Pagination
  , module Render
  , module Helpers
  ) where

import Hydrogen.Element.Compound.Widget.Table.Types as Types
import Hydrogen.Element.Compound.Widget.Table.Props as Props
import Hydrogen.Element.Compound.Widget.Table.Pagination as Pagination
import Hydrogen.Element.Compound.Widget.Table.Render as Render
import Hydrogen.Element.Compound.Widget.Table.Helpers as Helpers
