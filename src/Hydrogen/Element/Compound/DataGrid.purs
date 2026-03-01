-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // component // data-grid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid — Schema-native full-featured data grid component.
-- |
-- | A powerful, accessible data grid with sorting, filtering, pagination,
-- | row selection, row expansion, and more. All visual styling is controlled
-- | by Schema atoms from the 12 pillars — no hardcoded CSS values.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from Color, Geometry,
-- | Dimension, and Typography pillars. When an atom is `Nothing`, no style
-- | is emitted — the element inherits from its parent or browser defaults.
-- |
-- | ## Features
-- |
-- | - Column definitions with sorting, filtering, resizing
-- | - Fixed columns (left/right sticky)
-- | - Multi-column sorting (shift+click)
-- | - Per-column and global filtering
-- | - Row selection (single, multiple, checkbox)
-- | - Row expansion with detail views
-- | - Built-in and external pagination
-- | - Custom cell renderers
-- | - Keyboard navigation
-- | - ARIA grid pattern for accessibility
-- | - Export to CSV
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property              | Pillar     | Type                 |
-- | |-----------------------|------------|----------------------|
-- | | headerBgColor         | Color      | Color.RGB            |
-- | | headerTextColor       | Color      | Color.RGB            |
-- | | rowBgColor            | Color      | Color.RGB            |
-- | | rowAltBgColor         | Color      | Color.RGB            |
-- | | rowHoverBgColor       | Color      | Color.RGB            |
-- | | rowSelectedBgColor    | Color      | Color.RGB            |
-- | | cellTextColor         | Color      | Color.RGB            |
-- | | borderColor           | Color      | Color.RGB            |
-- | | containerBorderRadius | Geometry   | Geometry.Corners     |
-- | | cellPaddingX          | Dimension  | Device.Pixel         |
-- | | cellPaddingY          | Dimension  | Device.Pixel         |
-- | | fontSize              | Typography | FontSize.FontSize    |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.DataGrid as Grid
-- | import Hydrogen.Element.Compound.DataGrid.Column as Col
-- | import Hydrogen.Element.Compound.DataGrid.Types (CellType(..))
-- |
-- | -- Define columns
-- | columns =
-- |   [ Col.column "id" "ID" [ Col.colWidth 80, Col.sortable ]
-- |   , Col.column "name" "Name" [ Col.sortable, Col.filterable ]
-- |   , Col.column "status" "Status" [ Col.cellType CellBadge ]
-- |   , Col.column "actions" "" [ Col.cellType CellActions, Col.colWidth 100 ]
-- |   ]
-- |
-- | -- Render grid with brand atoms
-- | Grid.dataGrid
-- |   [ Grid.columns columns
-- |   , Grid.rows myData
-- |   , Grid.headerBgColor brand.muted
-- |   , Grid.headerTextColor brand.foreground
-- |   , Grid.borderColor brand.border
-- |   , Grid.onRowSelect HandleSelect
-- |   , Grid.pagination (Grid.BuiltIn { pageSize: 25 })
-- |   ]
-- | ```
-- |
-- | ## Module Structure
-- |
-- | The DataGrid is split across multiple submodules:
-- |
-- | - `DataGrid` (this module) — Main component and re-exports
-- | - `DataGrid.Types` — Type definitions
-- | - `DataGrid.Column` — Column definition builders
-- | - `DataGrid.Props` — Grid prop builders
-- | - `DataGrid.Render` — Internal rendering functions
-- | - `DataGrid.Cell` — Cell rendering
-- | - `DataGrid.Processing` — Data processing (sort, filter, paginate)

module Hydrogen.Element.Compound.DataGrid
  ( -- * Grid Component
    dataGrid
  
    -- * Re-exports from Types
  , module Hydrogen.Element.Compound.DataGrid.Types
  
    -- * Re-exports from Column
  , module Hydrogen.Element.Compound.DataGrid.Column
  
    -- * Re-exports from Props
  , module Hydrogen.Element.Compound.DataGrid.Props
  
    -- * Export Functions
  , exportCsv
  ) where

import Prelude
  ( ($)
  , show
  , not
  , (<>)
  )

import Data.Array (foldl, filter, length)
import Data.Maybe (maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.DataGrid.Types
  ( CellContext
  , CellType(CellText, CellNumber, CellDate, CellBoolean, CellLink, CellBadge, CellActions, CellCustom)
  , ColumnDef
  , ColumnProp
  , FilterValue(TextFilter, NumberFilter, BooleanFilter, SelectFilter, DateRangeFilter)
  , FixedPosition(FixedLeft, FixedRight, NotFixed)
  , GridProp
  , GridProps
  , GridState
  , PaginationConfig(NoPagination, BuiltIn, External)
  , RowContext
  , SelectionMode(NoSelection, SingleSelect, MultiSelect, CheckboxSelect)
  , SortConfig
  , SortDirection(Ascending, Descending)
  , VirtualScrollConfig
  , defaultColumnDef
  , defaultGridProps
  )
import Hydrogen.Element.Compound.DataGrid.Column
  ( cellRenderer
  , cellType
  , colMaxWidth
  , colMinWidth
  , colWidth
  , column
  , editable
  , filterable
  , fixedLeft
  , fixedRight
  , headerRenderer
  , hidden
  , notResizable
  , resizable
  , sortable
  )
import Hydrogen.Element.Compound.DataGrid.Props
  ( badgeBgColor
  , badgeBorderRadius
  , badgeTextColor
  , borderColor
  , borderWidth
  , builtInPagination
  , cellPaddingX
  , cellPaddingY
  , cellTextColor
  , columnFilters
  , columns
  , containerBorderRadius
  , containerMaxHeight
  , emptyState
  , enableKeyboardNav
  , expandable
  , expandedContent
  , expandedRowKeys
  , externalPagination
  , fontSize
  , globalFilter
  , gridRowHeight
  , headerBgColor
  , headerFontSize
  , headerHeight
  , headerTextColor
  , linkColor
  , loading
  , loadingSpinnerColor
  , loadingState
  , onCellEdit
  , onColumnReorder
  , onColumnResize
  , onFilter
  , onGlobalSearch
  , onPageChange
  , onRowExpand
  , onRowSelect
  , onSort
  , pagination
  , rowAltBgColor
  , rowBgColor
  , rowHoverBgColor
  , rowKey
  , rowSelectedBgColor
  , rows
  , selectedRowKeys
  , selectionMode
  , sortColumns
  )
import Hydrogen.Element.Compound.DataGrid.Render
  ( renderBody
  , renderGlobalSearch
  , renderHeader
  , renderLoadingOverlay
  )
import Hydrogen.Element.Compound.DataGrid.Pagination (renderPagination)
import Hydrogen.Element.Compound.DataGrid.Processing as Processing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // grid component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the data grid.
-- |
-- | Takes an array of property modifiers and produces an Element.
-- | All visual styling comes from Schema atoms — no hardcoded CSS.
dataGrid :: forall msg. Array (GridProp msg) -> E.Element msg
dataGrid propMods =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    visibleColumns = filter (\col -> not col.hidden) props.columns
    processedRows = Processing.processRows props
  in
    E.div_
      ( [ E.role "grid"
        , E.attr "aria-rowcount" (show $ length props.rows)
        , E.attr "aria-colcount" (show $ length visibleColumns)
        , E.style "position" "relative"
        , E.style "width" "100%"
        , E.style "overflow" "hidden"
        ]
        <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        <> maybe [] (\w -> [E.style "border-width" (show w)]) props.borderWidth
        <> maybe [] (\_ -> [E.style "border-style" "solid"]) props.borderWidth
        <> maybe [] (\r -> [E.style "border-radius" (Geometry.cornersToLegacyCss r)]) props.containerBorderRadius
      )
      [ -- Global search (if any filterable columns)
        renderGlobalSearch props visibleColumns
      , -- Scrollable container
        E.div_
          ( [ E.style "overflow" "auto"
            , E.attr "data-grid-scroll" "true"
            ]
            <> maybe [] (\h -> [E.style "max-height" (show h)]) props.containerMaxHeight
          )
          [ -- Table
            E.table_
              ( [ E.style "width" "100%"
                , E.style "border-collapse" "collapse"
                , E.style "caption-side" "bottom"
                ]
                <> maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.fontSize
              )
              [ renderHeader props visibleColumns
              , renderBody props visibleColumns processedRows
              ]
          ]
      , -- Loading overlay
        renderLoadingOverlay props
      , -- Pagination
        renderPagination props (length processedRows)
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // export
-- ═════════════════════════════════════════════════════════════════════════════

-- | Export grid data to CSV string.
exportCsv :: forall msg. GridProps msg -> String
exportCsv props = Processing.toCsvString props.columns props.rows
