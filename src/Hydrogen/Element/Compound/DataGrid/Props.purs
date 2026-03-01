-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // data-grid // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Prop Builders — Functions to construct grid configuration.
-- |
-- | This module provides all the prop builder functions used to configure
-- | the DataGrid component. Each function takes a value and returns a
-- | GridProp modifier that updates the GridProps record.
-- |
-- | ## Categories
-- |
-- | - **Data Props**: columns, rows, rowKey
-- | - **Selection Props**: selectionMode, selectedRowKeys
-- | - **Expansion Props**: expandable, expandedRowKeys, expandedContent
-- | - **Pagination Props**: pagination, builtInPagination, externalPagination
-- | - **Filtering Props**: globalFilter, columnFilters
-- | - **Sorting Props**: sortColumns
-- | - **Loading Props**: loading, emptyState, loadingState
-- | - **Keyboard Props**: enableKeyboardNav
-- | - **Color Atoms**: headerBgColor, rowBgColor, borderColor, etc.
-- | - **Geometry Atoms**: containerBorderRadius, badgeBorderRadius
-- | - **Dimension Atoms**: cellPaddingX, cellPaddingY, headerHeight, etc.
-- | - **Typography Atoms**: fontSize, headerFontSize
-- | - **Event Handlers**: onRowSelect, onSort, onFilter, etc.

module Hydrogen.Element.Compound.DataGrid.Props
  ( -- * Data Props
    columns
  , rows
  , rowKey
  
    -- * Selection Props
  , selectionMode
  , selectedRowKeys
  
    -- * Expansion Props
  , expandable
  , expandedRowKeys
  , expandedContent
  
    -- * Pagination Props
  , pagination
  , builtInPagination
  , externalPagination
  
    -- * Filtering Props
  , globalFilter
  , columnFilters
  
    -- * Sorting Props
  , sortColumns
  
    -- * Loading Props
  , loading
  , emptyState
  , loadingState
  
    -- * Keyboard Props
  , enableKeyboardNav
  
    -- * Color Atoms
  , headerBgColor
  , headerTextColor
  , rowBgColor
  , rowAltBgColor
  , rowHoverBgColor
  , rowSelectedBgColor
  , cellTextColor
  , borderColor
  , linkColor
  , badgeBgColor
  , badgeTextColor
  , loadingSpinnerColor
  
    -- * Geometry Atoms
  , containerBorderRadius
  , badgeBorderRadius
  
    -- * Dimension Atoms
  , cellPaddingX
  , cellPaddingY
  , headerHeight
  , gridRowHeight
  , containerMaxHeight
  , borderWidth
  
    -- * Typography Atoms
  , fontSize
  , headerFontSize
  
    -- * Event Handlers
  , onRowSelect
  , onRowExpand
  , onCellEdit
  , onSort
  , onFilter
  , onColumnResize
  , onColumnReorder
  , onPageChange
  , onGlobalSearch
  ) where

import Data.Maybe (Maybe(Just))
import Foreign.Object (Object)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.DataGrid.Types
  ( ColumnDef
  , FilterValue
  , GridProp
  , PaginationConfig(BuiltIn, External)
  , RowContext
  , SelectionMode
  , SortConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // data props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the column definitions for the grid.
columns :: forall msg. Array (ColumnDef msg) -> GridProp msg
columns cols props = props { columns = cols }

-- | Set the row data for the grid.
rows :: forall msg. Array (Object String) -> GridProp msg
rows data' props = props { rows = data' }

-- | Set the key used to identify each row uniquely.
rowKey :: forall msg. String -> GridProp msg
rowKey key props = props { rowKey = key }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selection props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the selection mode (NoSelection, SingleSelect, MultiSelect, CheckboxSelect).
selectionMode :: forall msg. SelectionMode -> GridProp msg
selectionMode mode props = props { selectionMode = mode }

-- | Set the currently selected row keys.
selectedRowKeys :: forall msg. Array String -> GridProp msg
selectedRowKeys keys props = props { selectedRowKeys = keys }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // expansion props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable or disable row expansion.
expandable :: forall msg. Boolean -> GridProp msg
expandable e props = props { expandable = e }

-- | Set the currently expanded row keys.
expandedRowKeys :: forall msg. Array String -> GridProp msg
expandedRowKeys keys props = props { expandedRowKeys = keys }

-- | Set the renderer for expanded row content.
expandedContent :: forall msg. (RowContext -> E.Element msg) -> GridProp msg
expandedContent renderer props = props { expandedContent = Just renderer }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // pagination props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the pagination configuration.
pagination :: forall msg. PaginationConfig -> GridProp msg
pagination config props = props { pagination = config }

-- | Configure built-in pagination with the given page size.
builtInPagination :: forall msg. Int -> GridProp msg
builtInPagination pageSize props = props { pagination = BuiltIn { pageSize } }

-- | Configure external pagination with page size, current page, and total rows.
externalPagination :: forall msg. Int -> Int -> Int -> GridProp msg
externalPagination pageSize currentPage totalRows props =
  props { pagination = External { pageSize, currentPage, totalRows } }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // filtering props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the global search filter string.
globalFilter :: forall msg. String -> GridProp msg
globalFilter search props = props { globalFilter = search }

-- | Set the per-column filter values.
columnFilters :: forall msg. Object FilterValue -> GridProp msg
columnFilters filters props = props { columnFilters = filters }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sorting props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the current sort configuration.
sortColumns :: forall msg. Array SortConfig -> GridProp msg
sortColumns sorts props = props { sortColumns = sorts }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // loading props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the loading state.
loading :: forall msg. Boolean -> GridProp msg
loading l props = props { loading = l }

-- | Set custom empty state content.
emptyState :: forall msg. E.Element msg -> GridProp msg
emptyState content props = props { emptyState = Just content }

-- | Set custom loading state content.
loadingState :: forall msg. E.Element msg -> GridProp msg
loadingState content props = props { loadingState = Just content }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // keyboard props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable or disable keyboard navigation.
enableKeyboardNav :: forall msg. Boolean -> GridProp msg
enableKeyboardNav enabled props = props { enableKeyboardNav = enabled }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the header background color.
headerBgColor :: forall msg. Color.RGB -> GridProp msg
headerBgColor c props = props { headerBgColor = Just c }

-- | Set the header text color.
headerTextColor :: forall msg. Color.RGB -> GridProp msg
headerTextColor c props = props { headerTextColor = Just c }

-- | Set the row background color.
rowBgColor :: forall msg. Color.RGB -> GridProp msg
rowBgColor c props = props { rowBgColor = Just c }

-- | Set the alternating row background color.
rowAltBgColor :: forall msg. Color.RGB -> GridProp msg
rowAltBgColor c props = props { rowAltBgColor = Just c }

-- | Set the row hover background color.
rowHoverBgColor :: forall msg. Color.RGB -> GridProp msg
rowHoverBgColor c props = props { rowHoverBgColor = Just c }

-- | Set the selected row background color.
rowSelectedBgColor :: forall msg. Color.RGB -> GridProp msg
rowSelectedBgColor c props = props { rowSelectedBgColor = Just c }

-- | Set the cell text color.
cellTextColor :: forall msg. Color.RGB -> GridProp msg
cellTextColor c props = props { cellTextColor = Just c }

-- | Set the border color.
borderColor :: forall msg. Color.RGB -> GridProp msg
borderColor c props = props { borderColor = Just c }

-- | Set the link text color.
linkColor :: forall msg. Color.RGB -> GridProp msg
linkColor c props = props { linkColor = Just c }

-- | Set the badge background color.
badgeBgColor :: forall msg. Color.RGB -> GridProp msg
badgeBgColor c props = props { badgeBgColor = Just c }

-- | Set the badge text color.
badgeTextColor :: forall msg. Color.RGB -> GridProp msg
badgeTextColor c props = props { badgeTextColor = Just c }

-- | Set the loading spinner color.
loadingSpinnerColor :: forall msg. Color.RGB -> GridProp msg
loadingSpinnerColor c props = props { loadingSpinnerColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // geometry atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the container border radius.
containerBorderRadius :: forall msg. Geometry.Corners -> GridProp msg
containerBorderRadius r props = props { containerBorderRadius = Just r }

-- | Set the badge border radius.
badgeBorderRadius :: forall msg. Geometry.Corners -> GridProp msg
badgeBorderRadius r props = props { badgeBorderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dimension atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the horizontal cell padding.
cellPaddingX :: forall msg. Device.Pixel -> GridProp msg
cellPaddingX p props = props { cellPaddingX = Just p }

-- | Set the vertical cell padding.
cellPaddingY :: forall msg. Device.Pixel -> GridProp msg
cellPaddingY p props = props { cellPaddingY = Just p }

-- | Set the header height.
headerHeight :: forall msg. Device.Pixel -> GridProp msg
headerHeight h props = props { headerHeight = Just h }

-- | Set the row height.
gridRowHeight :: forall msg. Device.Pixel -> GridProp msg
gridRowHeight h props = props { rowHeight = Just h }

-- | Set the container max height.
containerMaxHeight :: forall msg. Device.Pixel -> GridProp msg
containerMaxHeight h props = props { containerMaxHeight = Just h }

-- | Set the border width.
borderWidth :: forall msg. Device.Pixel -> GridProp msg
borderWidth w props = props { borderWidth = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // typography atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the base font size.
fontSize :: forall msg. FontSize.FontSize -> GridProp msg
fontSize s props = props { fontSize = Just s }

-- | Set the header font size.
headerFontSize :: forall msg. FontSize.FontSize -> GridProp msg
headerFontSize s props = props { headerFontSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // event handlers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handler for row selection changes.
onRowSelect :: forall msg. (Array String -> msg) -> GridProp msg
onRowSelect handler props = props { onRowSelect = Just handler }

-- | Handler for row expansion changes.
onRowExpand :: forall msg. (Array String -> msg) -> GridProp msg
onRowExpand handler props = props { onRowExpand = Just handler }

-- | Handler for cell edit events.
onCellEdit :: forall msg. ({ rowIndex :: Int, columnKey :: String, value :: String } -> msg) -> GridProp msg
onCellEdit handler props = props { onCellEdit = Just handler }

-- | Handler for sort changes.
onSort :: forall msg. (Array SortConfig -> msg) -> GridProp msg
onSort handler props = props { onSort = Just handler }

-- | Handler for filter changes.
onFilter :: forall msg. (Object FilterValue -> msg) -> GridProp msg
onFilter handler props = props { onFilter = Just handler }

-- | Handler for column resize events.
onColumnResize :: forall msg. ({ columnKey :: String, width :: Int } -> msg) -> GridProp msg
onColumnResize handler props = props { onColumnResize = Just handler }

-- | Handler for column reorder events.
onColumnReorder :: forall msg. (Array String -> msg) -> GridProp msg
onColumnReorder handler props = props { onColumnReorder = Just handler }

-- | Handler for page change events.
onPageChange :: forall msg. (Int -> msg) -> GridProp msg
onPageChange handler props = props { onPageChange = Just handler }

-- | Handler for global search changes.
onGlobalSearch :: forall msg. (String -> msg) -> GridProp msg
onGlobalSearch handler props = props { onGlobalSearch = Just handler }
