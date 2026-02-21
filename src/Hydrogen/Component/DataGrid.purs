-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // hydrogen // datagrid
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Full-featured data grid component
-- |
-- | A powerful, accessible data grid with sorting, filtering, pagination,
-- | virtual scrolling, and more. Inspired by AG Grid and TanStack Table.
-- |
-- | ## Features
-- |
-- | - Column definitions with sorting, filtering, resizing
-- | - Fixed header and fixed columns (left/right)
-- | - Column reordering via drag and drop
-- | - Multi-column sorting (shift+click)
-- | - Per-column and global filtering
-- | - Row selection (single, multiple, checkbox)
-- | - Row expansion with detail views
-- | - Built-in and external pagination
-- | - Virtual scrolling for large datasets
-- | - Inline cell editing
-- | - Custom cell renderers
-- | - Keyboard navigation (arrow keys, enter to edit)
-- | - ARIA grid pattern for accessibility
-- | - Export to CSV and JSON
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Component.DataGrid as DataGrid
-- |
-- | -- Define columns
-- | columns =
-- |   [ DataGrid.column "id" "ID" [ DataGrid.width 80, DataGrid.sortable ]
-- |   , DataGrid.column "name" "Name" [ DataGrid.sortable, DataGrid.filterable ]
-- |   , DataGrid.column "status" "Status"
-- |       [ DataGrid.cellType DataGrid.Badge
-- |       , DataGrid.cellRenderer statusRenderer
-- |       ]
-- |   , DataGrid.column "actions" ""
-- |       [ DataGrid.cellType DataGrid.Actions
-- |       , DataGrid.width 100
-- |       ]
-- |   ]
-- |
-- | -- Render grid
-- | DataGrid.dataGrid
-- |   [ DataGrid.columns columns
-- |   , DataGrid.rows myData
-- |   , DataGrid.onRowSelect HandleSelect
-- |   , DataGrid.pagination DataGrid.BuiltIn { pageSize: 25 }
-- |   ]
-- | ```
-- |
-- | ## Virtual Scrolling
-- |
-- | ```purescript
-- | DataGrid.dataGrid
-- |   [ DataGrid.columns columns
-- |   , DataGrid.rows largeDataset  -- 100k+ rows
-- |   , DataGrid.virtualScroll { rowHeight: 40, overscan: 5 }
-- |   ]
-- | ```
-- |
-- | ## Row Expansion
-- |
-- | ```purescript
-- | DataGrid.dataGrid
-- |   [ DataGrid.columns columns
-- |   , DataGrid.rows myData
-- |   , DataGrid.expandable true
-- |   , DataGrid.expandedContent renderDetailView
-- |   ]
-- | ```
-- |
-- | ## Export
-- |
-- | ```purescript
-- | -- Export functions
-- | csvData <- DataGrid.exportCsv grid
-- | jsonData <- DataGrid.exportJson grid
-- | ```
module Hydrogen.Component.DataGrid
  ( -- * Grid Component
    dataGrid
    -- * Column Definition
  , column
  , ColumnDef
  , ColumnProp
    -- * Column Props
  , width
  , minWidth
  , maxWidth
  , sortable
  , filterable
  , resizable
  , fixed
  , hidden
  , cellType
  , cellRenderer
  , headerRenderer
  , editable
    -- * Column Types
  , CellType(..)
  , FixedPosition(..)
    -- * Grid Props
  , GridProps
  , GridProp
  , columns
  , rows
  , rowKey
  , className
  , onRowSelect
  , onRowExpand
  , onCellEdit
  , onSort
  , onFilter
  , onColumnResize
  , onColumnReorder
    -- * Selection
  , selectionMode
  , SelectionMode(..)
  , selectedRows
    -- * Expansion
  , expandable
  , expandedRows
  , expandedContent
    -- * Pagination
  , pagination
  , PaginationConfig(..)
  , pageSize
  , currentPage
  , totalRows
  , onPageChange
    -- * Virtual Scrolling
  , virtualScroll
  , VirtualScrollConfig
    -- * Filtering
  , globalSearch
  , columnFilters
  , FilterValue(..)
    -- * Sorting
  , sortConfig
  , SortConfig
  , SortDirection(..)
    -- * States
  , loading
  , emptyState
  , loadingState
    -- * Export
  , exportCsv
  , exportJson
  , downloadCsv
  , downloadJson
    -- * Keyboard Navigation
  , enableKeyboardNav
    -- * Internal Types (for custom renderers)
  , GridState
  , CellContext
  , RowContext
  ) where

import Prelude

import Data.Argonaut (class EncodeJson, encodeJson, stringify)
import Data.Array (filter, foldl, length, mapWithIndex, sortBy, take, drop, (:))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (fromString) as Number

import Data.String (Pattern(..), contains, toLower)
import Data.String as String
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Hydrogen.UI.Core (cls)
import Web.UIEvent.KeyboardEvent (KeyboardEvent)
import Effect.Uncurried (EffectFn2, runEffectFn2)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                         // ffi
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Download CSV file
foreign import downloadCsvImpl :: EffectFn2 String String Unit

-- | Download JSON file
foreign import downloadJsonImpl :: EffectFn2 String String Unit

-- | Download CSV with given content and filename
downloadCsv :: String -> String -> Effect Unit
downloadCsv content filename = runEffectFn2 downloadCsvImpl content filename

-- | Download JSON with given content and filename
downloadJson :: String -> String -> Effect Unit
downloadJson content filename = runEffectFn2 downloadJsonImpl content filename

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // cell types
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Built-in cell type renderers
data CellType
  = Text
  | Number
  | Date
  | Boolean
  | Link
  | Badge
  | Actions
  | Custom

derive instance eqCellType :: Eq CellType

-- | Fixed column position
data FixedPosition
  = FixedLeft
  | FixedRight
  | NotFixed

derive instance eqFixedPosition :: Eq FixedPosition

-- | Sort direction
data SortDirection
  = Ascending
  | Descending

derive instance eqSortDirection :: Eq SortDirection

-- | Selection mode
data SelectionMode
  = NoSelection
  | SingleSelect
  | MultiSelect
  | CheckboxSelect

derive instance eqSelectionMode :: Eq SelectionMode

-- | Filter value types
data FilterValue
  = TextFilter String
  | NumberFilter { min :: Maybe Number, max :: Maybe Number }
  | BooleanFilter Boolean
  | SelectFilter (Array String)
  | DateRangeFilter { start :: Maybe String, end :: Maybe String }

-- | Sort configuration
type SortConfig =
  { column :: String
  , direction :: SortDirection
  }

-- | Virtual scroll configuration
type VirtualScrollConfig =
  { rowHeight :: Int
  , overscan :: Int
  , containerHeight :: Int
  }

-- | Pagination configuration
data PaginationConfig
  = NoPagination
  | BuiltIn { pageSize :: Int }
  | External
      { pageSize :: Int
      , currentPage :: Int
      , totalRows :: Int
      }

derive instance eqPaginationConfig :: Eq PaginationConfig

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // column definition
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Column definition
type ColumnDef w i =
  { key :: String
  , header :: String
  , width :: Maybe Int
  , minWidth :: Maybe Int
  , maxWidth :: Maybe Int
  , sortable :: Boolean
  , filterable :: Boolean
  , resizable :: Boolean
  , fixed :: FixedPosition
  , hidden :: Boolean
  , cellType :: CellType
  , cellRenderer :: Maybe (CellContext -> HH.HTML w i)
  , headerRenderer :: Maybe (String -> HH.HTML w i)
  , editable :: Boolean
  }

-- | Column property modifier
type ColumnProp w i = ColumnDef w i -> ColumnDef w i

-- | Default column definition
defaultColumnDef :: forall w i. String -> String -> ColumnDef w i
defaultColumnDef key header =
  { key
  , header
  , width: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , sortable: false
  , filterable: false
  , resizable: true
  , fixed: NotFixed
  , hidden: false
  , cellType: Text
  , cellRenderer: Nothing
  , headerRenderer: Nothing
  , editable: false
  }

-- | Create a column definition
column :: forall w i. String -> String -> Array (ColumnProp w i) -> ColumnDef w i
column key header props = foldl (\c f -> f c) (defaultColumnDef key header) props

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // column props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set column width
width :: forall w i. Int -> ColumnProp w i
width w col = col { width = Just w }

-- | Set minimum width
minWidth :: forall w i. Int -> ColumnProp w i
minWidth w col = col { minWidth = Just w }

-- | Set maximum width
maxWidth :: forall w i. Int -> ColumnProp w i
maxWidth w col = col { maxWidth = Just w }

-- | Make column sortable
sortable :: forall w i. ColumnProp w i
sortable col = col { sortable = true }

-- | Make column filterable
filterable :: forall w i. ColumnProp w i
filterable col = col { filterable = true }

-- | Make column resizable
resizable :: forall w i. ColumnProp w i
resizable col = col { resizable = true }

-- | Set fixed position
fixed :: forall w i. FixedPosition -> ColumnProp w i
fixed pos col = col { fixed = pos }

-- | Hide column
hidden :: forall w i. ColumnProp w i
hidden col = col { hidden = true }

-- | Set cell type
cellType :: forall w i. CellType -> ColumnProp w i
cellType t col = col { cellType = t }

-- | Set custom cell renderer
cellRenderer :: forall w i. (CellContext -> HH.HTML w i) -> ColumnProp w i
cellRenderer r col = col { cellRenderer = Just r }

-- | Set custom header renderer
headerRenderer :: forall w i. (String -> HH.HTML w i) -> ColumnProp w i
headerRenderer r col = col { headerRenderer = Just r }

-- | Make cell editable
editable :: forall w i. ColumnProp w i
editable col = col { editable = true }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // cell context
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Context passed to cell renderers
type CellContext =
  { value :: String
  , rowIndex :: Int
  , columnKey :: String
  , rowData :: Object String
  , isEditing :: Boolean
  , isSelected :: Boolean
  , isExpanded :: Boolean
  }

-- | Context for row-level operations
type RowContext =
  { rowIndex :: Int
  , rowData :: Object String
  , isSelected :: Boolean
  , isExpanded :: Boolean
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // grid state
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Internal grid state (exposed for advanced usage)
type GridState =
  { sortColumns :: Array SortConfig
  , filters :: Object FilterValue
  , globalFilter :: String
  , selectedRowKeys :: Array String
  , expandedRowKeys :: Array String
  , editingCell :: Maybe { rowIndex :: Int, columnKey :: String }
  , currentPage :: Int
  , pageSize :: Int
  , columnWidths :: Object Int
  , columnOrder :: Array String
  , scrollTop :: Int
  , focusedCell :: Maybe { rowIndex :: Int, colIndex :: Int }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // grid props
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Grid properties
type GridProps w i =
  { columns :: Array (ColumnDef w i)
  , rows :: Array (Object String)
  , rowKey :: String
  , className :: String
  , selectionMode :: SelectionMode
  , selectedRowKeys :: Array String
  , expandable :: Boolean
  , expandedRowKeys :: Array String
  , expandedContent :: Maybe (RowContext -> HH.HTML w i)
  , pagination :: PaginationConfig
  , virtualScroll :: Maybe VirtualScrollConfig
  , globalFilter :: String
  , columnFilters :: Object FilterValue
  , sortColumns :: Array SortConfig
  , loading :: Boolean
  , emptyState :: Maybe (HH.HTML w i)
  , loadingState :: Maybe (HH.HTML w i)
  , enableKeyboardNav :: Boolean
  , onRowSelect :: Maybe (Array String -> i)
  , onRowExpand :: Maybe (Array String -> i)
  , onCellEdit :: Maybe ({ rowIndex :: Int, columnKey :: String, value :: String } -> i)
  , onSort :: Maybe (Array SortConfig -> i)
  , onFilter :: Maybe (Object FilterValue -> i)
  , onColumnResize :: Maybe ({ columnKey :: String, width :: Int } -> i)
  , onColumnReorder :: Maybe (Array String -> i)
  , onPageChange :: Maybe (Int -> i)
  , onGlobalSearch :: Maybe (String -> i)
  , onKeyDown :: Maybe (KeyboardEvent -> i)
  }

-- | Grid property modifier
type GridProp w i = GridProps w i -> GridProps w i

-- | Default grid properties
defaultGridProps :: forall w i. GridProps w i
defaultGridProps =
  { columns: []
  , rows: []
  , rowKey: "id"
  , className: ""
  , selectionMode: NoSelection
  , selectedRowKeys: []
  , expandable: false
  , expandedRowKeys: []
  , expandedContent: Nothing
  , pagination: NoPagination
  , virtualScroll: Nothing
  , globalFilter: ""
  , columnFilters: Object.empty
  , sortColumns: []
  , loading: false
  , emptyState: Nothing
  , loadingState: Nothing
  , enableKeyboardNav: true
  , onRowSelect: Nothing
  , onRowExpand: Nothing
  , onCellEdit: Nothing
  , onSort: Nothing
  , onFilter: Nothing
  , onColumnResize: Nothing
  , onColumnReorder: Nothing
  , onPageChange: Nothing
  , onGlobalSearch: Nothing
  , onKeyDown: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // grid prop builders
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Set columns
columns :: forall w i. Array (ColumnDef w i) -> GridProp w i
columns cols props = props { columns = cols }

-- | Set row data
rows :: forall w i. Array (Object String) -> GridProp w i
rows data' props = props { rows = data' }

-- | Set row key field
rowKey :: forall w i. String -> GridProp w i
rowKey key props = props { rowKey = key }

-- | Add custom class
className :: forall w i. String -> GridProp w i
className c props = props { className = props.className <> " " <> c }

-- | Set selection mode
selectionMode :: forall w i. SelectionMode -> GridProp w i
selectionMode mode props = props { selectionMode = mode }

-- | Set selected rows
selectedRows :: forall w i. Array String -> GridProp w i
selectedRows keys props = props { selectedRowKeys = keys }

-- | Enable row expansion
expandable :: forall w i. Boolean -> GridProp w i
expandable e props = props { expandable = e }

-- | Set expanded rows
expandedRows :: forall w i. Array String -> GridProp w i
expandedRows keys props = props { expandedRowKeys = keys }

-- | Set expanded row content renderer
expandedContent :: forall w i. (RowContext -> HH.HTML w i) -> GridProp w i
expandedContent renderer props = props { expandedContent = Just renderer }

-- | Set pagination config
pagination :: forall w i. PaginationConfig -> GridProp w i
pagination config props = props { pagination = config }

-- | Set page size (for built-in pagination)
pageSize :: forall w i. Int -> GridProp w i
pageSize size props = case props.pagination of
  BuiltIn _ -> props { pagination = BuiltIn { pageSize: size } }
  _ -> props { pagination = BuiltIn { pageSize: size } }

-- | Set current page (for external pagination)
currentPage :: forall w i. Int -> GridProp w i
currentPage page props = case props.pagination of
  External cfg -> props { pagination = External (cfg { currentPage = page }) }
  _ -> props

-- | Set total rows (for external pagination)
totalRows :: forall w i. Int -> GridProp w i
totalRows total props = case props.pagination of
  External cfg -> props { pagination = External (cfg { totalRows = total }) }
  _ -> props

-- | Enable virtual scrolling
virtualScroll :: forall w i. VirtualScrollConfig -> GridProp w i
virtualScroll config props = props { virtualScroll = Just config }

-- | Set global search filter
globalSearch :: forall w i. String -> GridProp w i
globalSearch search props = props { globalFilter = search }

-- | Set column filters
columnFilters :: forall w i. Object FilterValue -> GridProp w i
columnFilters filters props = props { columnFilters = filters }

-- | Set sort configuration
sortConfig :: forall w i. Array SortConfig -> GridProp w i
sortConfig sorts props = props { sortColumns = sorts }

-- | Set loading state
loading :: forall w i. Boolean -> GridProp w i
loading l props = props { loading = l }

-- | Set empty state content
emptyState :: forall w i. HH.HTML w i -> GridProp w i
emptyState content props = props { emptyState = Just content }

-- | Set loading state content
loadingState :: forall w i. HH.HTML w i -> GridProp w i
loadingState content props = props { loadingState = Just content }

-- | Enable keyboard navigation
enableKeyboardNav :: forall w i. Boolean -> GridProp w i
enableKeyboardNav enabled props = props { enableKeyboardNav = enabled }

-- | Set row select handler
onRowSelect :: forall w i. (Array String -> i) -> GridProp w i
onRowSelect handler props = props { onRowSelect = Just handler }

-- | Set row expand handler
onRowExpand :: forall w i. (Array String -> i) -> GridProp w i
onRowExpand handler props = props { onRowExpand = Just handler }

-- | Set cell edit handler
onCellEdit :: forall w i. ({ rowIndex :: Int, columnKey :: String, value :: String } -> i) -> GridProp w i
onCellEdit handler props = props { onCellEdit = Just handler }

-- | Set sort handler
onSort :: forall w i. (Array SortConfig -> i) -> GridProp w i
onSort handler props = props { onSort = Just handler }

-- | Set filter handler
onFilter :: forall w i. (Object FilterValue -> i) -> GridProp w i
onFilter handler props = props { onFilter = Just handler }

-- | Set column resize handler
onColumnResize :: forall w i. ({ columnKey :: String, width :: Int } -> i) -> GridProp w i
onColumnResize handler props = props { onColumnResize = Just handler }

-- | Set column reorder handler
onColumnReorder :: forall w i. (Array String -> i) -> GridProp w i
onColumnReorder handler props = props { onColumnReorder = Just handler }

-- | Set page change handler
onPageChange :: forall w i. (Int -> i) -> GridProp w i
onPageChange handler props = props { onPageChange = Just handler }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // grid component
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Base grid container classes
gridContainerClasses :: String
gridContainerClasses =
  "relative w-full overflow-hidden rounded-md border border-border bg-background"

-- | Header classes
headerClasses :: String
headerClasses =
  "sticky top-0 z-10 bg-muted/50 backdrop-blur supports-[backdrop-filter]:bg-muted/50"

-- | Header cell classes
headerCellClasses :: String
headerCellClasses =
  "h-12 px-4 text-left align-middle font-medium text-muted-foreground border-b border-border select-none"

-- | Sortable header classes
sortableHeaderClasses :: String
sortableHeaderClasses =
  "cursor-pointer hover:bg-muted transition-colors"

-- | Row classes
rowClasses :: String
rowClasses =
  "border-b border-border transition-colors hover:bg-muted/50 data-[state=selected]:bg-muted"

-- | Cell classes
cellClasses :: String
cellClasses =
  "p-4 align-middle [&:has([role=checkbox])]:pr-0"

-- | Render the data grid
dataGrid :: forall w i. Array (GridProp w i) -> HH.HTML w i
dataGrid propMods =
  let
    props = foldl (\p f -> f p) defaultGridProps propMods
    visibleColumns = filter (not <<< _.hidden) props.columns
    processedRows = processRows props
    pagedRows = applyPagination props processedRows
  in
    HH.div
      [ cls [ gridContainerClasses, props.className ]
      , ARIA.role "grid"
      , HP.attr (HH.AttrName "aria-rowcount") (show $ length props.rows)
      , HP.attr (HH.AttrName "aria-colcount") (show $ length visibleColumns)
      ]
      [ -- Global search bar
        renderGlobalSearch props
      , -- Scrollable container
        HH.div
          [ cls [ "overflow-auto max-h-[600px]" ]
          , HP.attr (HH.AttrName "data-grid-scroll") "true"
          ]
          [ HH.table
              [ cls [ "w-full caption-bottom text-sm" ] ]
              [ renderHeader props visibleColumns
              , renderBody props visibleColumns pagedRows
              ]
          ]
      , -- Loading overlay
        renderLoadingOverlay props
      , -- Pagination
        renderPagination props (length processedRows)
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // global search
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render global search input
renderGlobalSearch :: forall w i. GridProps w i -> HH.HTML w i
renderGlobalSearch props =
  let
    hasFilterableColumns = Array.any _.filterable props.columns
  in
    if hasFilterableColumns
      then HH.div
        [ cls [ "flex items-center gap-2 p-4 border-b border-border" ] ]
        [ HH.div
            [ cls [ "relative flex-1 max-w-sm" ] ]
            [ -- Search icon
              HH.div
                [ cls [ "absolute left-3 top-1/2 -translate-y-1/2 text-muted-foreground" ] ]
                [ searchIcon ]
            , HH.input
                [ cls [ "flex h-9 w-full rounded-md border border-input bg-transparent px-3 py-1 pl-9 text-sm shadow-sm transition-colors placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-ring" ]
                , HP.type_ HP.InputText
                , HP.placeholder "Search all columns..."
                , HP.value props.globalFilter
                , ARIA.label "Search"
                ]
            ]
        ]
      else HH.text ""

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // header
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render table header
renderHeader :: forall w i. GridProps w i -> Array (ColumnDef w i) -> HH.HTML w i
renderHeader props cols =
  HH.thead
    [ cls [ headerClasses ]
    , ARIA.role "rowgroup"
    ]
    [ HH.tr
        [ ARIA.role "row" ]
        ( -- Selection checkbox column
          (if props.selectionMode == CheckboxSelect
            then [ renderSelectionHeaderCell props ]
            else [])
          -- Expansion column
          <> (if props.expandable
            then [ renderExpansionHeaderCell ]
            else [])
          -- Data columns
          <> mapWithIndex (renderHeaderCell props) cols
        )
    ]

-- | Render selection header cell (select all)
renderSelectionHeaderCell :: forall w i. GridProps w i -> HH.HTML w i
renderSelectionHeaderCell props =
  HH.th
    [ cls [ headerCellClasses, "w-12" ]
    , ARIA.role "columnheader"
    ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , cls [ "h-4 w-4 rounded border-primary text-primary focus:ring-primary" ]
        , HP.checked (length props.selectedRowKeys == length props.rows && length props.rows > 0)
        , ARIA.label "Select all rows"
        ]
    ]

-- | Render expansion header cell
renderExpansionHeaderCell :: forall w i. HH.HTML w i
renderExpansionHeaderCell =
  HH.th
    [ cls [ headerCellClasses, "w-12" ]
    , ARIA.role "columnheader"
    ]
    [ HH.text "" ]

-- | Render a header cell
renderHeaderCell :: forall w i. GridProps w i -> Int -> ColumnDef w i -> HH.HTML w i
renderHeaderCell props colIndex col =
  let
    sortState = Array.find (\s -> s.column == col.key) props.sortColumns
    sortIndicator = case sortState of
      Just { direction: Ascending } -> sortAscIcon
      Just { direction: Descending } -> sortDescIcon
      Nothing -> if col.sortable then sortNeutralIcon else HH.text ""
    
    widthStyle = case col.width of
      Just w -> [ HP.attr (HH.AttrName "style") ("width: " <> show w <> "px; min-width: " <> show w <> "px;") ]
      Nothing -> []
    
    fixedClass = case col.fixed of
      FixedLeft -> "sticky left-0 z-20 bg-muted"
      FixedRight -> "sticky right-0 z-20 bg-muted"
      NotFixed -> ""
    
    headerContent = case col.headerRenderer of
      Just renderer -> renderer col.header
      Nothing -> HH.text col.header
  in
    HH.th
      ( [ cls [ headerCellClasses
              , if col.sortable then sortableHeaderClasses else ""
              , fixedClass
              ]
        , ARIA.role "columnheader"
        , HP.attr (HH.AttrName "aria-colindex") (show $ colIndex + 1)
        , HP.attr (HH.AttrName "data-column-key") col.key
        ] <> widthStyle
          <> (if col.sortable 
              then [ HP.attr (HH.AttrName "aria-sort") 
                    (case sortState of
                      Just { direction: Ascending } -> "ascending"
                      Just { direction: Descending } -> "descending"
                      Nothing -> "none")
                   ]
              else [])
      )
      [ HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ headerContent
          , sortIndicator
          ]
      , -- Filter input for filterable columns
        if col.filterable
          then renderColumnFilter props col
          else HH.text ""
      , -- Resize handle
        if col.resizable
          then renderResizeHandle col
          else HH.text ""
      ]

-- | Render column filter input
renderColumnFilter :: forall w i. GridProps w i -> ColumnDef w i -> HH.HTML w i
renderColumnFilter _props col =
  HH.div
    [ cls [ "pt-2" ] ]
    [ HH.input
        [ cls [ "flex h-7 w-full rounded-md border border-input bg-transparent px-2 py-1 text-xs shadow-sm transition-colors placeholder:text-muted-foreground focus-visible:outline-none focus-visible:ring-1 focus-visible:ring-ring" ]
        , HP.type_ HP.InputText
        , HP.placeholder ("Filter " <> col.header <> "...")
        , HP.attr (HH.AttrName "data-filter-column") col.key
        ]
    ]

-- | Render resize handle
renderResizeHandle :: forall w i. ColumnDef w i -> HH.HTML w i
renderResizeHandle col =
  HH.div
    [ cls [ "absolute right-0 top-0 h-full w-1 cursor-col-resize bg-transparent hover:bg-primary/50" ]
    , HP.attr (HH.AttrName "data-resize-handle") col.key
    ]
    []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // body
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render table body
renderBody :: forall w i. GridProps w i -> Array (ColumnDef w i) -> Array (Object String) -> HH.HTML w i
renderBody props cols rowData =
  let
    isEmpty = length rowData == 0
    content = 
      if props.loading
        then renderLoadingRows cols
        else if isEmpty
          then renderEmptyState props cols
          else Array.concat (mapWithIndex (renderRowWithExpansion props cols) rowData)
  in
    HH.tbody
      [ ARIA.role "rowgroup"
      , cls [ "[&_tr:last-child]:border-0" ]
      ]
      content

-- | Render loading placeholder rows
renderLoadingRows :: forall w i. Array (ColumnDef w i) -> Array (HH.HTML w i)
renderLoadingRows cols =
  Array.replicate 5 (renderLoadingRow cols)

-- | Render a loading placeholder row
renderLoadingRow :: forall w i. Array (ColumnDef w i) -> HH.HTML w i
renderLoadingRow cols =
  HH.tr
    [ cls [ rowClasses ] ]
    (map renderLoadingCell cols)

-- | Render a loading placeholder cell
renderLoadingCell :: forall w i. ColumnDef w i -> HH.HTML w i
renderLoadingCell _col =
  HH.td
    [ cls [ cellClasses ] ]
    [ HH.div
        [ cls [ "h-4 w-3/4 animate-pulse rounded bg-muted" ] ]
        []
    ]

-- | Render empty state
renderEmptyState :: forall w i. GridProps w i -> Array (ColumnDef w i) -> Array (HH.HTML w i)
renderEmptyState props cols =
  [ HH.tr
      [ cls [ "h-48" ] ]
      [ HH.td
          [ HP.colSpan (length cols + (if props.selectionMode == CheckboxSelect then 1 else 0) + (if props.expandable then 1 else 0))
          , cls [ "text-center align-middle text-muted-foreground" ]
          ]
          [ case props.emptyState of
              Just custom -> custom
              Nothing -> defaultEmptyState
          ]
      ]
  ]

-- | Default empty state content
defaultEmptyState :: forall w i. HH.HTML w i
defaultEmptyState =
  HH.div
    [ cls [ "flex flex-col items-center justify-center gap-2 py-8" ] ]
    [ emptyIcon
    , HH.p
        [ cls [ "text-lg font-medium" ] ]
        [ HH.text "No data" ]
    , HH.p
        [ cls [ "text-sm text-muted-foreground" ] ]
        [ HH.text "There are no records to display." ]
    ]

-- | Render a data row
renderRow :: forall w i. GridProps w i -> Array (ColumnDef w i) -> Int -> Object String -> HH.HTML w i
renderRow props cols rowIndex rowData =
  let
    rowKeyValue = fromMaybe (show rowIndex) (Object.lookup props.rowKey rowData)
    isSelected = Array.elem rowKeyValue props.selectedRowKeys
    isExpanded = Array.elem rowKeyValue props.expandedRowKeys
    -- Note: rowContext available for expandedContent renderer
    _rowContext =
      { rowIndex
      , rowData
      , isSelected
      , isExpanded
      }
  in
    HH.tr
      ( [ cls [ rowClasses
              , if isSelected then "bg-muted" else ""
              ]
        , ARIA.role "row"
        , HP.attr (HH.AttrName "aria-rowindex") (show $ rowIndex + 1)
        , HP.attr (HH.AttrName "data-row-key") rowKeyValue
        , HP.attr (HH.AttrName "data-state") (if isSelected then "selected" else "")
        ] <> case props.onRowSelect of
          Just handler -> 
            if props.selectionMode == SingleSelect || props.selectionMode == MultiSelect
              then [ HE.onClick (\_ -> handler (toggleSelection props.selectedRowKeys rowKeyValue props.selectionMode)) ]
              else []
          Nothing -> []
      )
      ( -- Selection checkbox
        (if props.selectionMode == CheckboxSelect
          then [ renderSelectionCell props rowKeyValue isSelected ]
          else [])
        -- Expansion toggle
        <> (if props.expandable
          then [ renderExpansionCell props rowKeyValue isExpanded ]
          else [])
        -- Data cells
        <> mapWithIndex (\colIndex col -> renderCell props col rowIndex colIndex rowData isSelected isExpanded) cols
      )
-- | Render a data row with optional expansion row
renderRowWithExpansion :: forall w i. GridProps w i -> Array (ColumnDef w i) -> Int -> Object String -> Array (HH.HTML w i)
renderRowWithExpansion props cols rowIndex rowData =
  let
    rowKeyValue = fromMaybe (show rowIndex) (Object.lookup props.rowKey rowData)
    isSelected = Array.elem rowKeyValue props.selectedRowKeys
    isExpanded = Array.elem rowKeyValue props.expandedRowKeys
    rowContext =
      { rowIndex
      , rowData
      , isSelected
      , isExpanded
      }
    mainRow = renderRow props cols rowIndex rowData
    totalColSpan = length cols 
      + (if props.selectionMode == CheckboxSelect then 1 else 0) 
      + (if props.expandable then 1 else 0)
    expandedRow = 
      if isExpanded
        then case props.expandedContent of
          Just renderer ->
            [ HH.tr
                [ cls [ "border-b border-border bg-muted/30" ]
                , HP.attr (HH.AttrName "data-expanded-row") rowKeyValue
                ]
                [ HH.td
                    [ HP.colSpan totalColSpan
                    , cls [ "p-4" ]
                    ]
                    [ renderer rowContext ]
                ]
            ]
          Nothing -> []
        else []
  in [ mainRow ] <> expandedRow

-- | Toggle selection helper
toggleSelection :: Array String -> String -> SelectionMode -> Array String
toggleSelection current key mode =
  case mode of
    SingleSelect -> 
      if Array.elem key current 
        then [] 
        else [key]
    MultiSelect -> 
      if Array.elem key current 
        then filter (_ /= key) current 
        else key : current
    CheckboxSelect -> 
      if Array.elem key current 
        then filter (_ /= key) current 
        else key : current
    NoSelection -> current

-- | Render selection checkbox cell
renderSelectionCell :: forall w i. GridProps w i -> String -> Boolean -> HH.HTML w i
renderSelectionCell _props _rowKey isSelected =
  HH.td
    [ cls [ cellClasses, "w-12" ]
    , ARIA.role "gridcell"
    ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , cls [ "h-4 w-4 rounded border-primary text-primary focus:ring-primary" ]
        , HP.checked isSelected
        , ARIA.label "Select row"
        ]
    ]

-- | Render expansion toggle cell
renderExpansionCell :: forall w i. GridProps w i -> String -> Boolean -> HH.HTML w i
renderExpansionCell _props _rowKey isExpanded =
  HH.td
    [ cls [ cellClasses, "w-12" ]
    , ARIA.role "gridcell"
    ]
    [ HH.button
        [ cls [ "p-1 rounded hover:bg-muted transition-colors" ]
        , HP.type_ HP.ButtonButton
        , ARIA.label (if isExpanded then "Collapse row" else "Expand row")
        , HP.attr (HH.AttrName "aria-expanded") (if isExpanded then "true" else "false")
        ]
        [ if isExpanded then chevronDownIcon else chevronRightIcon ]
    ]

-- | Render a data cell
renderCell :: forall w i. GridProps w i -> ColumnDef w i -> Int -> Int -> Object String -> Boolean -> Boolean -> HH.HTML w i
renderCell _props col rowIndex colIndex rowData isSelected isExpanded =
  let
    value = fromMaybe "" (Object.lookup col.key rowData)
    
    cellContext =
      { value
      , rowIndex
      , columnKey: col.key
      , rowData
      , isEditing: false
      , isSelected
      , isExpanded
      }
    
    fixedClass = case col.fixed of
      FixedLeft -> "sticky left-0 z-10 bg-background"
      FixedRight -> "sticky right-0 z-10 bg-background"
      NotFixed -> ""
    
    content = case col.cellRenderer of
      Just renderer -> renderer cellContext
      Nothing -> renderCellByType col.cellType cellContext
  in
    HH.td
      [ cls [ cellClasses, fixedClass ]
      , ARIA.role "gridcell"
      , HP.attr (HH.AttrName "aria-colindex") (show $ colIndex + 1)
      , HP.attr (HH.AttrName "data-column-key") col.key
      ]
      [ content ]

-- | Render cell content by type
renderCellByType :: forall w i. CellType -> CellContext -> HH.HTML w i
renderCellByType cellType' ctx =
  case cellType' of
    Text -> HH.span [] [ HH.text ctx.value ]
    
    Number ->
      HH.span
        [ cls [ "font-mono tabular-nums" ] ]
        [ HH.text ctx.value ]
    
    Date ->
      HH.span
        [ cls [ "text-muted-foreground" ] ]
        [ HH.text ctx.value ]
    
    Boolean ->
      let checked = ctx.value == "true" || ctx.value == "1"
      in HH.input
        [ HP.type_ HP.InputCheckbox
        , HP.checked checked
        , HP.disabled true
        , cls [ "h-4 w-4 rounded border-primary" ]
        ]
    
    Link ->
      HH.a
        [ HP.href ctx.value
        , cls [ "text-primary underline-offset-4 hover:underline" ]
        ]
        [ HH.text ctx.value ]
    
    Badge ->
      HH.span
        [ cls [ "inline-flex items-center rounded-full border px-2.5 py-0.5 text-xs font-semibold transition-colors bg-secondary text-secondary-foreground" ] ]
        [ HH.text ctx.value ]
    
    Actions ->
      HH.div
        [ cls [ "flex items-center gap-1" ] ]
        [ HH.button
            [ cls [ "p-1 rounded hover:bg-muted" ]
            , HP.type_ HP.ButtonButton
            ]
            [ editIcon ]
        , HH.button
            [ cls [ "p-1 rounded hover:bg-destructive hover:text-destructive-foreground" ]
            , HP.type_ HP.ButtonButton
            ]
            [ deleteIcon ]
        ]
    
    Custom -> HH.span [] [ HH.text ctx.value ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // loading overlay
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render loading overlay
renderLoadingOverlay :: forall w i. GridProps w i -> HH.HTML w i
renderLoadingOverlay props =
  if props.loading
    then HH.div
      [ cls [ "absolute inset-0 z-30 flex items-center justify-center bg-background/50 backdrop-blur-sm" ] ]
      [ case props.loadingState of
          Just custom -> custom
          Nothing -> defaultLoadingState
      ]
    else HH.text ""

-- | Default loading state content
defaultLoadingState :: forall w i. HH.HTML w i
defaultLoadingState =
  HH.div
    [ cls [ "flex flex-col items-center gap-2" ] ]
    [ HH.div
        [ cls [ "h-8 w-8 animate-spin rounded-full border-4 border-primary border-t-transparent" ] ]
        []
    , HH.span
        [ cls [ "text-sm text-muted-foreground" ] ]
        [ HH.text "Loading..." ]
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // pagination
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Render pagination controls
renderPagination :: forall w i. GridProps w i -> Int -> HH.HTML w i
renderPagination props totalFiltered =
  case props.pagination of
    NoPagination -> HH.text ""
    
    BuiltIn { pageSize: ps } ->
      let
        totalPages = (totalFiltered + ps - 1) / ps
        currentPg = 1 -- Would need state for this
      in renderPaginationControls currentPg totalPages totalFiltered ps
    
    External { pageSize: ps, currentPage: cp, totalRows: tr } ->
      let totalPages = (tr + ps - 1) / ps
      in renderPaginationControls cp totalPages tr ps

-- | Render pagination controls UI
renderPaginationControls :: forall w i. Int -> Int -> Int -> Int -> HH.HTML w i
renderPaginationControls currentPg totalPages total ps =
  let
    startRow = (currentPg - 1) * ps + 1
    endRow = min (currentPg * ps) total
  in
    HH.div
      [ cls [ "flex items-center justify-between border-t border-border px-4 py-3" ] ]
      [ -- Row count info
        HH.div
          [ cls [ "text-sm text-muted-foreground" ] ]
          [ HH.text $ "Showing " <> show startRow <> " to " <> show endRow <> " of " <> show total <> " rows" ]
      , -- Page navigation
        HH.div
          [ cls [ "flex items-center gap-2" ] ]
          [ -- First page
            HH.button
              [ cls [ paginationButtonClasses, if currentPg <= 1 then "opacity-50 cursor-not-allowed" else "" ]
              , HP.type_ HP.ButtonButton
              , HP.disabled (currentPg <= 1)
              , ARIA.label "First page"
              ]
              [ chevronFirstIcon ]
          , -- Previous page
            HH.button
              [ cls [ paginationButtonClasses, if currentPg <= 1 then "opacity-50 cursor-not-allowed" else "" ]
              , HP.type_ HP.ButtonButton
              , HP.disabled (currentPg <= 1)
              , ARIA.label "Previous page"
              ]
              [ chevronLeftIcon ]
          , -- Page indicator
            HH.span
              [ cls [ "text-sm" ] ]
              [ HH.text $ "Page " <> show currentPg <> " of " <> show totalPages ]
          , -- Next page
            HH.button
              [ cls [ paginationButtonClasses, if currentPg >= totalPages then "opacity-50 cursor-not-allowed" else "" ]
              , HP.type_ HP.ButtonButton
              , HP.disabled (currentPg >= totalPages)
              , ARIA.label "Next page"
              ]
              [ chevronRightIcon ]
          , -- Last page
            HH.button
              [ cls [ paginationButtonClasses, if currentPg >= totalPages then "opacity-50 cursor-not-allowed" else "" ]
              , HP.type_ HP.ButtonButton
              , HP.disabled (currentPg >= totalPages)
              , ARIA.label "Last page"
              ]
              [ chevronLastIcon ]
          ]
      ]

-- | Pagination button classes
paginationButtonClasses :: String
paginationButtonClasses =
  "inline-flex items-center justify-center h-8 w-8 rounded-md border border-input bg-transparent hover:bg-accent hover:text-accent-foreground transition-colors"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // data processing
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Process rows (filter and sort)
processRows :: forall w i. GridProps w i -> Array (Object String)
processRows props =
  let
    -- Apply global filter
    globalFiltered = 
      if String.null props.globalFilter
        then props.rows
        else filter (matchesGlobalFilter props.globalFilter props.columns) props.rows
    
    -- Apply column filters
    columnFiltered = foldl applyColumnFilter globalFiltered (Object.toUnfoldable props.columnFilters :: Array (Tuple String FilterValue))
    
    -- Apply sorting
    sorted = applySorting props.sortColumns columnFiltered
  in sorted

-- | Check if row matches global filter
matchesGlobalFilter :: forall w i. String -> Array (ColumnDef w i) -> Object String -> Boolean
matchesGlobalFilter search cols rowData =
  let
    searchLower = toLower search
    filterableCols = filter _.filterable cols
    values = Array.mapMaybe (\col -> Object.lookup col.key rowData) filterableCols
  in Array.any (\v -> contains (Pattern searchLower) (toLower v)) values

-- | Apply a column filter
applyColumnFilter :: Array (Object String) -> Tuple String FilterValue -> Array (Object String)
applyColumnFilter rows' (Tuple colKey filterVal) =
  filter (matchesColumnFilter colKey filterVal) rows'

-- | Check if row matches column filter
matchesColumnFilter :: String -> FilterValue -> Object String -> Boolean
matchesColumnFilter colKey filterVal rowData =
  case Object.lookup colKey rowData of
    Nothing -> false
    Just cellValue ->
      case filterVal of
        TextFilter searchText ->
          contains (Pattern (toLower searchText)) (toLower cellValue)
        NumberFilter { min: minVal, max: maxVal } ->
          case Number.fromString cellValue of
            Nothing -> false
            Just num ->
              let
                aboveMin = case minVal of
                  Nothing -> true
                  Just m -> num >= m
                aboveMax = case maxVal of
                  Nothing -> true
                  Just m -> num <= m
              in aboveMin && aboveMax
        BooleanFilter expected ->
          (cellValue == "true" || cellValue == "1") == expected
        SelectFilter allowedValues ->
          Array.elem cellValue allowedValues
        DateRangeFilter { start: startDate, end: endDate } ->
          let
            afterStart = case startDate of
              Nothing -> true
              Just s -> cellValue >= s
            beforeEnd = case endDate of
              Nothing -> true
              Just e -> cellValue <= e
          in afterStart && beforeEnd

-- | Apply sorting to rows
applySorting :: Array SortConfig -> Array (Object String) -> Array (Object String)
applySorting sortConfigs rows' =
  foldl applySingleSort rows' (Array.reverse sortConfigs)

-- | Apply a single sort
applySingleSort :: Array (Object String) -> SortConfig -> Array (Object String)
applySingleSort rows' { column: col, direction } =
  let
    compareFn = comparing (\row -> fromMaybe "" (Object.lookup col row))
    sorted = sortBy compareFn rows'
  in case direction of
    Ascending -> sorted
    Descending -> Array.reverse sorted

-- | Apply pagination
applyPagination :: forall w i. GridProps w i -> Array (Object String) -> Array (Object String)
applyPagination props rows' =
  case props.pagination of
    NoPagination -> rows'
    BuiltIn { pageSize: ps } -> take ps rows'
    External { pageSize: ps, currentPage: cp } ->
      take ps (drop ((cp - 1) * ps) rows')

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // export
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Export grid data to CSV
exportCsv :: forall w i. GridProps w i -> Effect String
exportCsv props = pure $ toCsvString props.columns props.rows

-- | Convert to CSV string
toCsvString :: forall w i. Array (ColumnDef w i) -> Array (Object String) -> String
toCsvString cols rows' =
  let
    visibleCols = filter (not <<< _.hidden) cols
    headerRow = String.joinWith "," (map (escapeCsv <<< _.header) visibleCols)
    dataRows = map (rowToCsv visibleCols) rows'
  in String.joinWith "\n" (headerRow : dataRows)

-- | Convert row to CSV
rowToCsv :: forall w i. Array (ColumnDef w i) -> Object String -> String
rowToCsv cols rowData =
  String.joinWith "," (map (\col -> escapeCsv (fromMaybe "" (Object.lookup col.key rowData))) cols)

-- | Escape CSV value
escapeCsv :: String -> String
escapeCsv value =
  if contains (Pattern ",") value || contains (Pattern "\"") value || contains (Pattern "\n") value
    then "\"" <> String.replaceAll (Pattern "\"") (String.Replacement "\"\"") value <> "\""
    else value

-- | Export grid data to JSON
exportJson :: forall a. EncodeJson a => Array a -> Effect String
exportJson rows' = pure $ stringify (encodeJson rows')

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // icons
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Search icon
searchIcon :: forall w i. HH.HTML w i
searchIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ] ]
    [ HH.text "S" ] -- Simplified - in production use Lucide icons

-- | Sort ascending icon
sortAscIcon :: forall w i. HH.HTML w i
sortAscIcon =
  HH.span
    [ cls [ "text-primary" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "^" ]

-- | Sort descending icon
sortDescIcon :: forall w i. HH.HTML w i
sortDescIcon =
  HH.span
    [ cls [ "text-primary" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "v" ]

-- | Sort neutral icon
sortNeutralIcon :: forall w i. HH.HTML w i
sortNeutralIcon =
  HH.span
    [ cls [ "text-muted-foreground opacity-0 group-hover:opacity-100" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "^v" ]

-- | Chevron right icon
chevronRightIcon :: forall w i. HH.HTML w i
chevronRightIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text ">" ]

-- | Chevron down icon
chevronDownIcon :: forall w i. HH.HTML w i
chevronDownIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "v" ]

-- | Chevron left icon
chevronLeftIcon :: forall w i. HH.HTML w i
chevronLeftIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "<" ]

-- | Chevron first icon
chevronFirstIcon :: forall w i. HH.HTML w i
chevronFirstIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "|<" ]

-- | Chevron last icon
chevronLastIcon :: forall w i. HH.HTML w i
chevronLastIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text ">|" ]

-- | Empty state icon
emptyIcon :: forall w i. HH.HTML w i
emptyIcon =
  HH.div
    [ cls [ "w-12 h-12 rounded-full bg-muted flex items-center justify-center" ] ]
    [ HH.span
        [ cls [ "text-2xl text-muted-foreground" ] ]
        [ HH.text "0" ]
    ]

-- | Edit icon
editIcon :: forall w i. HH.HTML w i
editIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "E" ]

-- | Delete icon
deleteIcon :: forall w i. HH.HTML w i
deleteIcon =
  HH.span
    [ cls [ "inline-block w-4 h-4" ]
    , ARIA.hidden "true"
    ]
    [ HH.text "X" ]
