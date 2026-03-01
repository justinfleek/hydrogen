-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // data-grid // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Rendering — Internal rendering functions for grid components.
-- |
-- | This module contains all the rendering functions used by the DataGrid
-- | component. It handles:
-- |
-- | - Global search input
-- | - Table header with sorting indicators
-- | - Table body with rows and cells
-- | - Loading states (skeleton rows, overlay)
-- | - Empty state
-- | - Pagination controls

module Hydrogen.Element.Compound.DataGrid.Render
  ( -- * Primary Render Functions
    renderGlobalSearch
  , renderHeader
  , renderBody
  , renderLoadingOverlay
  ) where

import Prelude
  ( (==)
  , (>)
  , (+)
  , (<>)
  , show
  , map
  )

import Data.Array (filter, mapWithIndex, length, elem)
import Data.Maybe (Maybe(Nothing, Just), maybe, fromMaybe)
import Foreign.Object (Object)
import Foreign.Object as Object

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Typography.FontSize as FontSize

import Hydrogen.Element.Compound.DataGrid.Types
  ( CellContext
  , ColumnDef
  , FixedPosition(FixedLeft, FixedRight, NotFixed)
  , GridProps
  , SelectionMode(CheckboxSelect)
  )
import Hydrogen.Element.Compound.DataGrid.Cell as Cell

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // global search
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render global search input.
-- |
-- | Only renders if there are filterable columns.
renderGlobalSearch :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderGlobalSearch props cols =
  let
    hasFilterableColumns = length (filter (\col -> col.filterable) cols) > 0
  in
    if hasFilterableColumns
      then E.div_
        ( [ E.style "padding" "1rem"
          , E.style "border-bottom" "1px solid"
          ]
          <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        )
        [ E.input_
            [ E.type_ "text"
            , E.placeholder "Search all columns..."
            , E.value props.globalFilter
            , E.ariaLabel "Search"
            , E.style "width" "100%"
            , E.style "max-width" "24rem"
            , E.style "padding" "0.5rem 0.75rem"
            , E.style "border" "1px solid"
            , E.style "border-radius" "0.375rem"
            ]
        ]
      else E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // header
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render table header.
-- |
-- | Includes selection checkbox column, expansion column, and data columns.
renderHeader :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderHeader props cols =
  E.thead_
    ( [ E.role "rowgroup"
      , E.style "position" "sticky"
      , E.style "top" "0"
      , E.style "z-index" "10"
      ]
      <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.headerBgColor
    )
    [ E.tr_
        [ E.role "row" ]
        ( -- Selection checkbox column
          (if props.selectionMode == CheckboxSelect
            then [renderSelectionHeaderCell props]
            else [])
          -- Expansion column
          <> (if props.expandable
            then [renderExpansionHeaderCell]
            else [])
          -- Data columns
          <> mapWithIndex (renderHeaderCell props) cols
        )
    ]

-- | Render selection header cell (select all).
renderSelectionHeaderCell :: forall msg. GridProps msg -> E.Element msg
renderSelectionHeaderCell props =
  E.th_
    ( [ E.role "columnheader"
      , E.style "width" "3rem"
      , E.style "padding" "0.75rem 1rem"
      , E.style "text-align" "center"
      , E.style "border-bottom" "1px solid"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ E.input_
        [ E.type_ "checkbox"
        , E.checked (length props.selectedRowKeys == length props.rows)
        , E.ariaLabel "Select all rows"
        , E.style "width" "1rem"
        , E.style "height" "1rem"
        ]
    ]

-- | Render expansion header cell.
renderExpansionHeaderCell :: forall msg. E.Element msg
renderExpansionHeaderCell =
  E.th_
    [ E.role "columnheader"
    , E.style "width" "3rem"
    , E.style "padding" "0.75rem 1rem"
    ]
    [ E.empty ]

-- | Render a header cell.
renderHeaderCell :: forall msg. GridProps msg -> Int -> ColumnDef msg -> E.Element msg
renderHeaderCell props colIndex col =
  let
    widthStyle = case col.width of
      Just w -> [E.style "width" (show w <> "px"), E.style "min-width" (show w <> "px")]
      Nothing -> []
    
    fixedStyle = case col.fixed of
      FixedLeft -> [E.style "position" "sticky", E.style "left" "0", E.style "z-index" "20"]
      FixedRight -> [E.style "position" "sticky", E.style "right" "0", E.style "z-index" "20"]
      NotFixed -> []
    
    headerContent = case col.headerRenderer of
      Just renderer -> renderer col.header
      Nothing -> E.text col.header
  in
    E.th_
      ( [ E.role "columnheader"
        , E.attr "aria-colindex" (show (colIndex + 1))
        , E.attr "data-column-key" col.key
        , E.style "padding" "0.75rem 1rem"
        , E.style "text-align" "left"
        , E.style "font-weight" "500"
        , E.style "border-bottom" "1px solid"
        , E.style "user-select" "none"
        ]
        <> widthStyle
        <> fixedStyle
        <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.headerTextColor
        <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.headerBgColor
        <> maybe [] (\s -> [E.style "font-size" (FontSize.toLegacyCss s)]) props.headerFontSize
        <> (if col.sortable then [E.style "cursor" "pointer"] else [])
      )
      [ headerContent ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // body
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render table body.
-- |
-- | Shows loading rows, empty state, or data rows depending on state.
renderBody :: forall msg. GridProps msg -> Array (ColumnDef msg) -> Array (Object String) -> E.Element msg
renderBody props cols rowData =
  let
    isEmpty = length rowData == 0
    content =
      if props.loading
        then renderLoadingRows props cols
        else if isEmpty
          then [renderEmptyState props cols]
          else mapWithIndex (renderRow props cols) rowData
  in
    E.tbody_
      [ E.role "rowgroup" ]
      content

-- | Render loading placeholder rows.
renderLoadingRows :: forall msg. GridProps msg -> Array (ColumnDef msg) -> Array (E.Element msg)
renderLoadingRows props cols =
  map (\_ -> renderLoadingRow props cols) [1, 2, 3, 4, 5]

-- | Render a loading placeholder row.
renderLoadingRow :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderLoadingRow props cols =
  E.tr_
    ( [ E.style "border-bottom" "1px solid" ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    (map (renderLoadingCell props) cols)

-- | Render a loading placeholder cell.
renderLoadingCell :: forall msg. GridProps msg -> ColumnDef msg -> E.Element msg
renderLoadingCell props _col =
  E.td_
    ( [ E.style "padding" "1rem" ]
      <> maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.cellPaddingX
      <> maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.cellPaddingY
    )
    [ E.div_
        [ E.style "height" "1rem"
        , E.style "width" "75%"
        , E.style "border-radius" "0.25rem"
        , E.style "background-color" "currentColor"
        , E.style "opacity" "0.1"
        , E.style "animation" "pulse 2s cubic-bezier(0.4, 0, 0.6, 1) infinite"
        ]
        []
    ]

-- | Render empty state.
renderEmptyState :: forall msg. GridProps msg -> Array (ColumnDef msg) -> E.Element msg
renderEmptyState props cols =
  let
    colSpan = length cols
      + (if props.selectionMode == CheckboxSelect then 1 else 0)
      + (if props.expandable then 1 else 0)
  in
    E.tr_
      [ E.style "height" "12rem" ]
      [ E.td_
          [ E.attr "colspan" (show colSpan)
          , E.style "text-align" "center"
          , E.style "vertical-align" "middle"
          ]
          [ case props.emptyState of
              Just custom -> custom
              Nothing -> defaultEmptyState props
          ]
      ]

-- | Default empty state content.
defaultEmptyState :: forall msg. GridProps msg -> E.Element msg
defaultEmptyState props =
  E.div_
    ( [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "gap" "0.5rem"
      , E.style "padding" "2rem"
      ]
      <> maybe [] (\c -> [E.style "color" (Color.toLegacyCss c)]) props.cellTextColor
    )
    [ E.p_
        [ E.style "font-size" "1.125rem"
        , E.style "font-weight" "500"
        ]
        [ E.text "No data" ]
    , E.p_
        [ E.style "font-size" "0.875rem"
        , E.style "opacity" "0.7"
        ]
        [ E.text "There are no records to display." ]
    ]

-- | Render a data row.
renderRow :: forall msg. GridProps msg -> Array (ColumnDef msg) -> Int -> Object String -> E.Element msg
renderRow props cols rowIndex rowData =
  let
    rowKeyValue = fromMaybe (show rowIndex) (Object.lookup props.rowKey rowData)
    isSelected = elem rowKeyValue props.selectedRowKeys
    isExpanded = elem rowKeyValue props.expandedRowKeys
  in
    E.tr_
      ( [ E.role "row"
        , E.attr "aria-rowindex" (show (rowIndex + 1))
        , E.attr "data-row-key" rowKeyValue
        , E.style "border-bottom" "1px solid"
        , E.style "transition" "background-color 0.15s"
        ]
        <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
        <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.rowBgColor
        <> (if isSelected then maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.rowSelectedBgColor else [])
        <> maybe [] (\h -> [E.style "height" (show h)]) props.rowHeight
      )
      ( -- Selection checkbox
        (if props.selectionMode == CheckboxSelect
          then [renderSelectionCell props rowKeyValue isSelected]
          else [])
        -- Expansion toggle
        <> (if props.expandable
          then [renderExpansionCell props rowKeyValue isExpanded]
          else [])
        -- Data cells
        <> mapWithIndex (\colIndex col -> renderDataCell props col rowIndex colIndex rowData isSelected isExpanded) cols
      )

-- | Render selection checkbox cell.
renderSelectionCell :: forall msg. GridProps msg -> String -> Boolean -> E.Element msg
renderSelectionCell props _rowKey isSelected =
  E.td_
    ( [ E.role "gridcell"
      , E.style "width" "3rem"
      , E.style "padding" "0.75rem 1rem"
      , E.style "text-align" "center"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ E.input_
        [ E.type_ "checkbox"
        , E.checked isSelected
        , E.ariaLabel "Select row"
        , E.style "width" "1rem"
        , E.style "height" "1rem"
        ]
    ]

-- | Render expansion toggle cell.
renderExpansionCell :: forall msg. GridProps msg -> String -> Boolean -> E.Element msg
renderExpansionCell props _rowKey isExpanded =
  E.td_
    ( [ E.role "gridcell"
      , E.style "width" "3rem"
      , E.style "padding" "0.75rem 1rem"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ E.button_
        [ E.type_ "button"
        , E.ariaLabel (if isExpanded then "Collapse row" else "Expand row")
        , E.attr "aria-expanded" (if isExpanded then "true" else "false")
        , E.style "padding" "0.25rem"
        , E.style "border-radius" "0.25rem"
        , E.style "border" "none"
        , E.style "background" "transparent"
        , E.style "cursor" "pointer"
        ]
        [ E.text (if isExpanded then "v" else ">") ]
    ]

-- | Render a data cell.
renderDataCell :: forall msg. GridProps msg -> ColumnDef msg -> Int -> Int -> Object String -> Boolean -> Boolean -> E.Element msg
renderDataCell props col rowIndex colIndex rowData isSelected isExpanded =
  let
    value = fromMaybe "" (Object.lookup col.key rowData)
    
    cellContext :: CellContext
    cellContext =
      { value
      , rowIndex
      , columnKey: col.key
      , rowData
      , isEditing: false
      , isSelected
      , isExpanded
      }
    
    fixedStyle = case col.fixed of
      FixedLeft -> [E.style "position" "sticky", E.style "left" "0", E.style "z-index" "10"]
      FixedRight -> [E.style "position" "sticky", E.style "right" "0", E.style "z-index" "10"]
      NotFixed -> []
  in
    E.td_
      ( [ E.role "gridcell"
        , E.attr "aria-colindex" (show (colIndex + 1))
        , E.attr "data-column-key" col.key
        , E.style "padding" "1rem"
        ]
        <> fixedStyle
        <> maybe [] (\p -> [E.style "padding-left" (show p), E.style "padding-right" (show p)]) props.cellPaddingX
        <> maybe [] (\p -> [E.style "padding-top" (show p), E.style "padding-bottom" (show p)]) props.cellPaddingY
        <> maybe [] (\c -> [E.style "background-color" (Color.toLegacyCss c)]) props.rowBgColor
      )
      [ Cell.renderCell props col rowIndex colIndex cellContext ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // loading overlay
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render loading overlay.
-- |
-- | Shows a semi-transparent overlay with a loading indicator.
renderLoadingOverlay :: forall msg. GridProps msg -> E.Element msg
renderLoadingOverlay props =
  if props.loading
    then E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "z-index" "30"
      , E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "background-color" "rgba(255, 255, 255, 0.5)"
      , E.style "backdrop-filter" "blur(2px)"
      ]
      [ case props.loadingState of
          Just custom -> custom
          Nothing -> defaultLoadingState props
      ]
    else E.empty

-- | Default loading state content.
defaultLoadingState :: forall msg. GridProps msg -> E.Element msg
defaultLoadingState props =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "align-items" "center"
    , E.style "gap" "0.5rem"
    ]
    [ E.div_
        ( [ E.style "width" "2rem"
          , E.style "height" "2rem"
          , E.style "border-radius" "50%"
          , E.style "border-width" "4px"
          , E.style "border-style" "solid"
          , E.style "border-top-color" "transparent"
          , E.style "animation" "spin 1s linear infinite"
          ]
          <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.loadingSpinnerColor
        )
        []
    , E.span_
        [ E.style "font-size" "0.875rem"
        , E.style "opacity" "0.7"
        ]
        [ E.text "Loading..." ]
    ]


