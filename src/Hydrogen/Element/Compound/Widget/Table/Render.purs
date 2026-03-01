-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // element // table // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Table Render — Rendering functions for table components.
-- |
-- | ## Overview
-- |
-- | This module contains all rendering logic for Table widgets:
-- | - Main table widget composition
-- | - Header, body, and cell rendering
-- | - Search box rendering
-- | - Pagination controls rendering
-- | - Sparkline SVG generation

module Hydrogen.Element.Compound.Widget.Table.Render
  ( -- * Widget Components
    tableWidget
  , tableWidgetSimple
  
  -- * Render Functions
  , renderSearchBox
  , renderTableHeader
  , renderHeaderCell
  , renderTableBody
  , renderTableRow
  , renderTableCell
  , renderCellContent
  , renderPagination
  , renderMiniSparkline
  , generateSparklinePath
  ) where

import Prelude
  ( class Show
  , show
  , (==)
  , (&&)
  , (<>)
  , (-)
  , (/)
  , (*)
  , (<=)
  )

import Data.Array (foldl, length, mapWithIndex, index)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Widget.Types (Percentage, unwrapPercentage)
import Hydrogen.Element.Compound.Widget.Table.Types 
  ( ColumnDef
  , ColumnType(ColText)
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
  , Pagination
  , SortDirection(SortAsc, SortDesc)
  , TableData
  , defaultColumn
  )
import Hydrogen.Element.Compound.Widget.Table.Props (TableProps, TableProp, defaultProps)
import Hydrogen.Element.Compound.Widget.Table.Pagination (hasNextPage, hasPrevPage, pageRange)
import Hydrogen.Element.Compound.Widget.Table.Helpers (arrayMin, arrayMax, formatNumber, toNumber, mod)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a table widget.
-- |
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
tableWidget :: forall msg. Array TableProp -> TableData -> E.Element msg
tableWidget propMods tableData =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    containerCls = "rounded-lg border bg-card text-card-foreground overflow-hidden" <> 
                   " " <> props.className
    
    tableCls = "w-full" <>
               (if props.bordered then " divide-y" else "") <>
               (if props.compact then " text-sm" else "")
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Search box
        if tableData.searchable
          then renderSearchBox
          else E.text ""
      
      -- Table
      , E.div_
          [ E.class_ "overflow-x-auto" ]
          [ E.table_
              [ E.class_ tableCls ]
              [ renderTableHeader tableData.columns tableData.sortBy tableData.sortDir
              , renderTableBody props tableData.columns tableData.rows
              ]
          ]
      
      -- Pagination
      , case tableData.pagination of
          Just p -> renderPagination p
          Nothing -> E.text ""
      ]

-- | Simple table widget (minimal configuration).
tableWidgetSimple :: forall msg. 
  Array String ->          -- ^ Column labels
  Array (Array String) ->  -- ^ Row data as strings
  E.Element msg
tableWidgetSimple headers rows =
  let
    columns = mapWithIndex (\idx label ->
      { key: "col" <> show idx
      , label: label
      , colType: ColText
      , width: Nothing
      , align: Nothing
      , sortable: false
      , format: Nothing
      }
    ) headers
    
    tableRows = mapWithIndex (\_ row ->
      mapWithIndex (\_ cell -> TextCell cell) row
    ) rows
    
    tableData :: TableData
    tableData =
      { columns: columns
      , rows: tableRows
      , pagination: Nothing
      , sortBy: Nothing
      , sortDir: Nothing
      , selectable: false
      , searchable: false
      }
  in
    tableWidget [] tableData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // render helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render search box.
renderSearchBox :: forall msg. E.Element msg
renderSearchBox =
  E.div_
    [ E.class_ "p-4 border-b" ]
    [ E.input_
        [ E.attr "type" "search"
        , E.attr "placeholder" "Search..."
        , E.class_ "w-full px-3 py-2 border rounded-md text-sm bg-background"
        ]
    ]

-- | Render table header.
renderTableHeader :: forall msg. 
  Array ColumnDef -> 
  Maybe String -> 
  Maybe SortDirection -> 
  E.Element msg
renderTableHeader columns sortBy sortDir =
  E.thead_
    [ E.class_ "bg-muted/50" ]
    [ E.tr_
        []
        (mapWithIndex (\_ col -> renderHeaderCell col sortBy sortDir) columns)
    ]

-- | Render header cell.
renderHeaderCell :: forall msg. 
  ColumnDef -> 
  Maybe String -> 
  Maybe SortDirection -> 
  E.Element msg
renderHeaderCell col sortBy sortDir =
  let
    isSorted = sortBy == Just col.key
    sortIcon = if isSorted
                 then case sortDir of
                   Just SortAsc -> " ↑"
                   Just SortDesc -> " ↓"
                   Nothing -> ""
                 else ""
    
    alignCls = case col.align of
      Just "center" -> "text-center"
      Just "right" -> "text-right"
      _ -> "text-left"
    
    widthStyle = case col.width of
      Just w -> [ E.style "width" (show w <> "px") ]
      Nothing -> []
    
    cellCls = "px-4 py-3 font-medium text-sm " <> alignCls <>
              (if col.sortable then " cursor-pointer hover:bg-muted" else "")
  in
    E.th_
      ([ E.class_ cellCls ] <> widthStyle)
      [ E.text (col.label <> sortIcon) ]

-- | Render table body.
renderTableBody :: forall msg. TableProps -> Array ColumnDef -> Array (Array CellValue) -> E.Element msg
renderTableBody props columns rows =
  E.tbody_
    [ E.class_ (if props.striped then "divide-y" else "") ]
    (mapWithIndex (\idx row -> renderTableRow props columns idx row) rows)

-- | Render table row.
renderTableRow :: forall msg. TableProps -> Array ColumnDef -> Int -> Array CellValue -> E.Element msg
renderTableRow props columns idx cells =
  let
    rowCls = (if props.striped && (idx `mod` 2) == 1 then "bg-muted/30" else "") <>
             " hover:bg-muted/50 transition-colors"
  in
    E.tr_
      [ E.class_ rowCls ]
      (mapWithIndex (\colIdx cell ->
        let col = fromMaybe defaultColumn (index columns colIdx)
        in renderTableCell props col cell
      ) cells)

-- | Render table cell.
renderTableCell :: forall msg. TableProps -> ColumnDef -> CellValue -> E.Element msg
renderTableCell props col cell =
  let
    alignCls = case col.align of
      Just "center" -> "text-center"
      Just "right" -> "text-right"
      _ -> "text-left"
    
    paddingCls = if props.compact then "px-3 py-2" else "px-4 py-3"
    cellCls = paddingCls <> " " <> alignCls
  in
    E.td_
      [ E.class_ cellCls ]
      [ renderCellContent cell ]

-- | Render cell content based on type.
renderCellContent :: forall msg. CellValue -> E.Element msg
renderCellContent cell = case cell of
  TextCell s -> E.text s
  
  NumberCell n -> 
    E.span_ [ E.class_ "tabular-nums" ] [ E.text (formatNumber n) ]
  
  CurrencyCell n code ->
    E.span_ [ E.class_ "tabular-nums" ] 
      [ E.text (code <> " " <> formatNumber n) ]
  
  PercentCell n ->
    E.span_ [ E.class_ "tabular-nums" ] [ E.text (show n <> "%") ]
  
  DateCell s -> E.text s
  
  BoolCell b ->
    if b
      then E.span_ [ E.class_ "text-green-500" ] [ E.text "Yes" ]
      else E.span_ [ E.class_ "text-muted-foreground" ] [ E.text "No" ]
  
  BadgeCell text variant ->
    let
      variantCls = case variant of
        "success" -> "bg-green-100 text-green-800"
        "warning" -> "bg-yellow-100 text-yellow-800"
        "error" -> "bg-red-100 text-red-800"
        "info" -> "bg-blue-100 text-blue-800"
        _ -> "bg-gray-100 text-gray-800"
    in
      E.span_
        [ E.class_ ("px-2 py-1 rounded-full text-xs font-medium " <> variantCls) ]
        [ E.text text ]
  
  SparklineCell points ->
    renderMiniSparkline points
  
  ProgressCell pct ->
    let
      width = show (unwrapPercentage pct) <> "%"
    in
      E.div_
        [ E.class_ "w-24 h-2 bg-muted rounded-full overflow-hidden" ]
        [ E.div_
            [ E.class_ "h-full bg-primary rounded-full"
            , E.style "width" width
            ]
            []
        ]
  
  EmptyCell -> E.text "—"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // sparkline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render mini sparkline for table cell.
renderMiniSparkline :: forall msg. Array Number -> E.Element msg
renderMiniSparkline points =
  if length points <= 1
    then E.text "—"
    else
      let
        minVal = arrayMin points
        maxVal = arrayMax points
        range = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
        width = 60.0
        height = 20.0
        
        pathData = generateSparklinePath points width height minVal range
      in
        E.svg_
          [ E.attr "viewBox" ("0 0 " <> show width <> " " <> show height)
          , E.class_ "w-16 h-5"
          ]
          [ E.path_
              [ E.attr "d" pathData
              , E.attr "fill" "none"
              , E.attr "stroke" "currentColor"
              , E.attr "stroke-width" "1.5"
              , E.class_ "text-primary"
              ]
          ]

-- | Generate sparkline path.
generateSparklinePath :: Array Number -> Number -> Number -> Number -> Number -> String
generateSparklinePath points width height minVal range =
  let
    numPoints = length points
    step = if numPoints <= 1 then width else width / toNumber (numPoints - 1)
    
    pathParts = mapWithIndex (\idx val ->
      let x = toNumber idx * step
          y = height - ((val - minVal) / range * height)
      in if idx == 0
           then "M " <> show x <> " " <> show y
           else "L " <> show x <> " " <> show y
    ) points
  in
    foldl (\acc part -> acc <> " " <> part) "" pathParts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // pagination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render pagination controls.
renderPagination :: forall msg. Pagination -> E.Element msg
renderPagination p =
  E.div_
    [ E.class_ "flex items-center justify-between px-4 py-3 border-t text-sm" ]
    [ -- Info text
      E.span_
        [ E.class_ "text-muted-foreground" ]
        [ E.text ("Page " <> show p.page <> " of " <> show p.totalPages <> 
                  " (" <> show p.total <> " items)") ]
    
    -- Navigation buttons
    , E.div_
        [ E.class_ "flex items-center gap-2" ]
        [ -- Previous button
          E.button_
            [ E.class_ ("px-3 py-1 rounded border " <>
                       if hasPrevPage p then "hover:bg-muted" else "opacity-50 cursor-not-allowed")
            , E.attr "disabled" (if hasPrevPage p then "false" else "true")
            ]
            [ E.text "Previous" ]
        
        -- Page numbers
        , E.div_
            [ E.class_ "flex items-center gap-1" ]
            (mapWithIndex (\_ pageNum ->
              E.button_
                [ E.class_ ("w-8 h-8 rounded " <>
                           if pageNum == p.page 
                             then "bg-primary text-primary-foreground"
                             else "hover:bg-muted")
                ]
                [ E.text (show pageNum) ]
            ) (pageRange p 5))
        
        -- Next button
        , E.button_
            [ E.class_ ("px-3 py-1 rounded border " <>
                       if hasNextPage p then "hover:bg-muted" else "opacity-50 cursor-not-allowed")
            , E.attr "disabled" (if hasNextPage p then "false" else "true")
            ]
            [ E.text "Next" ]
        ]
    ]
