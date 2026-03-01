-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // kanban // render // board
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Board Render — Pure Element rendering for Kanban boards and columns.
-- |
-- | ## Design Philosophy
-- |
-- | The board is the top-level container for columns. Columns are vertical
-- | containers for cards with headers that show title and count.
-- |
-- | All styling uses Schema atoms — no CSS strings, no Tailwind classes.

module Hydrogen.Element.Compound.Kanban.Render.Board
  ( -- * Board Render
    renderBoard
  
  -- * Column Render
  , renderColumn
  , renderColumnHeader
  , renderColumnContent
  
  -- * Add Card Button
  , renderAddCardButton
  , renderAddCardButtonWithConfig
  ) where

import Prelude
  ( map
  , show
  , ($)
  , (<>)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry

import Hydrogen.Element.Compound.Kanban.Types
  ( ColumnId
  , KanbanMsg
      ( MoveCard
      , AddCard
      , ToggleColumnCollapse
      , EndDrag
      , DeselectCard
      )
  , unwrapColumnId
  )
import Hydrogen.Element.Compound.Kanban.Card
  ( KanbanCard
  )
import Hydrogen.Element.Compound.Kanban.Column
  ( KanbanColumn
  , columnIdOf
  , columnTitle
  , columnColor
  , columnCollapsed
  , columnCollapsible
  , columnCardCountLabel
  , isColumnOverWIP
  )
import Hydrogen.Element.Compound.Kanban.State
  ( KanbanState
  , getColumns
  , getCardsInColumn
  , cardCountInColumn
  , getDraggedCard
  , isDragging
  )
import Hydrogen.Element.Compound.Kanban.Render.Config
  ( KanbanConfig
  , KanbanProp
  , defaultConfig
  )
import Hydrogen.Element.Compound.Kanban.Render.Card
  ( renderCardWithSelection
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // board render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render complete Kanban board
renderBoard :: Array KanbanProp -> KanbanState -> E.Element KanbanMsg
renderBoard props state =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
    columns = getColumns state
  in
    E.div_
      ([ E.role "region"
       , E.ariaLabel "Kanban board"
       ] <> E.styles
          [ Tuple "display" "flex"
          , Tuple "gap" $ show cfg.gap
          , Tuple "padding" $ show cfg.padding
          , Tuple "overflow-x" "auto"
          , Tuple "min-height" "500px"
          , Tuple "background-color" $ Color.toHex cfg.backgroundColor
          ])
      (map (renderColumn props state) columns)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // column render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single column
renderColumn :: Array KanbanProp -> KanbanState -> KanbanColumn -> E.Element KanbanMsg
renderColumn props state col =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
    colId = columnIdOf col
    cards = getCardsInColumn colId state
    cardCnt = cardCountInColumn colId state
    isCollapsed = columnCollapsed col
    isOverWIP = isColumnOverWIP cardCnt col
    
    headerBgColor = case columnColor col of
      Just c -> c
      Nothing -> cfg.headerColor
  in
    E.div_
      ([ E.role "listbox"
       , E.ariaLabel (columnTitle col)
       , E.attr "data-column-id" (unwrapColumnId colId)
       ] <> E.styles
          [ Tuple "display" "flex"
          , Tuple "flex-direction" "column"
          , Tuple "flex-shrink" "0"
          , Tuple "width" (if isCollapsed then "48px" else show cfg.columnWidth)
          , Tuple "background-color" (Color.toHex cfg.backgroundColor)
          , Tuple "border-radius" (Geometry.toLegacyCss cfg.borderRadius)
          , Tuple "border" ("1px solid " <> Color.toHex cfg.borderColor)
          ])
      [ -- Header
        renderColumnHeader cfg col cardCnt isOverWIP headerBgColor
      , -- Cards (if not collapsed)
        if isCollapsed
          then E.empty
          else renderColumnContent cfg props state col cards
      ]

-- | Render column header
renderColumnHeader :: KanbanConfig -> KanbanColumn -> Int -> Boolean -> Color.RGB -> E.Element KanbanMsg
renderColumnHeader cfg col cardCnt isOverWIP headerBgColor =
  let
    colId = columnIdOf col
    isCollapsed = columnCollapsed col
    countLabel = columnCardCountLabel cardCnt col
    
    countBadgeColor = if isOverWIP
      then Color.rgb 239 68 68  -- red-500
      else cfg.mutedTextColor
  in
    E.div_
      (E.styles
          [ Tuple "display" "flex"
          , Tuple "align-items" "center"
          , Tuple "justify-content" "space-between"
          , Tuple "padding" (show cfg.cardPadding)
          , Tuple "background-color" (Color.toHex headerBgColor)
          , Tuple "border-radius" (Geometry.toLegacyCss cfg.borderRadius <> " " <> Geometry.toLegacyCss cfg.borderRadius <> " 0 0")
          ])
      [ if isCollapsed
          then 
            -- Vertical text when collapsed
            E.span_
              (E.styles
                  [ Tuple "writing-mode" "vertical-lr"
                  , Tuple "transform" "rotate(180deg)"
                  , Tuple "font-weight" "600"
                  , Tuple "font-size" "14px"
                  , Tuple "color" (Color.toHex cfg.textColor)
                  ])
              [ E.text (columnTitle col) ]
          else
            E.div_
              (E.styles
                  [ Tuple "display" "flex"
                  , Tuple "align-items" "center"
                  , Tuple "gap" "8px"
                  , Tuple "flex" "1"
                  ])
              [ E.h3_
                  (E.styles
                      [ Tuple "font-weight" "600"
                      , Tuple "font-size" "14px"
                      , Tuple "color" (Color.toHex cfg.textColor)
                      , Tuple "margin" "0"
                      ])
                  [ E.text (columnTitle col) ]
              , E.span_
                  (E.styles
                      [ Tuple "font-size" "12px"
                      , Tuple "padding" "2px 8px"
                      , Tuple "border-radius" "9999px"
                      , Tuple "background-color" (Color.toHex countBadgeColor)
                      , Tuple "color" "white"
                      ])
                  [ E.text countLabel ]
              ]
      , -- Collapse/Expand button
        if columnCollapsible col
          then
            let
              -- Use custom callback or default to ToggleColumnCollapse
              toggleMsg = case cfg.onColumnCollapse of
                Just f -> f colId
                Nothing -> ToggleColumnCollapse colId
              
              -- Arrow direction and label depend on collapsed state
              arrowIcon = if isCollapsed then ">" else "<"
              ariaLabelText = if isCollapsed then "Expand column" else "Collapse column"
            in
              E.button_
                ([ E.type_ "button"
                 , E.ariaLabel ariaLabelText
                 , E.onClick toggleMsg
                 ] <> E.styles
                    [ Tuple "padding" "4px"
                    , Tuple "border" "none"
                    , Tuple "background" "transparent"
                    , Tuple "cursor" "pointer"
                    , Tuple "border-radius" "4px"
                    , Tuple "margin-top" (if isCollapsed then "8px" else "0")
                    ])
                [ E.text arrowIcon ]
          else E.empty
      ]

-- | Render column content (cards area)
-- |
-- | The props, state, and col parameters are used for:
-- | - props: allows future extension for dynamic prop handling
-- | - state: provides access to selection/drag state for card highlighting and drop handling
-- | - col: provides column context for accessibility, data attributes, and drop target
-- |
-- | Drop behavior:
-- | - onDragOver: allows dropping (prevents default)
-- | - onDrop: moves dragged card to this column at the end
-- | - onClick: deselects any selected card (clicking empty area)
renderColumnContent :: KanbanConfig -> Array KanbanProp -> KanbanState -> KanbanColumn -> Array KanbanCard -> E.Element KanbanMsg
renderColumnContent cfg _props state col cards =
  let
    colId = columnIdOf col
    colTitle = columnTitle col
    cardCnt = cardCountInColumn colId state
    
    -- When a card is dropped here, move it to this column at the end
    -- The runtime will read the dragged card from state
    dropHandler = case getDraggedCard state of
      Nothing -> EndDrag  -- No card being dragged, just end
      Just draggedCardId -> MoveCard draggedCardId colId cardCnt
    
    -- Visual feedback: highlight when dragging over
    dropTargetStyle = if isDragging state
      then [ Tuple "outline" ("2px dashed " <> Color.toHex cfg.selectedColor) ]
      else []
  in
    E.div_
      ([ E.role "group"
       , E.ariaLabel ("Cards in " <> colTitle)
       , E.attr "data-content-for" (unwrapColumnId colId)
       -- Click handler: clicking empty area deselects
       , E.onClick DeselectCard
       -- Drop target handlers
       , E.onDragOver EndDrag  -- Allow drop (EndDrag is a no-op message for dragover)
       , E.onDrop dropHandler
       ] <> E.styles
          ([ Tuple "flex" "1"
           , Tuple "padding" (show cfg.cardPadding)
           , Tuple "display" "flex"
           , Tuple "flex-direction" "column"
           , Tuple "gap" "8px"
           , Tuple "overflow-y" "auto"
           , Tuple "min-height" (show cfg.columnMinHeight)
           ] <> dropTargetStyle))
      (map (renderCardWithSelection cfg state) cards <> [renderAddCardButtonWithConfig cfg colId])

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // add card button
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render add card button (props-based API)
-- |
-- | Uses config callback if provided, otherwise emits AddCard message
renderAddCardButton :: Array KanbanProp -> ColumnId -> E.Element KanbanMsg
renderAddCardButton props colId =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
  in
    renderAddCardButtonWithConfig cfg colId

-- | Render add card button (config-based API)
-- |
-- | Internal version that takes config directly for use within render functions.
-- | Uses config callback if provided, otherwise emits AddCard message.
renderAddCardButtonWithConfig :: KanbanConfig -> ColumnId -> E.Element KanbanMsg
renderAddCardButtonWithConfig cfg colId =
  let
    -- Use custom callback or default to AddCard
    addMsg = case cfg.onAddCard of
      Just f -> f colId
      Nothing -> AddCard colId
  in
    E.button_
      ([ E.type_ "button"
       , E.onClick addMsg
       ] <> E.styles
          [ Tuple "width" "100%"
          , Tuple "padding" "8px"
          , Tuple "text-align" "left"
          , Tuple "font-size" "14px"
          , Tuple "color" (Color.toHex cfg.mutedTextColor)
          , Tuple "background" "transparent"
          , Tuple "border" "none"
          , Tuple "cursor" "pointer"
          , Tuple "border-radius" (Geometry.toLegacyCss cfg.cardRadius)
          , Tuple "display" "flex"
          , Tuple "align-items" "center"
          , Tuple "gap" "8px"
          -- Hover color as data for runtime state management
          , Tuple "--hydrogen-hover-bg" (Color.toHex cfg.hoverColor)
          ])
      [ E.text "+ Add card" ]
