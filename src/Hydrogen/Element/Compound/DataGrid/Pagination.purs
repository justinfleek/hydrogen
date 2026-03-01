-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // data-grid // pagination
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DataGrid Pagination — Pagination controls for the data grid.
-- |
-- | This module renders pagination controls for the DataGrid component.
-- | Supports both built-in pagination (state managed internally) and
-- | external pagination (state managed by parent component).

module Hydrogen.Element.Compound.DataGrid.Pagination
  ( renderPagination
  ) where

import Prelude
  ( (>=)
  , (<=)
  , ($)
  , (<>)
  , show
  )

import Data.Maybe (maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Compound.DataGrid.Types
  ( GridProps
  , PaginationConfig(NoPagination, BuiltIn, External)
  )
import Hydrogen.Element.Compound.DataGrid.Processing as Processing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // pagination
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render pagination controls.
-- |
-- | Supports both built-in and external pagination modes.
renderPagination :: forall msg. GridProps msg -> Int -> E.Element msg
renderPagination props totalFiltered =
  case props.pagination of
    NoPagination -> E.empty
    
    BuiltIn { pageSize } ->
      let
        totalPages = Processing.calculateTotalPages totalFiltered pageSize
        currentPg = 1 -- Would need state management for this
      in
        renderPaginationControls props currentPg totalPages totalFiltered pageSize
    
    External { pageSize, currentPage, totalRows } ->
      let
        totalPages = Processing.calculateTotalPages totalRows pageSize
      in
        renderPaginationControls props currentPage totalPages totalRows pageSize

-- | Render pagination controls UI.
renderPaginationControls :: forall msg. GridProps msg -> Int -> Int -> Int -> Int -> E.Element msg
renderPaginationControls props currentPg totalPages total _ps =
  E.div_
    ( [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "space-between"
      , E.style "padding" "0.75rem 1rem"
      , E.style "border-top" "1px solid"
      ]
      <> maybe [] (\c -> [E.style "border-color" (Color.toLegacyCss c)]) props.borderColor
    )
    [ -- Row count info
      E.div_
        [ E.style "font-size" "0.875rem"
        , E.style "opacity" "0.7"
        ]
        [ E.text $ "Total: " <> show total <> " rows" ]
    , -- Page navigation
      E.div_
        [ E.style "display" "flex"
        , E.style "align-items" "center"
        , E.style "gap" "0.5rem"
        ]
        [ -- Previous page
          E.button_
            [ E.type_ "button"
            , E.disabled (currentPg <= 1)
            , E.ariaLabel "Previous page"
            , E.style "padding" "0.25rem 0.5rem"
            , E.style "border" "1px solid"
            , E.style "border-radius" "0.25rem"
            , E.style "background" "transparent"
            , E.style "cursor" (if currentPg <= 1 then "not-allowed" else "pointer")
            , E.style "opacity" (if currentPg <= 1 then "0.5" else "1")
            ]
            [ E.text "<" ]
        , -- Page indicator
          E.span_
            [ E.style "font-size" "0.875rem" ]
            [ E.text $ "Page " <> show currentPg <> " of " <> show totalPages ]
        , -- Next page
          E.button_
            [ E.type_ "button"
            , E.disabled (currentPg >= totalPages)
            , E.ariaLabel "Next page"
            , E.style "padding" "0.25rem 0.5rem"
            , E.style "border" "1px solid"
            , E.style "border-radius" "0.25rem"
            , E.style "background" "transparent"
            , E.style "cursor" (if currentPg >= totalPages then "not-allowed" else "pointer")
            , E.style "opacity" (if currentPg >= totalPages then "0.5" else "1")
            ]
            [ E.text ">" ]
        ]
    ]
