-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // kanban // render // swimlane
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Swimlane Render — Pure Element rendering for Kanban swimlanes.
-- |
-- | ## Design Philosophy
-- |
-- | Swimlanes are horizontal groupings that organize cards across columns.
-- | Common use cases include grouping by priority, assignee, or epic.
-- |
-- | All styling uses Schema atoms — no CSS strings, no Tailwind classes.

module Hydrogen.Element.Compound.Kanban.Render.Swimlane
  ( renderSwimlane
  ) where

import Prelude
  ( show
  , (<>)
  )

import Data.Array (foldl)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Compound.Kanban.Types
  ( KanbanMsg
  )
import Hydrogen.Element.Compound.Kanban.State
  ( Swimlane
  , swimlaneName
  , swimlaneCollapsed
  )
import Hydrogen.Element.Compound.Kanban.Render.Config
  ( KanbanProp
  , defaultConfig
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // swimlane render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render swimlane
renderSwimlane :: Array KanbanProp -> Swimlane -> Array (E.Element KanbanMsg) -> E.Element KanbanMsg
renderSwimlane props sl children =
  let
    cfg = foldl (\c f -> f c) defaultConfig props
    isCollapsed = swimlaneCollapsed sl
  in
    E.div_
      (E.styles
          [ Tuple "border-bottom" ("1px solid " <> Color.toHex cfg.borderColor)
          , Tuple "padding-bottom" (show cfg.padding)
          , Tuple "margin-bottom" (show cfg.padding)
          ])
      [ -- Swimlane header
        E.div_
          (E.styles
              [ Tuple "display" "flex"
              , Tuple "align-items" "center"
              , Tuple "gap" "8px"
              , Tuple "padding" "8px 0"
              , Tuple "margin-bottom" "8px"
              ])
          [ E.div_
              (E.styles
                  [ Tuple "width" "4px"
                  , Tuple "height" "16px"
                  , Tuple "border-radius" "2px"
                  , Tuple "background-color" (Color.toHex cfg.selectedColor)
                  ])
              []
          , E.h3_
              (E.styles
                  [ Tuple "font-weight" "600"
                  , Tuple "font-size" "14px"
                  , Tuple "color" (Color.toHex cfg.textColor)
                  , Tuple "margin" "0"
                  ])
              [ E.text (swimlaneName sl) ]
          ]
      , -- Content
        if isCollapsed
          then E.empty
          else
            E.div_
              (E.styles
                  [ Tuple "display" "flex"
                  , Tuple "gap" (show cfg.gap)
                  ])
              children
      ]
