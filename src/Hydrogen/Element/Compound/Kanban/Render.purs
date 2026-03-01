-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // kanban // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Render — Pure Element rendering for Kanban boards.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides pure render functions that produce Element values.
-- | All styling uses Schema atoms — no CSS strings, no Tailwind classes.
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- |
-- | - `Config` — Configuration type, defaults, and property setters
-- | - `Board` — Board and column rendering
-- | - `Card` — Card rendering and parts (labels, footer, priority)
-- | - `Swimlane` — Swimlane rendering
-- |
-- | ## Schema Atoms Used
-- |
-- | | Property         | Pillar    | Type                | Purpose            |
-- | |------------------|-----------|---------------------|-------------------|
-- | | backgroundColor  | Color     | Color.RGB           | Board/card bg      |
-- | | borderColor      | Color     | Color.RGB           | Card borders       |
-- | | headerColor      | Color     | Color.RGB           | Column headers     |
-- | | textColor        | Color     | Color.RGB           | Text color         |
-- | | priorityColor    | Color     | Color.RGB           | Priority indicator |
-- | | borderRadius     | Geometry  | Geometry.Radius     | Corner rounding    |
-- | | padding          | Dimension | Device.Pixel        | Internal padding   |
-- | | gap              | Dimension | Device.Pixel        | Spacing            |
-- | | columnWidth      | Dimension | Device.Pixel        | Column width       |
-- | | elevation        | Elevation | BoxShadow           | Card shadows       |

module Hydrogen.Element.Compound.Kanban.Render
  ( -- * Re-exports
    module Config
  , module Board
  , module Card
  , module Swimlane
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // re-exports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Kanban.Render.Config
  ( KanbanConfig
  , KanbanProp
  , defaultConfig
  , backgroundColor
  , borderColor
  , cardBackgroundColor
  , headerColor
  , textColor
  , mutedTextColor
  , selectedColor
  , hoverColor
  , borderRadius
  , cardRadius
  , padding
  , cardPadding
  , gap
  , columnWidth
  , columnMinHeight
  , priorityLowColor
  , priorityMediumColor
  , priorityHighColor
  , priorityUrgentColor
  , onCardClick
  , onCardExpand
  , onColumnCollapse
  , onAddCard
  ) as Config

import Hydrogen.Element.Compound.Kanban.Render.Board
  ( renderBoard
  , renderColumn
  , renderAddCardButton
  ) as Board

import Hydrogen.Element.Compound.Kanban.Render.Card
  ( renderCard
  , renderDragPreview
  ) as Card

import Hydrogen.Element.Compound.Kanban.Render.Swimlane
  ( renderSwimlane
  ) as Swimlane
