-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // kanban // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Kanban Config — Configuration type and property setters for Kanban boards.
-- |
-- | ## Design Philosophy
-- |
-- | Configuration uses Schema atoms exclusively — no CSS strings, no Tailwind.
-- | All color, dimension, and geometry values are bounded primitives from
-- | the Schema pillars.
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

module Hydrogen.Element.Compound.Kanban.Render.Config
  ( -- * Config Type
    KanbanConfig
  , KanbanProp
  , defaultConfig
  
  -- * Color Setters
  , backgroundColor
  , borderColor
  , cardBackgroundColor
  , headerColor
  , textColor
  , mutedTextColor
  , selectedColor
  , hoverColor
  
  -- * Priority Color Setters
  , priorityLowColor
  , priorityMediumColor
  , priorityHighColor
  , priorityUrgentColor
  
  -- * Geometry Setters
  , borderRadius
  , cardRadius
  
  -- * Dimension Setters
  , padding
  , cardPadding
  , gap
  , columnWidth
  , columnMinHeight
  
  -- * Event Handler Setters
  , onCardClick
  , onCardExpand
  , onColumnCollapse
  , onAddCard
  ) where

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device

import Hydrogen.Element.Compound.Kanban.Types
  ( CardId
  , ColumnId
  , KanbanMsg
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kanban board configuration (all Schema atoms)
type KanbanConfig =
  { backgroundColor :: Color.RGB
  , borderColor :: Color.RGB
  , cardBackgroundColor :: Color.RGB
  , headerColor :: Color.RGB
  , textColor :: Color.RGB
  , mutedTextColor :: Color.RGB
  , selectedColor :: Color.RGB
  , hoverColor :: Color.RGB
  , borderRadius :: Geometry.Radius
  , cardRadius :: Geometry.Radius
  , padding :: Device.Pixel
  , cardPadding :: Device.Pixel
  , gap :: Device.Pixel
  , columnWidth :: Device.Pixel
  , columnMinHeight :: Device.Pixel
  , priorityLowColor :: Color.RGB
  , priorityMediumColor :: Color.RGB
  , priorityHighColor :: Color.RGB
  , priorityUrgentColor :: Color.RGB
  , onCardClick :: Maybe (CardId -> KanbanMsg)
  , onCardExpand :: Maybe (CardId -> Boolean -> KanbanMsg)
  , onColumnCollapse :: Maybe (ColumnId -> KanbanMsg)
  , onAddCard :: Maybe (ColumnId -> KanbanMsg)
  }

-- | Config property modifier
type KanbanProp = KanbanConfig -> KanbanConfig

-- | Default configuration
defaultConfig :: KanbanConfig
defaultConfig =
  { backgroundColor: Color.rgb 248 250 252        -- slate-50
  , borderColor: Color.rgb 226 232 240            -- slate-200
  , cardBackgroundColor: Color.rgb 255 255 255    -- white
  , headerColor: Color.rgb 241 245 249            -- slate-100
  , textColor: Color.rgb 15 23 42                 -- slate-900
  , mutedTextColor: Color.rgb 100 116 139         -- slate-500
  , selectedColor: Color.rgb 219 234 254          -- blue-100
  , hoverColor: Color.rgb 241 245 249             -- slate-100
  , borderRadius: Geometry.px 8.0                 -- 8px
  , cardRadius: Geometry.px 8.0                   -- 8px
  , padding: Device.px 16.0                       -- 16px
  , cardPadding: Device.px 12.0                   -- 12px
  , gap: Device.px 16.0                           -- 16px
  , columnWidth: Device.px 288.0                  -- 288px (18rem)
  , columnMinHeight: Device.px 200.0              -- 200px
  , priorityLowColor: Color.rgb 34 197 94         -- green-500
  , priorityMediumColor: Color.rgb 234 179 8      -- yellow-500
  , priorityHighColor: Color.rgb 249 115 22       -- orange-500
  , priorityUrgentColor: Color.rgb 239 68 68      -- red-500
  , onCardClick: Nothing
  , onCardExpand: Nothing
  , onColumnCollapse: Nothing
  , onAddCard: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color setters
-- ═════════════════════════════════════════════════════════════════════════════

backgroundColor :: Color.RGB -> KanbanProp
backgroundColor c cfg = cfg { backgroundColor = c }

borderColor :: Color.RGB -> KanbanProp
borderColor c cfg = cfg { borderColor = c }

cardBackgroundColor :: Color.RGB -> KanbanProp
cardBackgroundColor c cfg = cfg { cardBackgroundColor = c }

headerColor :: Color.RGB -> KanbanProp
headerColor c cfg = cfg { headerColor = c }

textColor :: Color.RGB -> KanbanProp
textColor c cfg = cfg { textColor = c }

mutedTextColor :: Color.RGB -> KanbanProp
mutedTextColor c cfg = cfg { mutedTextColor = c }

selectedColor :: Color.RGB -> KanbanProp
selectedColor c cfg = cfg { selectedColor = c }

hoverColor :: Color.RGB -> KanbanProp
hoverColor c cfg = cfg { hoverColor = c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // priority color setters
-- ═════════════════════════════════════════════════════════════════════════════

priorityLowColor :: Color.RGB -> KanbanProp
priorityLowColor c cfg = cfg { priorityLowColor = c }

priorityMediumColor :: Color.RGB -> KanbanProp
priorityMediumColor c cfg = cfg { priorityMediumColor = c }

priorityHighColor :: Color.RGB -> KanbanProp
priorityHighColor c cfg = cfg { priorityHighColor = c }

priorityUrgentColor :: Color.RGB -> KanbanProp
priorityUrgentColor c cfg = cfg { priorityUrgentColor = c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // geometry setters
-- ═════════════════════════════════════════════════════════════════════════════

borderRadius :: Geometry.Radius -> KanbanProp
borderRadius r cfg = cfg { borderRadius = r }

cardRadius :: Geometry.Radius -> KanbanProp
cardRadius r cfg = cfg { cardRadius = r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // dimension setters
-- ═════════════════════════════════════════════════════════════════════════════

padding :: Device.Pixel -> KanbanProp
padding p cfg = cfg { padding = p }

cardPadding :: Device.Pixel -> KanbanProp
cardPadding p cfg = cfg { cardPadding = p }

gap :: Device.Pixel -> KanbanProp
gap g cfg = cfg { gap = g }

columnWidth :: Device.Pixel -> KanbanProp
columnWidth w cfg = cfg { columnWidth = w }

columnMinHeight :: Device.Pixel -> KanbanProp
columnMinHeight h cfg = cfg { columnMinHeight = h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // event handler setters
-- ═════════════════════════════════════════════════════════════════════════════

onCardClick :: (CardId -> KanbanMsg) -> KanbanProp
onCardClick f cfg = cfg { onCardClick = Just f }

onCardExpand :: (CardId -> Boolean -> KanbanMsg) -> KanbanProp
onCardExpand f cfg = cfg { onCardExpand = Just f }

onColumnCollapse :: (ColumnId -> KanbanMsg) -> KanbanProp
onColumnCollapse f cfg = cfg { onColumnCollapse = Just f }

onAddCard :: (ColumnId -> KanbanMsg) -> KanbanProp
onAddCard f cfg = cfg { onAddCard = Just f }
