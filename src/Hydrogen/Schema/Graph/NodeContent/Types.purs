-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // graph // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NodeContent Types — Core ADTs for node content model.
-- |
-- | ## Overview
-- |
-- | Defines the fundamental types for node content:
-- | - ContentSlot: Named regions within a node
-- | - ContentTemplate: Pre-built content configurations
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Graph.NodeContent.Types
  ( -- * Content Slots
    ContentSlot(..)
  , isLeadingSlot
  , isMainSlot
  , isTrailingSlot
  , slotPriority
  
  -- * Content Templates
  , ContentTemplate(..)
  , isTextTemplate
  , isCardTemplate
  , isCustomTemplate
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content slots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named regions within a node where content appears
data ContentSlot
  = SlotLeading      -- ^ Before main content (expand icon, checkbox)
  | SlotIcon         -- ^ Node icon area
  | SlotMain         -- ^ Primary content area
  | SlotSubtitle     -- ^ Secondary text below main
  | SlotTrailing     -- ^ After main content (badges, status)
  | SlotActions      -- ^ Action buttons (show on hover)
  | SlotBelow        -- ^ Content below the main row
  | SlotOverlay      -- ^ Overlaid on top of node
  | SlotBackground   -- ^ Behind all content

derive instance eqContentSlot :: Eq ContentSlot
derive instance ordContentSlot :: Ord ContentSlot

instance showContentSlot :: Show ContentSlot where
  show SlotLeading = "leading"
  show SlotIcon = "icon"
  show SlotMain = "main"
  show SlotSubtitle = "subtitle"
  show SlotTrailing = "trailing"
  show SlotActions = "actions"
  show SlotBelow = "below"
  show SlotOverlay = "overlay"
  show SlotBackground = "background"

isLeadingSlot :: ContentSlot -> Boolean
isLeadingSlot SlotLeading = true
isLeadingSlot _ = false

isMainSlot :: ContentSlot -> Boolean
isMainSlot SlotMain = true
isMainSlot _ = false

isTrailingSlot :: ContentSlot -> Boolean
isTrailingSlot SlotTrailing = true
isTrailingSlot _ = false

-- | Slot render priority (lower = rendered first)
slotPriority :: ContentSlot -> Int
slotPriority SlotBackground = 0
slotPriority SlotLeading = 1
slotPriority SlotIcon = 2
slotPriority SlotMain = 3
slotPriority SlotSubtitle = 4
slotPriority SlotTrailing = 5
slotPriority SlotActions = 6
slotPriority SlotBelow = 7
slotPriority SlotOverlay = 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // content templates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pre-built content configurations
data ContentTemplate
  = TemplateTextOnly         -- ^ Simple text label
  | TemplateIconText         -- ^ Icon + text (file explorer)
  | TemplateTitleSubtitle    -- ^ Title + subtitle
  | TemplateCard             -- ^ Multi-field card
  | TemplateAvatar           -- ^ Avatar + name
  | TemplateMetric           -- ^ Value + label
  | TemplateProgress         -- ^ Progress indicator
  | TemplateThumbnail        -- ^ Image thumbnail
  | TemplateCustom           -- ^ Custom Element

derive instance eqContentTemplate :: Eq ContentTemplate

instance showContentTemplate :: Show ContentTemplate where
  show TemplateTextOnly = "text-only"
  show TemplateIconText = "icon-text"
  show TemplateTitleSubtitle = "title-subtitle"
  show TemplateCard = "card"
  show TemplateAvatar = "avatar"
  show TemplateMetric = "metric"
  show TemplateProgress = "progress"
  show TemplateThumbnail = "thumbnail"
  show TemplateCustom = "custom"

isTextTemplate :: ContentTemplate -> Boolean
isTextTemplate TemplateTextOnly = true
isTextTemplate TemplateTitleSubtitle = true
isTextTemplate _ = false

isCardTemplate :: ContentTemplate -> Boolean
isCardTemplate TemplateCard = true
isCardTemplate _ = false

isCustomTemplate :: ContentTemplate -> Boolean
isCustomTemplate TemplateCustom = true
isCustomTemplate _ = false
