-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // graph // node-content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph NodeContent — Content model for nodes in hierarchical visualizations.
-- |
-- | ## Design Philosophy
-- |
-- | Nodes can contain arbitrary content. This module defines the content model:
-- | - **Slots**: Named regions where content appears (leading, main, trailing, etc.)
-- | - **Templates**: Pre-built content configurations (text, card, avatar, etc.)
-- | - **Renderers**: Functions that produce Element from node data
-- |
-- | ## Slot Architecture
-- |
-- | ```
-- | ┌─────────────────────────────────────────────────────────┐
-- | │ [Leading]  [Icon]  [Main Content]  [Trailing] [Actions]│
-- | │                    [Subtitle]                          │
-- | │                    [Below Content / Details]           │
-- | └─────────────────────────────────────────────────────────┘
-- | ```
-- |
-- | ## Content Types
-- |
-- | - TextOnly: Simple label
-- | - IconText: Icon + label (file explorer)
-- | - TitleSubtitle: Two-line text
-- | - Card: Multi-field card (org chart)
-- | - Avatar: Image with name (people)
-- | - Metric: Value with label (dashboards)
-- | - Custom: Arbitrary Element
-- |
-- | ## Module Structure
-- |
-- | This is a leader module that re-exports from submodules:
-- | - Types: ContentSlot, ContentTemplate
-- | - SlotContent: SlotContent, TextContent
-- | - ContentTypes: BadgeContent, ActionContent, ProgressContent
-- | - CardAndShape: CardField, NodeShape
-- | - Config: NodeStateVisual, ContentConfig, SlotLayout
-- |
-- | ## Dependencies
-- |
-- | - Submodules only

module Hydrogen.Schema.Graph.NodeContent
  ( module Types
  , module SlotContent
  , module ContentTypes
  , module CardAndShape
  , module Config
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Graph.NodeContent.Types
  ( ContentSlot(SlotLeading, SlotIcon, SlotMain, SlotSubtitle, SlotTrailing, SlotActions, SlotBelow, SlotOverlay, SlotBackground)
  , ContentTemplate(TemplateTextOnly, TemplateIconText, TemplateTitleSubtitle, TemplateCard, TemplateAvatar, TemplateMetric, TemplateProgress, TemplateThumbnail, TemplateCustom)
  , isCardTemplate
  , isCustomTemplate
  , isLeadingSlot
  , isMainSlot
  , isTextTemplate
  , isTrailingSlot
  , slotPriority
  ) as Types

import Hydrogen.Schema.Graph.NodeContent.SlotContent
  ( SlotContent(ContentText, ContentIcon, ContentBadge, ContentAction, ContentProgress, ContentImage, ContentCustom)
  , TextContent
  , actionContent
  , badgeContent
  , customContent
  , editableText
  , iconContent
  , progressContent
  , richText
  , simpleText
  , textContent
  ) as SlotContent

import Hydrogen.Schema.Graph.NodeContent.ContentTypes
  ( ActionContent
  , BadgeContent
  , ProgressContent
  , badgeCount
  , badgeDot
  , badgeStatus
  , buttonAction
  , iconAction
  , menuAction
  , progressBar
  , progressCircle
  , progressSparkline
  ) as ContentTypes

import Hydrogen.Schema.Graph.NodeContent.CardAndShape
  ( CardField(FieldTitle, FieldSubtitle, FieldMetadata, FieldImage, FieldAvatar, FieldBadge, FieldProgress, FieldDivider, FieldSpacer)
  , NodeShape(ShapeRectangle, ShapeRoundedRect, ShapePill, ShapeCircle, ShapeEllipse, ShapeDiamond, ShapeHexagon, ShapeOctagon, ShapeParallelogram, ShapeCylinder, ShapeDocument, ShapeCloud, ShapeCustomPath)
  , avatarField
  , imageField
  , isCircle
  , isDiamond
  , isRectangle
  , metadataField
  , subtitleField
  , titleField
  ) as CardAndShape

import Hydrogen.Schema.Graph.NodeContent.Config
  ( ContentConfig
  , NodeStateVisual
  , SlotLayout
  , avatarContent
  , cardContent
  , contentConfig
  , customContentConfig
  , defaultStateVisual
  , gridSlots
  , horizontalSlots
  , iconTextContent
  , metricContent
  , nodeStateVisual
  , slotLayout
  , textOnlyContent
  , verticalSlots
  , withDisabledStyle
  , withFocusStyle
  , withHoverStyle
  , withSelectedStyle
  ) as Config
