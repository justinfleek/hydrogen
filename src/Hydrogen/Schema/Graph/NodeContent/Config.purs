-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // graph // config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Config — Node state visuals, content config, and slot layout.
-- |
-- | ## Overview
-- |
-- | Defines compound configuration types:
-- | - NodeStateVisual: Styling for different node states
-- | - ContentConfig: Complete content configuration for nodes
-- | - SlotLayout: Layout for slots within a node
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe
-- | - Types (ContentSlot, ContentTemplate)
-- | - SlotContent (SlotContent)
-- | - CardAndShape (CardField, NodeShape)

module Hydrogen.Schema.Graph.NodeContent.Config
  ( -- * Node State Visual
    NodeStateVisual
  , nodeStateVisual
  , defaultStateVisual
  , withHoverStyle
  , withSelectedStyle
  , withFocusStyle
  , withDisabledStyle
  
  -- * Content Config (Compound)
  , ContentConfig
  , contentConfig
  , textOnlyContent
  , iconTextContent
  , cardContent
  , avatarContent
  , metricContent
  , customContentConfig
  
  -- * Slot Layout
  , SlotLayout
  , slotLayout
  , horizontalSlots
  , verticalSlots
  , gridSlots
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Graph.NodeContent.Types
  ( ContentSlot
  , ContentTemplate
    ( TemplateTextOnly
    , TemplateIconText
    , TemplateCard
    , TemplateAvatar
    , TemplateMetric
    , TemplateCustom
    )
  )

import Hydrogen.Schema.Graph.NodeContent.SlotContent
  ( SlotContent
  )

import Hydrogen.Schema.Graph.NodeContent.CardAndShape
  ( CardField
  , NodeShape
    ( ShapeRectangle
    , ShapeRoundedRect
    )
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // node state visual
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual styling for different node states
type NodeStateVisual =
  { defaultBg :: Maybe String
  , defaultBorder :: Maybe String
  , hoverBg :: Maybe String
  , hoverBorder :: Maybe String
  , selectedBg :: Maybe String
  , selectedBorder :: Maybe String
  , focusBorder :: Maybe String
  , focusRing :: Maybe String
  , disabledOpacity :: Number
  , pressedScale :: Number
  }

-- | Create node state visual
nodeStateVisual :: NodeStateVisual
nodeStateVisual =
  { defaultBg: Nothing
  , defaultBorder: Nothing
  , hoverBg: Nothing
  , hoverBorder: Nothing
  , selectedBg: Nothing
  , selectedBorder: Nothing
  , focusBorder: Nothing
  , focusRing: Nothing
  , disabledOpacity: 0.5
  , pressedScale: 0.98
  }

-- | Default state visual
defaultStateVisual :: NodeStateVisual
defaultStateVisual = nodeStateVisual

-- | Set hover styles
withHoverStyle :: String -> String -> NodeStateVisual -> NodeStateVisual
withHoverStyle bg border v = v { hoverBg = Just bg, hoverBorder = Just border }

-- | Set selected styles
withSelectedStyle :: String -> String -> NodeStateVisual -> NodeStateVisual
withSelectedStyle bg border v = v { selectedBg = Just bg, selectedBorder = Just border }

-- | Set focus styles
withFocusStyle :: String -> String -> NodeStateVisual -> NodeStateVisual
withFocusStyle border ring v = v { focusBorder = Just border, focusRing = Just ring }

-- | Set disabled opacity
withDisabledStyle :: Number -> NodeStateVisual -> NodeStateVisual
withDisabledStyle opacity v = v { disabledOpacity = opacity }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // content config compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete content configuration for nodes
type ContentConfig =
  { template :: ContentTemplate
  , shape :: NodeShape
  , slots :: Array { slot :: ContentSlot, content :: SlotContent }
  , fields :: Array CardField        -- ^ For card template
  , stateVisual :: NodeStateVisual
  , padding :: Number
  , minWidth :: Maybe Number
  , maxWidth :: Maybe Number
  , aspectRatio :: Maybe Number
  }

-- | Create content config
contentConfig :: ContentTemplate -> NodeShape -> ContentConfig
contentConfig template shape =
  { template
  , shape
  , slots: []
  , fields: []
  , stateVisual: defaultStateVisual
  , padding: 8.0
  , minWidth: Nothing
  , maxWidth: Nothing
  , aspectRatio: Nothing
  }

-- | Text-only node content
textOnlyContent :: ContentConfig
textOnlyContent = contentConfig TemplateTextOnly ShapeRectangle

-- | Icon + text content (file explorer style)
iconTextContent :: ContentConfig
iconTextContent = contentConfig TemplateIconText ShapeRectangle

-- | Card content (org chart style)
cardContent :: ContentConfig
cardContent = (contentConfig TemplateCard ShapeRoundedRect)
  { padding = 16.0
  , minWidth = Just 200.0
  }

-- | Avatar + name content (people)
avatarContent :: ContentConfig
avatarContent = (contentConfig TemplateAvatar ShapeRoundedRect)
  { padding = 12.0 }

-- | Metric content (dashboards)
metricContent :: ContentConfig
metricContent = contentConfig TemplateMetric ShapeRoundedRect

-- | Custom Element content
customContentConfig :: ContentConfig
customContentConfig = contentConfig TemplateCustom ShapeRectangle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // slot layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout for slots within a node
type SlotLayout =
  { direction :: String          -- ^ "horizontal" | "vertical" | "grid"
  , gap :: Number
  , alignItems :: String         -- ^ "start" | "center" | "end" | "stretch"
  , justifyContent :: String     -- ^ "start" | "center" | "end" | "space-between"
  , wrap :: Boolean
  , gridColumns :: Int
  }

-- | Create slot layout
slotLayout :: String -> Number -> SlotLayout
slotLayout direction gap =
  { direction
  , gap
  , alignItems: "center"
  , justifyContent: "start"
  , wrap: false
  , gridColumns: 2
  }

-- | Horizontal slot layout
horizontalSlots :: SlotLayout
horizontalSlots = slotLayout "horizontal" 8.0

-- | Vertical slot layout
verticalSlots :: SlotLayout
verticalSlots = slotLayout "vertical" 4.0

-- | Grid slot layout
gridSlots :: Int -> SlotLayout
gridSlots cols = (slotLayout "grid" 8.0) { gridColumns = cols }
