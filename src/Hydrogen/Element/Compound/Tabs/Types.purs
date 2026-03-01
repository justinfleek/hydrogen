-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // tabs // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tabs Types — Type definitions for tabbed interface components.
-- |
-- | This module contains all type aliases for the Tabs compound component:
-- | - TabsProps / TabsProp — Container properties
-- | - ListProps / ListProp — Tab list properties
-- | - TabProps / TabProp — Individual tab properties
-- | - PanelProps / PanelProp — Tab panel properties

module Hydrogen.Element.Compound.Tabs.Types
  ( -- * Container Types
    TabsProps
  , TabsProp
  
  -- * List Types
  , ListProps
  , ListProp
  
  -- * Tab Types
  , TabProps
  , TabProp
  
  -- * Panel Types
  , PanelProps
  , PanelProp
  ) where

import Data.Maybe (Maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tabs container properties
type TabsProps msg =
  { -- State
    activeTab :: String
  
  -- Accessibility
  , ariaLabel :: Maybe String
  , reducedMotion :: Boolean
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for TabsProps
type TabsProp msg = TabsProps msg -> TabsProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // list types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tab list properties
type ListProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for ListProps
type ListProp msg = ListProps msg -> ListProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tab types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual tab properties
type TabProps msg =
  { -- State
    value :: String
  , active :: Boolean
  , disabled :: Boolean
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , activeBackgroundColor :: Maybe Color.RGB
  , hoverBackgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , activeTextColor :: Maybe Color.RGB
  , hoverTextColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  , focusRingWidth :: Maybe Device.Pixel
  
  -- Dimension atoms
  , height :: Maybe Device.Pixel
  , paddingX :: Maybe Device.Pixel
  , paddingY :: Maybe Device.Pixel
  
  -- Typography atoms
  , fontSize :: Maybe FontSize.FontSize
  , fontWeight :: Maybe FontWeight.FontWeight
  
  -- Accessibility
  , controlsPanel :: Maybe String  -- ID of the panel this tab controls
  , reducedMotion :: Boolean
  
  -- Behavior
  , onSelect :: Maybe msg
  , onKeyDown :: Maybe (String -> msg)  -- For arrow key navigation
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for TabProps
type TabProp msg = TabProps msg -> TabProps msg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // panel types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tab panel properties
type PanelProps msg =
  { -- State
    value :: String
  , active :: Boolean
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  
  -- Accessibility
  , labelledBy :: Maybe String  -- ID of the tab that labels this panel
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier for PanelProps
type PanelProp msg = PanelProps msg -> PanelProps msg
