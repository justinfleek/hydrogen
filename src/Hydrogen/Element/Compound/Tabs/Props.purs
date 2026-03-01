-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // element // tabs // props
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tabs Props — Property modifiers for tabbed interface components.
-- |
-- | This module contains all default props and property modifier functions:
-- | - Container props (activeTab, ariaLabel, reducedMotion)
-- | - List props (backgroundColor, borderRadius, padding, gap)
-- | - Tab props (all color, dimension, typography, and behavior settings)
-- | - Panel props (value, active, padding, labelledBy)

module Hydrogen.Element.Compound.Tabs.Props
  ( -- * Container Props
    defaultProps
  , activeTab
  , tabsAriaLabel
  , tabsReducedMotion
  , extraAttributes
  
  -- * List Props
  , defaultListProps
  , listBackgroundColor
  , listBorderRadius
  , listPadding
  , listGap
  , listExtraAttributes
  
  -- * Tab Props
  , defaultTabProps
  , tabValue
  , isTabActive
  , isTabDisabled
  , tabBackgroundColor
  , tabActiveBackgroundColor
  , tabHoverBackgroundColor
  , tabTextColor
  , tabActiveTextColor
  , tabHoverTextColor
  , tabFocusRingColor
  , tabBorderRadius
  , tabFocusRingWidth
  , tabHeight
  , tabPaddingX
  , tabPaddingY
  , tabFontSize
  , tabFontWeight
  , tabControlsPanel
  , tabReducedMotion
  , onSelect
  , onTabKeyDown
  , tabExtraAttributes
  
  -- * Panel Props
  , defaultPanelProps
  , panelValue
  , isPanelActive
  , panelPadding
  , panelLabelledBy
  , panelExtraAttributes
  ) where

import Prelude
  ( (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Tabs.Types
  ( TabsProps
  , TabsProp
  , ListProps
  , ListProp
  , TabProps
  , TabProp
  , PanelProps
  , PanelProp
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // container props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default container properties
defaultProps :: forall msg. TabsProps msg
defaultProps =
  { activeTab: ""
  , ariaLabel: Nothing
  , reducedMotion: false
  , extraAttributes: []
  }

-- | Set active tab value
activeTab :: forall msg. String -> TabsProp msg
activeTab v props = props { activeTab = v }

-- | Set ARIA label for the tabs container
tabsAriaLabel :: forall msg. String -> TabsProp msg
tabsAriaLabel label props = props { ariaLabel = Just label }

-- | Enable reduced motion (disables transitions)
tabsReducedMotion :: forall msg. Boolean -> TabsProp msg
tabsReducedMotion r props = props { reducedMotion = r }

-- | Add extra attributes
extraAttributes :: forall msg. Array (E.Attribute msg) -> TabsProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // list props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default list properties
defaultListProps :: forall msg. ListProps msg
defaultListProps =
  { backgroundColor: Nothing
  , borderRadius: Nothing
  , padding: Nothing
  , gap: Nothing
  , extraAttributes: []
  }

-- | Set list background color (Color.RGB atom)
listBackgroundColor :: forall msg. Color.RGB -> ListProp msg
listBackgroundColor c props = props { backgroundColor = Just c }

-- | Set list border radius (Geometry.Corners atom)
listBorderRadius :: forall msg. Geometry.Corners -> ListProp msg
listBorderRadius r props = props { borderRadius = Just r }

-- | Set list padding (Device.Pixel atom)
listPadding :: forall msg. Device.Pixel -> ListProp msg
listPadding p props = props { padding = Just p }

-- | Set gap between tabs (Device.Pixel atom)
listGap :: forall msg. Device.Pixel -> ListProp msg
listGap g props = props { gap = Just g }

-- | Add extra attributes to list
listExtraAttributes :: forall msg. Array (E.Attribute msg) -> ListProp msg
listExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // tab props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default tab properties
defaultTabProps :: forall msg. TabProps msg
defaultTabProps =
  { value: ""
  , active: false
  , disabled: false
  , backgroundColor: Nothing
  , activeBackgroundColor: Nothing
  , hoverBackgroundColor: Nothing
  , textColor: Nothing
  , activeTextColor: Nothing
  , hoverTextColor: Nothing
  , focusRingColor: Nothing
  , borderRadius: Nothing
  , focusRingWidth: Nothing
  , height: Nothing
  , paddingX: Nothing
  , paddingY: Nothing
  , fontSize: Nothing
  , fontWeight: Nothing
  , controlsPanel: Nothing
  , reducedMotion: false
  , onSelect: Nothing
  , onKeyDown: Nothing
  , extraAttributes: []
  }

-- | Set tab value (identifier)
tabValue :: forall msg. String -> TabProp msg
tabValue v props = props { value = v }

-- | Set tab active state
isTabActive :: forall msg. Boolean -> TabProp msg
isTabActive a props = props { active = a }

-- | Set tab disabled state
isTabDisabled :: forall msg. Boolean -> TabProp msg
isTabDisabled d props = props { disabled = d }

-- | Set inactive background color (Color.RGB atom)
tabBackgroundColor :: forall msg. Color.RGB -> TabProp msg
tabBackgroundColor c props = props { backgroundColor = Just c }

-- | Set active background color (Color.RGB atom)
tabActiveBackgroundColor :: forall msg. Color.RGB -> TabProp msg
tabActiveBackgroundColor c props = props { activeBackgroundColor = Just c }

-- | Set hover background color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
tabHoverBackgroundColor :: forall msg. Color.RGB -> TabProp msg
tabHoverBackgroundColor c props = props { hoverBackgroundColor = Just c }

-- | Set inactive text color (Color.RGB atom)
tabTextColor :: forall msg. Color.RGB -> TabProp msg
tabTextColor c props = props { textColor = Just c }

-- | Set active text color (Color.RGB atom)
tabActiveTextColor :: forall msg. Color.RGB -> TabProp msg
tabActiveTextColor c props = props { activeTextColor = Just c }

-- | Set hover text color (Color.RGB atom)
-- | Used via data attribute — runtime interprets hover state
tabHoverTextColor :: forall msg. Color.RGB -> TabProp msg
tabHoverTextColor c props = props { hoverTextColor = Just c }

-- | Set focus ring color (Color.RGB atom)
-- | Applied as box-shadow on focus
tabFocusRingColor :: forall msg. Color.RGB -> TabProp msg
tabFocusRingColor c props = props { focusRingColor = Just c }

-- | Set border radius (Geometry.Corners atom)
tabBorderRadius :: forall msg. Geometry.Corners -> TabProp msg
tabBorderRadius r props = props { borderRadius = Just r }

-- | Set focus ring width (Device.Pixel atom)
tabFocusRingWidth :: forall msg. Device.Pixel -> TabProp msg
tabFocusRingWidth w props = props { focusRingWidth = Just w }

-- | Set tab height (Device.Pixel atom)
tabHeight :: forall msg. Device.Pixel -> TabProp msg
tabHeight h props = props { height = Just h }

-- | Set horizontal padding (Device.Pixel atom)
tabPaddingX :: forall msg. Device.Pixel -> TabProp msg
tabPaddingX p props = props { paddingX = Just p }

-- | Set vertical padding (Device.Pixel atom)
tabPaddingY :: forall msg. Device.Pixel -> TabProp msg
tabPaddingY p props = props { paddingY = Just p }

-- | Set font size (FontSize atom)
tabFontSize :: forall msg. FontSize.FontSize -> TabProp msg
tabFontSize s props = props { fontSize = Just s }

-- | Set font weight (FontWeight atom)
tabFontWeight :: forall msg. FontWeight.FontWeight -> TabProp msg
tabFontWeight w props = props { fontWeight = Just w }

-- | Set the panel ID this tab controls (for aria-controls)
tabControlsPanel :: forall msg. String -> TabProp msg
tabControlsPanel panelId props = props { controlsPanel = Just panelId }

-- | Enable reduced motion (disables transitions)
tabReducedMotion :: forall msg. Boolean -> TabProp msg
tabReducedMotion r props = props { reducedMotion = r }

-- | Set selection handler
onSelect :: forall msg. msg -> TabProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set keyboard handler for arrow key navigation
-- | Runtime passes key name ("ArrowLeft", "ArrowRight", "Home", "End")
onTabKeyDown :: forall msg. (String -> msg) -> TabProp msg
onTabKeyDown handler props = props { onKeyDown = Just handler }

-- | Add extra attributes to tab
tabExtraAttributes :: forall msg. Array (E.Attribute msg) -> TabProp msg
tabExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // panel props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default panel properties
defaultPanelProps :: forall msg. PanelProps msg
defaultPanelProps =
  { value: ""
  , active: false
  , padding: Nothing
  , labelledBy: Nothing
  , extraAttributes: []
  }

-- | Set panel value (identifier)
panelValue :: forall msg. String -> PanelProp msg
panelValue v props = props { value = v }

-- | Set panel active state
isPanelActive :: forall msg. Boolean -> PanelProp msg
isPanelActive a props = props { active = a }

-- | Set panel padding (Device.Pixel atom)
panelPadding :: forall msg. Device.Pixel -> PanelProp msg
panelPadding p props = props { padding = Just p }

-- | Set the tab ID that labels this panel (for aria-labelledby)
panelLabelledBy :: forall msg. String -> PanelProp msg
panelLabelledBy tabId props = props { labelledBy = Just tabId }

-- | Add extra attributes to panel
panelExtraAttributes :: forall msg. Array (E.Attribute msg) -> PanelProp msg
panelExtraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }
